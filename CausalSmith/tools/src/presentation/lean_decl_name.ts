import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";

/** Declaration command header, including repeated attributes and modifiers. */
const DECL_HEAD =
  /^[ \t]*(?:(?:@\[[^\]]*\])\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial|scoped|local)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|constant)\b/gmu;

/** Leaf of a qualified Lean name, splitting only on dots outside `«quoted components»`. */
export function leanNameLeaf(name: string): string {
  let quoted = false;
  let lastDot = -1;
  for (let i = 0; i < name.length; i += 1) {
    if (name[i] === "«") quoted = true;
    else if (name[i] === "»") quoted = false;
    else if (name[i] === "." && !quoted) lastDot = i;
  }
  return name.slice(lastDot + 1);
}

/** Read one possibly-qualified name, allowing whitespace and dots inside quoted components. */
function nameAfterHeader(source: string, masked: string, offset: number): string | null {
  let i = offset;
  while (i < masked.length && /\s/u.test(masked[i])) i += 1;
  const start = i;
  let quoted = false;
  for (; i < masked.length; i += 1) {
    const ch = masked[i];
    if (ch === "«") quoted = true;
    else if (ch === "»") quoted = false;
    else if (!quoted && (/[\s:({\[]/u.test(ch) || source.startsWith(":=", i))) break;
  }
  const name = source.slice(start, i);
  if (name.length === 0 || quoted || name.endsWith(".")) return null;
  return name;
}

const TYPE_TOKEN_NAMES: Record<string, string> = {
  "×": "Prod", "⊕": "Sum", "→": "Forall", "ℕ": "Nat", "ℤ": "Int", "ℚ": "Rat", "ℝ": "Real", "ℂ": "Complex",
};
const TYPE_STOP_WORDS = new Set(["fun", "let", "in", "Type", "Sort", "Prop", "where", "with", "by", "at", "of"]);

/** The name Lean gives an anonymous `instance <binders> : C a b …`: `inst` followed by the leaf of
 *  every constant in the result type, in order, capitalized and deduplicated (binder names are
 *  variables, not constants; a few symbols stand for their constant). An anonymous instance a
 *  component names (`instTopologicalSpaceMechanism`) is otherwise invisible to every index built
 *  from source text. Best effort: a mismatch leaves the name unresolved, as before. */
export function autoInstanceName(masked: string, offset: number): string | null {
  let i = offset;
  const binders = new Set<string>();
  // Skip binder groups, collecting the names they bind.
  for (;;) {
    while (i < masked.length && /\s/u.test(masked[i])) i += 1;
    const open = masked[i];
    const close = open === "{" ? "}" : open === "(" ? ")" : open === "[" ? "]" : open === "⦃" ? "⦄" : null;
    if (!close) break;
    let depth = 0;
    let j = i;
    for (; j < masked.length; j += 1) {
      if (masked[j] === open) depth += 1;
      else if (masked[j] === close && --depth === 0) break;
    }
    const inner = masked.slice(i + 1, j);
    const colon = inner.indexOf(":");
    if (colon > 0) for (const b of inner.slice(0, colon).split(/\s+/u)) if (b) binders.add(b);
    i = j + 1;
  }
  if (masked[i] !== ":" || masked[i + 1] === "=") return null;
  const rest = masked.slice(i + 1);
  const end = rest.search(/:=|\bwhere\b|\n\S/u);
  const type = end < 0 ? rest : rest.slice(0, end);
  const parts: string[] = [];
  for (const raw of typeConstants(type, binders)) {
    const leaf = leanNameLeaf(raw).replace(/'/gu, "");
    // A single letter (Latin or Greek, optionally with a digit) is an auto-bound variable, not a constant.
    if (!leaf || /^[\p{L}]\p{N}?$/u.test(leaf)) continue;
    const cap = leaf[0].toUpperCase() + leaf.slice(1);
    if (!parts.includes(cap)) parts.push(cap);
  }
  return parts.length > 0 ? `inst${parts.join("")}` : null;
}

/** Constants of a type expression in Lean's naming order: an infix operator's constant before its
 *  operands (`Fin n × Bool` is `Prod (Fin n) Bool`), prefix applications in source order. */
function typeConstants(expr: string, binders: ReadonlySet<string>): string[] {
  let e = expr.trim();
  while (e.startsWith("(") && closingParen(e, 0) === e.length - 1) e = e.slice(1, -1).trim();
  for (const op of ["→", "×", "⊕"]) {
    let depth = 0;
    for (let i = 0; i < e.length; i += 1) {
      const ch = e[i];
      if (ch === "(" || ch === "[" || ch === "{") depth += 1;
      else if (ch === ")" || ch === "]" || ch === "}") depth -= 1;
      else if (ch === op && depth === 0) {
        return [TYPE_TOKEN_NAMES[op], ...typeConstants(e.slice(0, i), binders), ...typeConstants(e.slice(i + 1), binders)];
      }
    }
  }
  // Prefix applications: tokens in source order, recursing into each parenthesized argument so
  // an operator nested there still leads its own operands.
  const out: string[] = [];
  const tokens = (seg: string) => {
    for (const tok of seg.match(/[\p{L}_][\p{L}\p{N}_.']*|[ℕℤℚℝℂ]/gu) ?? []) {
      const mapped = TYPE_TOKEN_NAMES[tok];
      if (mapped) { out.push(mapped); continue; }
      if (binders.has(tok) || TYPE_STOP_WORDS.has(tok)) continue;
      out.push(tok);
    }
  };
  let i = 0;
  while (i < e.length) {
    const open = e.indexOf("(", i);
    if (open < 0) { tokens(e.slice(i)); break; }
    const close = closingParen(e, open);
    if (close < 0) { tokens(e.slice(i)); break; }
    tokens(e.slice(i, open));
    out.push(...typeConstants(e.slice(open + 1, close), binders));
    i = close + 1;
  }
  return out;
}

function closingParen(text: string, open: number): number {
  let depth = 0;
  for (let i = open; i < text.length; i += 1) {
    if (text[i] === "(") depth += 1;
    else if (text[i] === ")" && --depth === 0) return i;
  }
  return -1;
}

/** Whether the first source declaration explicitly has the private modifier. */
export function isPrivateDeclarationSource(source: string): boolean {
  DECL_HEAD.lastIndex = 0;
  const header = DECL_HEAD.exec(maskLeanCommandQuotations(source))?.[0];
  return header !== undefined && /\bprivate\b/u.test(header.replace(/@\[[^\]]*\]/gu, ""));
}

/**
 * Leaf name of the first declaration inside a cached source slice,
 * skipping block comments. `null` when the slice declares nothing recognisable.
 */
export function firstDeclaredLeaf(source: string): string | null {
  const masked = maskLeanCommandQuotations(source);
  DECL_HEAD.lastIndex = 0;
  const match = DECL_HEAD.exec(masked);
  if (!match) return null;
  const name = nameAfterHeader(source, masked, match.index + match[0].length);
  return name === null ? null : leanNameLeaf(name);
}


/** Mask syntax quotations as well as comments/strings so quoted commands are never declarations.
 * Preserve positions and newlines for source pointers. */
export function maskLeanCommandQuotations(source: string): string {
  const masked = maskLeanCommentsAndStrings(source);
  // Use code-unit indexing, matching regex offsets and source slices.
  const out = masked.split("");
  let quotedName = false;
  for (let i = 0; i < masked.length; i++) {
    if (masked[i] === "«") quotedName = true;
    else if (masked[i] === "»") quotedName = false;
    if (quotedName || masked[i] !== "`" || masked[i + 1] !== "(") continue;
    let depth = 0;
    let j = i + 1;
    for (; j < masked.length; j++) {
      if (masked[j] === "(") depth++;
      if (masked[j] === ")" && --depth === 0) { j++; break; }
    }
    for (let k = i; k < j; k++) if (out[k] !== "\n" && out[k] !== "\r") out[k] = " ";
    i = j - 1;
  }
  return out.join("");
}

/** Declaration names as written, retaining relative qualification and quoted/Unicode components. */
export function leanSourceDeclarations(source: string): { name: string; line: number; kind: string }[] {
  const masked = maskLeanCommandQuotations(source);
  const seenAuto = new Map<string, number>(); // Lean suffixes a repeated auto name: bare, then _1, _2, …
  return [...masked.matchAll(new RegExp(DECL_HEAD.source, DECL_HEAD.flags))].flatMap((m) => {
    let name = nameAfterHeader(source, masked, m.index + m[0].length);
    if (name === null && m[1] === "instance") {
      const auto = autoInstanceName(masked, m.index + m[0].length);
      if (auto) {
        const n = seenAuto.get(auto) ?? 0;
        seenAuto.set(auto, n + 1);
        name = n === 0 ? auto : `${auto}_${n}`;
      }
    }
    // Attributes/modifiers may span lines. Point at the declaration keyword, otherwise
    // extraction can mistake the following theorem line for a different declaration.
    const keywordOffset = m.index + m[0].length - m[1].length;
    return name ? [{ name, line: source.slice(0, keywordOffset).split("\n").length, kind: m[1] }] : [];
  });
}

/** Public qualified snippet target whose declaration header matches its canonical label.
 * Bare component aliases must never become additional canonical declarations. */
export function isCanonicalSourceDeclaration(name: string, source: string): boolean {
  return name.includes(".") && !isPrivateDeclarationSource(source) &&
    firstDeclaredLeaf(source) === leanNameLeaf(name);
}
