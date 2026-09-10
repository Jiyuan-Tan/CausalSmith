import { maskLeanCommentsAndStrings } from "../graph/extractor.js";

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
  return [...masked.matchAll(new RegExp(DECL_HEAD.source, DECL_HEAD.flags))].flatMap((m) => {
    const name = nameAfterHeader(source, masked, m.index + m[0].length);
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
