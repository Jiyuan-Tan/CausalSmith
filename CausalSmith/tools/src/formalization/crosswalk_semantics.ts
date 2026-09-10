// F2.5 tex↔Lean crosswalk — semantics layer: the symbol → realization-cluster
// map and the hidden/semantic statement-def surface, built on crosswalk_parse.ts.
// See crosswalk.ts for the module-level design note.

import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { readFile, readdir } from "node:fs/promises";
import path from "node:path";
import { isPaperTmpPath } from "../paths.js";
import { statementHash } from "../graph/hash.js";
import { extractLeanCommentText, maskLeanCommentsAndStrings } from "../graph/extractor.js";
import {
  classifyComment,
  DECL_HEADER_SCAN_RE,
  VARIABLE_HEADER_RE,
  deriveObjId,
  parseAllDecls,
  type FullDecl,
  statementText,
  splitStatement,
  leanIdentifiers,
  isPropValued,
  CONSTANT_EXISTENTIAL_RE,
} from "./crosswalk_parse.js";

// ---------------------------------------------------------------------------
// Symbol → realization-cluster map (the SETUP/ENVIRONMENT faithfulness unit)
// ---------------------------------------------------------------------------
//
// A core SYMBOL's space (e.g. `propensity : (0,1)`) is faithfully realized by the
// CONJUNCTION of several Lean decls — a carrier-type structure field
// (`propensity : 𝒳 → ℝ`) PLUS the predicate(s) that pin its range
// (`WellFormedLaw`, `Positivity`). Grading the field-decl ALONE false-flags the
// carrier idiom as drift. So the scaffolder annotates each realizing decl with a
// `@realizes <symbol>(<clause hint>), …` docstring tag, and this scanner groups
// them into a per-symbol cluster the reviewer judges as a whole. `drift` is then
// correct ONLY when a symbol's cluster constrains its space NOWHERE.

/** One Lean decl that (partly) realizes a core symbol. */
export interface SymbolClusterMember {
  decl: string;
  declKind: string;
  file: string; // relative to leanDir
  line: number; // 1-indexed
  hint?: string; // the `@realizes sym(<hint>)` clause hint, if any
  /** Stable code anchor for line-number-named carriers such as standalone `variable` commands.
   *  Docstring insertion moves their source line but must not change F4 evidence. */
  codeAnchor?: string;
}

/** A core symbol + the cluster of Lean decls that jointly realize its space. */
export interface SymbolCluster {
  symbol: string;
  space?: string;
  members: SymbolClusterMember[];
}

/** Capture a complete standalone `variable` command, including multiline binders. The masked
 * source lets us scan balanced binder delimiters without mistaking comments, strings, array
 * literals, or a tactic keyword for a new top-level command. */
function variableCommandAnchor(lines: string[], maskedLines: string[], start: number): string {
  const raw = lines.slice(start).join("\n");
  const masked = maskedLines.slice(start).join("\n");
  const head = masked.match(/^\s*variable\b/);
  let pos = head?.[0].length ?? 0;
  let end = pos;
  const pairs: Record<string, string> = { "(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄" };
  while (pos < masked.length) {
    while (/\s/.test(masked[pos] ?? "")) pos++;
    const close = pairs[masked[pos]];
    if (!close) break;
    const stack = [close];
    pos++;
    while (pos < masked.length && stack.length > 0) {
      if (masked[pos] === "«") {
        const escapedEnd = masked.indexOf("»", pos + 1);
        pos = escapedEnd < 0 ? masked.length : escapedEnd + 1;
        continue;
      }
      const nestedClose = pairs[masked[pos]];
      if (nestedClose) stack.push(nestedClose);
      else if (masked[pos] === stack.at(-1)) stack.pop();
      pos++;
    }
    end = pos;
  }
  return commentInsensitiveLeanCode(raw.slice(0, end));
}

/** Canonicalize Lean code while ignoring comments/docstrings and formatting-only whitespace.
 * Exact string/char literals are digested first because their internal whitespace is semantic. */
export function commentInsensitiveLeanCode(source: string): string {
  return protectLeanLexemes(source).trim().replace(/\s+/g, " ");
}

/** Replace lexemes whose internal whitespace/delimiters are semantic before surrounding source
 * whitespace is canonicalized. */
function leanStringEnd(code: string, quote: number): number {
  let rawPrefix = quote - 1;
  while (rawPrefix >= 0 && code[rawPrefix] === "#") rawPrefix--;
  const rawHashes = quote - 1 - rawPrefix;
  const previousCodePoint = [...code.slice(0, rawPrefix)].at(-1);
  const rawAtClearBoundary = previousCodePoint === undefined || /[\s([{,;:=⟨⦃]/u.test(previousCodePoint);
  if (rawPrefix >= 0 && code[rawPrefix] === "r" && (rawHashes > 0 || rawAtClearBoundary)) {
    const close = `"${"#".repeat(rawHashes)}`;
    const rawEnd = code.indexOf(close, quote + 1);
    return rawEnd < 0 ? -1 : rawEnd + close.length - 1;
  }
  // `token-ending-in-r"..."` is lexically ambiguous without the active syntax table: it may be
  // an ordinary string after a custom atom (`😀r"..."`) or a zero-hash raw string after an
  // operator. Bind the rest of the file exactly rather than risk truncating either literal.
  if (rawPrefix >= 0 && code[rawPrefix] === "r" && rawHashes === 0) return code.length - 1;
  const interpolated = quote >= 2 && code.slice(quote - 2, quote) === "s!";
  if (!interpolated) {
    for (let j = quote + 1; j < code.length; j++) {
      if (code[j] === "\\") j++;
      else if (code[j] === '"') return j;
    }
    return -1;
  }
  let braces = 0;
  for (let j = quote + 1; j < code.length; j++) {
    if (code[j] === "\\") { j++; continue; }
    if (braces > 0 && code[j] === "-" && code[j + 1] === "-") {
      j += 2;
      while (j < code.length && code[j] !== "\n") j++;
      continue;
    }
    if (braces > 0 && code[j] === "/" && code[j + 1] === "-") {
      let commentDepth = 1;
      j += 2;
      while (j < code.length && commentDepth > 0) {
        if (code[j] === "/" && code[j + 1] === "-") { commentDepth++; j += 2; continue; }
        if (code[j] === "-" && code[j + 1] === "/") { commentDepth--; j += 2; continue; }
        j++;
      }
      j--;
      continue;
    }
    if (braces > 0 && code[j] === "«") {
      const escapedEnd = code.indexOf("»", j + 1);
      if (escapedEnd >= 0) j = escapedEnd;
      continue;
    }
    if (braces > 0 && code[j] === "'") {
      if (code[j + 1] === "\\" && code[j + 3] === "'") { j += 3; continue; }
      if (code[j + 1] !== "\\" && code[j + 1] !== undefined && code[j + 2] === "'") { j += 2; continue; }
    }
    if (code[j] === '"') {
      if (braces === 0) return j;
      const nestedEnd = leanStringEnd(code, j);
      if (nestedEnd >= 0) j = nestedEnd;
      continue;
    }
    if (code[j] === "{") {
      if (braces === 0 && code[j + 1] === "{") { j++; continue; }
      braces++;
    } else if (code[j] === "}") {
      if (braces === 0 && code[j + 1] === "}") { j++; continue; }
      if (braces > 0) braces--;
    }
  }
  return -1;
}

function protectLeanLexemes(code: string): string {
  let protectedCode = "";
  for (let i = 0; i < code.length; i++) {
    if (code[i] === "-" && code[i + 1] === "-") {
      protectedCode += " ";
      i += 2;
      while (i < code.length && code[i] !== "\n") i++;
      if (i < code.length) protectedCode += "\n";
      continue;
    }
    if (code[i] === "/" && code[i + 1] === "-") {
      protectedCode += " ";
      let depth = 1;
      i += 2;
      while (i < code.length && depth > 0) {
        if (code[i] === "/" && code[i + 1] === "-") { depth++; i += 2; continue; }
        if (code[i] === "-" && code[i + 1] === "/") { depth--; i += 2; continue; }
        if (code[i] === "\n") protectedCode += "\n";
        i++;
      }
      i--;
      continue;
    }
    let endLiteral = -1;
    if (code[i] === "«") {
      const escapedEnd = code.indexOf("»", i + 1);
      if (escapedEnd >= 0) endLiteral = escapedEnd;
    } else if (code[i] === '"') {
      endLiteral = leanStringEnd(code, i);
    } else if (code[i] === "'") {
      if (code[i + 1] === "\\" && code[i + 3] === "'") endLiteral = i + 3;
      else if (code[i + 1] !== "\\" && code[i + 1] !== undefined && code[i + 2] === "'") endLiteral = i + 2;
    }
    if (endLiteral < 0) {
      protectedCode += code[i];
      continue;
    }
    const literal = code.slice(i, endLiteral + 1);
    protectedCode += `__lit_${createHash("sha1").update(literal).digest("hex")}__`;
    i = endLiteral;
  }
  return protectedCode;
}

/** Preserve Lean's potentially meaningful layout while excluding documentation/comments. Comment
 * stripping preserves newlines; dropping blank lines and right-padding makes added doc blocks and
 * changed trailing comments invisible without collapsing indentation of actual code. */
export function commentInsensitiveLeanLayout(source: string): string {
  return protectLeanLexemes(source)
    .split(/\r?\n/)
    .filter((line) => line.trim() !== "")
    .join("\n");
}

/** Parse `@realizes a(hint with spaces), b, c(hint2)` out of a docstring block.
 *  Splits the list on TOP-LEVEL commas (so a hint may itself contain commas).
 *
 *  `knownNames` (optional) lets the caller pass the canonical core-symbol names so
 *  a name that the heuristic split CANNOT reconstruct is matched literally first:
 *   - a name containing a top-level comma (`O_1, ..., O_n`) would be shredded by the
 *     comma-split, and
 *   - a name that itself ends in parens (`Y(a)`) would be truncated to `Y` by the
 *     `(…)`-is-hint rule (`Y(a)(hint)` ⇒ symbol `Y`).
 *  When a tag's payload begins with such a known name (followed by end-of-tag or an
 *  opening `(` that introduces the hint), it is emitted whole and the comma/paren
 *  heuristics are skipped for that tag. */
function parseRealizesTagsRaw(
  commentAbove: string,
  knownNames: string[] = [],
): { symbol: string; hint?: string }[] {
  const out: { symbol: string; hint?: string }[] = [];
  // Only names the heuristic split can't reconstruct need the literal-prefix path;
  // longest-first so `O_1, ..., O_n` wins over a hypothetical `O_1` prefix.
  const literalNames = knownNames
    .filter((n) => n.includes(",") || /\)\s*$/.test(n.trim()))
    .map((n) => n.trim())
    .sort((a, b) => b.length - a.length);
  // Each tag is introduced by the `@realizes` keyword; SEVERAL tags may share one
  // line, `;`-separated (`@realizes A(h1); @realizes B(h2)`). Split on the keyword so
  // a same-line second/third tag is not swallowed by a rest-of-line capture (which
  // silently dropped every tag but the first). A tag payload never spans a newline.
  for (const seg of commentAbove.split(/@realizes\s+/g).slice(1)) {
    const rest = seg
      .split("\n")[0]
      .replace(/-\/\s*$/, "") // drop a trailing block-comment close
      .replace(/;\s*$/, "") // drop the `;` separating it from the next tag
      .trim();
    // A payload written inside math delimiters: the delimited group IS the symbol and whatever
    // follows is the hint. Decided before the paren heuristics, which would otherwise read the
    // closing delimiter as the start of a hint.
    const delimited = rest.match(/^(?:\\\((.*?)\\\)|\$(.*?)\$|\\\[(.*?)\\\])\s*(?:\((.*)\))?\s*$/s);
    if (delimited) {
      const symbol = canonicalRealizedSymbol((delimited[1] ?? delimited[2] ?? delimited[3] ?? "").trim());
      if (symbol) out.push({ symbol, hint: delimited[4]?.trim() || undefined });
      continue;
    }
    const literal = literalNames.find(
      (n) => rest === n || rest.startsWith(n + "(") || rest.startsWith(n + " ("),
    );
    if (literal) {
      const tail = rest.slice(literal.length).trim();
      const hm = tail.match(/^\((.*)\)\s*$/);
      out.push({ symbol: literal, hint: hm ? hm[1].trim() : undefined });
      continue;
    }
    const items: string[] = [];
    let parenDepth = 0;
    let braceDepth = 0;
    let bracketDepth = 0;
    let cur = "";
    for (let i = 0; i < rest.length; i++) {
      const ch = rest[i];
      // Escaped TeX braces delimit literal notation (e.g. `S_{\\{0,1\\}}`), but their
      // commas must still stay within the symbol rather than split this tag list.
      if (ch === "\\" && (rest[i + 1] === "{" || rest[i + 1] === "}")) {
        cur += ch + rest[++i];
        if (rest[i] === "{") braceDepth++;
        else braceDepth = Math.max(0, braceDepth - 1);
        continue;
      }
      if (ch === "(") parenDepth++;
      else if (ch === ")") parenDepth = Math.max(0, parenDepth - 1);
      else if (ch === "{") braceDepth++;
      else if (ch === "}") braceDepth = Math.max(0, braceDepth - 1);
      else if (ch === "[") bracketDepth++;
      else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
      if (ch === "," && parenDepth === 0 && braceDepth === 0 && bracketDepth === 0) {
        if (cur.trim()) items.push(cur.trim());
        cur = "";
      } else cur += ch;
    }
    if (cur.trim()) items.push(cur.trim());
    for (const it of items) {
      // A symbol may have TeX-index braces and application arguments before its optional hint:
      // `kappa_{r,a}(P)(coordinate...)`.  The final top-level parenthesized group is the hint;
      // preceding groups remain part of the clickable symbol.  A single bare variable argument
      // (`R^b_{m,L}(t)`) is notation rather than a prose hint.
      const groups: { open: number; close: number }[] = [];
      let depth = 0;
      let open = -1;
      let braces = 0;
      for (let i = 0; i < it.length; i++) {
        const ch = it[i];
        if (ch === "\\" && (it[i + 1] === "{" || it[i + 1] === "}")) {
          if (it[++i] === "{") braces++;
          else braces = Math.max(0, braces - 1);
          continue;
        }
        if (ch === "{") braces++;
        else if (ch === "}") braces = Math.max(0, braces - 1);
        else if (braces === 0 && ch === "(") {
          if (depth === 0) open = i;
          depth++;
        } else if (braces === 0 && ch === ")" && depth > 0 && --depth === 0) {
          groups.push({ open, close: i });
        }
      }
      // A tag hint is human prose and is not guaranteed to have balanced mathematical
      // delimiters.  Common examples include interval notation `(0,1]`, and long hints may be
      // continued onto the next comment line even though one `@realizes` payload is line-local.
      // In either case the general balanced scan above sees the symbol's application group but
      // never closes the following hint group.  Preserve the complete applied symbol and treat
      // the remaining text as its (possibly truncated) hint instead of folding the hint into the
      // symbol name; otherwise P2 emits `sym:pi_i^1(p)` while P4 indexes a different dead target.
      if (groups.length >= 1) {
        const first = groups[0];
        const afterApplication = it.slice(first.close + 1).trimStart();
        if (afterApplication.startsWith("(")) {
          const rawHint = afterApplication.slice(1).trim().replace(/\)\s*$/, "").trim();
          out.push({
            symbol: it.slice(0, first.close + 1).trim(),
            hint: rawHint || undefined,
          });
          continue;
        }
      }
      const last = groups.at(-1);
      const suffixOnly = last && last.close === it.trimEnd().length - 1;
      const candidate = suffixOnly ? it.slice(last.open + 1, last.close).trim() : "";
      const bareArgument = /^[A-Za-z][A-Za-z0-9_]*(?:\s*,\s*[A-Za-z][A-Za-z0-9_]*)*$/.test(candidate);
      const mathHead = last ? it.slice(0, last.open) : "";
      const looksLikeIndexedMath = /[_^{}]/.test(mathHead);
      if (last && suffixOnly && (groups.length > 1 || !bareArgument || !looksLikeIndexedMath)) {
        out.push({ symbol: it.slice(0, last.open).trim(), hint: candidate });
      } else out.push({ symbol: it.trim() });
    }
  }
  return out.filter((t) => t.symbol);
}

/** A `@realizes` symbol as the paper names it: bare TeX, never wrapped in math delimiters. Tags
 *  written as `@realizes \(Y(a)\)(hint)` produced ids like `sym:\(Y(a)\)`, which break every
 *  delimiter scan downstream (a link nested in a display closes the display early). */
export function canonicalRealizedSymbol(symbol: string): string {
  let s = symbol.trim();
  for (;;) {
    const m = s.match(/^(?:\\\((.*)\\\)|\$(.*)\$|\\\[(.*)\\\])$/s);
    if (!m) return s;
    s = (m[1] ?? m[2] ?? m[3] ?? "").trim();
  }
}

export function parseRealizesTags(
  commentAbove: string,
  knownNames: string[] = [],
): { symbol: string; hint?: string }[] {
  return parseRealizesTagsRaw(commentAbove, knownNames)
    .map((t) => ({ ...t, symbol: canonicalRealizedSymbol(t.symbol) }))
    .filter((t) => t.symbol);
}

/**
 * Discover EVERY core symbol that carries at least one `@realizes <sym>` tag anywhere in the Lean
 * tree (distinct, in first-seen order). The presentation surfaces all of them — the F-phase
 * `buildSymbolClusters` filters to a fixed `core.symbols` list, but the website wants whatever was
 * actually tagged in the code, so this drives the symbol list for `buildSymbolClusters`.
 */
export async function discoverRealizedSymbols(leanDir: string): Promise<string[]> {
  const seen = new Set<string>();
  const order: string[] = [];
  if (!existsSync(leanDir)) return order;
  const files = (await readdir(leanDir, { recursive: true }))
    .map(String)
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f))
    .sort();
  for (const rel of files) {
    const source = await readFile(path.join(leanDir, rel), "utf8");
    const lines = extractLeanCommentText(source).split(/\r?\n/);
    for (const ln of lines) {
      if (!ln.includes("@realizes")) continue;
      for (const t of parseRealizesTags(ln)) {
        if (!seen.has(t.symbol)) {
          seen.add(t.symbol);
          order.push(t.symbol);
        }
      }
    }
  }
  return order;
}

/**
 * Canonical comparison key for a paper-side TeX symbol and an ASCII `@realizes`
 * tag. This is intentionally notation-level normalization, not fuzzy declaration
 * matching: it only erases TeX spelling differences such as
 * `E_{\mathcal P_N}` versus `E_Pcal_N`.
 */
/** ONE greek-letter command list for both comparison keys. The two keys used to
 * carry different partial lists (one had `\delta`/`\omega`, the other
 * `\alpha`/`\epsilon`/…), so whether a symbol's TeX and ASCII spellings matched
 * depended on WHICH letter it used — `\sigma` (in neither list) could never
 * bind its `@realizes sigma^2` tag and escalated as a tagging gap. Case stays
 * significant (`\Sigma` → `Sigma` ≠ `sigma`). */
const GREEK_COMMAND_RE =
  /\\(?:alpha|beta|gamma|delta|epsilon|varepsilon|zeta|eta|theta|vartheta|iota|kappa|lambda|mu|nu|xi|omicron|pi|varpi|rho|varrho|sigma|varsigma|tau|upsilon|phi|varphi|chi|psi|omega|Gamma|Delta|Theta|Lambda|Xi|Pi|Sigma|Upsilon|Phi|Psi|Omega)(?![A-Za-z])/g;

export function realizedNotationKey(raw: string, opts: { preserveCase?: boolean } = {}): string {
  const key = raw
    .trim()
    .replace(/^\$|\$$/g, "")
    .replace(/^\\\(|\\\)$/g, "")
    .replace(/\\mathcal\s*(?:\{([A-Za-z])\}|([A-Za-z]))/g, (_, braced, bare) => `${braced ?? bare}cal`)
    .replace(/\\mathscr\s*(?:\{([A-Za-z])\}|([A-Za-z]))/g, (_, braced, bare) => `${braced ?? bare}scr`)
    .replace(/\\mathfrak\s*(?:\{([A-Za-z])\}|([A-Za-z]))/g, (_, braced, bare) => `${braced ?? bare}frak`)
    .replace(GREEK_COMMAND_RE, (m) => m.slice(1))
    .replace(/_\{([^{}]*)\}/g, "_$1")
    // Erase `^` in BOTH spellings: the braced rule dropped it while the bare
    // spelling kept it, so `\pi^{1}` and `\pi^1` produced DIFFERENT keys and
    // the same symbol was reported as unrealized depending on bracing.
    .replace(/\^\{([^{}]*)\}/g, "$1")
    .replace(/\^/g, "")
    .replace(/[{}\\]/g, "")
    .replace(/[\s,;:'`]/g, "");
  return opts.preserveCase ? key : key.toLowerCase();
}

/** Narrow symbol-tag key: remove only outer math wrappers and normalize harmless TeX command
 * bracing/whitespace. Case, commas, subscripts, and backslashes remain significant. */
export function canonicalSymbolTagKey(raw: string): string {
  return raw
    .trim()
    .replace(/^\$([\s\S]*)\$$/, "$1")
    .replace(/^\\\(([\s\S]*)\\\)$/, "$1")
    .replace(/\\(mathcal|mathsf|mathrm|mathbf|mathbb)\s*\{([^{}]+)\}/g, "\\$1 $2")
    .replace(GREEK_COMMAND_RE, (m) => m.slice(1))
    .replace(/\s+/g, " ")
    .trim();
}


/**
 * Build the per-symbol realization-cluster map by scanning `@realizes` docstring
 * tags across every Lean decl in `leanDir`. Returns one entry PER input symbol
 * (in order); a symbol with an EMPTY cluster has no `@realizes` tag at all and is
 * surfaced to the caller as a TAGGING GAP (not a drift — see the reviewer prompt).
 *
 * Tags are the SOLE source: fuzzy name-matching is deliberately NOT used — a core
 * symbol name (`mu_0`, `tau_P`, `pi_star`) routinely differs from its Lean decl
 * name (`mu0`, `contrast`, `optimalPolicy`), and single-letter symbols (`A`, `O`)
 * match almost every docstring, so name-matching both misses and over-matches. The
 * scaffolder (F2) is responsible for tagging each realizing decl `@realizes <sym>`.
 */
export async function buildSymbolClusters(
  leanDir: string,
  symbols: { name: string; space?: string }[],
): Promise<SymbolCluster[]> {
  const tagged: { sym: string; member: SymbolClusterMember }[] = [];
  if (existsSync(leanDir)) {
    const files = (await readdir(leanDir, { recursive: true }))
      .map(String)
      .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f))
      .sort();
    for (const rel of files) {
      const source = await readFile(path.join(leanDir, rel), "utf8");
      const lines = source.split(/\r?\n/);
      const commentLines = extractLeanCommentText(source).split(/\r?\n/);
      const masked = maskLeanCommentsAndStrings(source);
      const maskedLines = masked.split(/\r?\n/);
      const comment = classifyComment(source);
      const headers: { line: number; m: RegExpMatchArray }[] = [];
      DECL_HEADER_SCAN_RE.lastIndex = 0;
      let headerMatch: RegExpExecArray | null;
      while ((headerMatch = DECL_HEADER_SCAN_RE.exec(masked))) {
        const line = source.slice(0, headerMatch.index).split(/\r?\n/).length - 1;
        const name = headerMatch[2] ?? headerMatch[3];
        headers.push({ line, m: [headerMatch[0], headerMatch[1], name] as unknown as RegExpMatchArray });
      }
      const enclosing = (L: number): { line: number; m: RegExpMatchArray } | undefined => {
        let owner: { line: number; m: RegExpMatchArray } | undefined;
        for (const h of headers) {
          if (h.line <= L) owner = h;
          else break;
        }
        return owner;
      };
      // Attribute each `@realizes` line to a decl, discriminating on whether the
      // tag sits on a COMMENT line or a CODE line:
      //  - CODE line (`comment[L]` false) — an inline field tag like
      //    `propensity : 𝒳 → ℝ -- @realizes e_P` — belongs to the ENCLOSING decl.
      //  - COMMENT line — a docstring block immediately ABOVE a decl belongs to that
      //    FOLLOWING decl; any other comment belongs to the enclosing decl.
      for (let L = 0; L < lines.length; L++) {
        if (!commentLines[L].includes("@realizes")) continue;
        let owner: { line: number; m: RegExpMatchArray } | undefined;
        // A standalone variable command owns inline tags and immediately-following comment tags.
        // Use a stable source label rather than pretending its first binder names every symbol.
        const variableAt = (line: number): { line: number; m: RegExpMatchArray } | undefined => {
          if (line < 0 || !/^\s*variable\b/.test(maskedLines[line] ?? "")) return undefined;
          return { line, m: [lines[line], "variable", `variable@${line + 1}`] as unknown as RegExpMatchArray };
        };
        owner = variableAt(L);
        if (!owner && comment[L]) {
          let prior = L - 1;
          while (prior >= 0 && comment[prior] && lines[prior].trim() !== "") prior--;
          owner = variableAt(prior);
        }
        if (!owner && comment[L]) {
          const nextIdx = headers.findIndex((h) => h.line > L);
          if (nextIdx !== -1) {
            let allComment = true;
            // A docstring block ABOVE the next decl is a CONTIGUOUS run of comment lines. A BLANK line
            // between the tag and that decl breaks contiguity → the tag is a TRAILING comment of the
            // ENCLOSING (preceding) decl (e.g. `-- @realizes X` on the line just after a def body,
            // separated from the next def by a blank), NOT a docstring for the following decl.
            for (let k = L + 1; k < headers[nextIdx].line; k++) {
              if (!comment[k] || lines[k].trim() === "") { allComment = false; break; }
            }
            if (allComment) owner = headers[nextIdx]; // docstring above this decl
          }
        }
        // A `@realizes` trailing a standalone `variable` command anchors to THAT
        // binder (its type realizes the symbol), never the preceding closed decl.
        if (!owner && !comment[L]) {
          const vm = lines[L].replace(/--.*$/, "").match(VARIABLE_HEADER_RE);
          if (vm) owner = { line: L, m: [lines[L], "variable", vm[1]] as unknown as RegExpMatchArray };
        }
        if (!owner) owner = enclosing(L); // inline code-line tag, or a non-docstring comment
        if (!owner) continue;
        const knownNames = symbols.flatMap((s) => [s.name, canonicalSymbolTagKey(s.name)]);
        for (const t of parseRealizesTags(commentLines[L], knownNames)) {
          tagged.push({
            sym: t.symbol,
            member: {
              decl: owner.m[2],
              declKind: owner.m[1],
              file: rel,
              line: L + 1,
              hint: t.hint,
              codeAnchor: owner.m[1] === "variable"
                ? variableCommandAnchor(lines, maskedLines, owner.line)
                : undefined,
            },
          });
        }
      }
    }
  }
  // Case-SENSITIVE exact match (trim only): `pi` (policy) and `Pi` (policy class)
  // are distinct core symbols, so lower-casing would conflate their clusters.
  const norm = canonicalSymbolTagKey;
  return symbols.map((s) => ({
    symbol: s.name,
    space: s.space,
    members: tagged.filter((t) => norm(t.sym) === norm(s.name)).map((t) => t.member),
  }));
}

/** Why a hidden decl is surfaced — drives the reviewer's per-row instruction.
 *  `const-exist`: ∃-real-constant membership predicate (uniform-constant trap).
 *  `structure`: assumption-bundle structure (fields are conditions).
 *  `predicate`: a Prop-valued inline assumption/condition.
 *  `quantity`: an ℝ-valued computational quantity named in a CONCLUSION (a rate /
 *  estimand / threshold whose FORMULA defines what is proved). */
export type HiddenDefFlavor = "const-exist" | "structure" | "predicate" | "quantity";

export interface HiddenStatementDef {
  name: string;
  file: string;
  line: number;
  kind: string; // "def" | "abbrev" | "structure"
  flavor: HiddenDefFlavor;
  reachedFrom: string[]; // T-ids whose statement reaches this decl
  /** Hash of the complete meaning-bearing declaration (signature + def body /
   *  structure fields), whitespace-normalized.  F2 revise mode compares this
   *  across the producer edit to invalidate only the affected headline rows. */
  contentHash: string;
}

/** Every definition-like declaration reachable from a typed headline theorem's
 * statement, including deep computational helpers.  This is intentionally
 * broader than `HiddenStatementDef`: F2.5 should not display low-level helpers,
 * but revise-mode F2 must still invalidate a cached headline review when one of
 * those helpers changes the meaning of a predicate/structure in its statement. */
export interface StatementSemanticDef {
  name: string;
  file: string;
  line: number;
  kind: string;
  reachedFrom: string[];
  contentHash: string;
}

export async function findStatementSemanticDefs(leanDir: string): Promise<StatementSemanticDef[]> {
  const decls = await parseAllDecls(leanDir);
  const nodeByName = new Map<string, FullDecl>();
  for (const d of decls) {
    if (
      (d.kind === "def" || d.kind === "abbrev" || d.kind === "structure") &&
      d.name &&
      !nodeByName.has(d.name)
    ) {
      nodeByName.set(d.name, d);
    }
  }
  const theorems = decls.filter((d) => {
    if (d.kind !== "theorem") return false;
    const id = deriveObjId("theorem", d.name, d.commentAbove);
    return id?.startsWith("T-") || id?.startsWith("thm:");
  });
  const reachedBy = new Map<string, Set<string>>();
  const MAX_DEPTH = 32;
  for (const thm of theorems) {
    const tid = deriveObjId("theorem", thm.name, thm.commentAbove)!;
    const { hyp, concl } = splitStatement(statementText(thm.text));
    const seen = new Set<string>();
    let frontier = new Set([...leanIdentifiers(hyp), ...leanIdentifiers(concl)]);
    for (let depth = 0; depth < MAX_DEPTH && frontier.size > 0; depth++) {
      const next = new Set<string>();
      for (const id of frontier) {
        if (seen.has(id)) continue;
        seen.add(id);
        const d = nodeByName.get(id);
        if (!d) continue;
        if (!reachedBy.has(id)) reachedBy.set(id, new Set());
        reachedBy.get(id)!.add(tid);
        for (const child of leanIdentifiers(d.text)) {
          if (child !== id && !seen.has(child) && nodeByName.has(child)) next.add(child);
        }
      }
      frontier = next;
    }
  }
  const out: StatementSemanticDef[] = [];
  for (const [name, tids] of reachedBy) {
    const d = nodeByName.get(name)!;
    out.push({
      name,
      file: d.file,
      line: d.line,
      kind: d.kind,
      reachedFrom: [...tids].sort(),
      contentHash: statementHash(d.text),
    });
  }
  out.sort((a, b) => a.name.localeCompare(b.name));
  return out;
}

/**
 * Meaning-bearing decls (`def`/`abbrev`/`structure`) reachable — directly or
 * transitively — from a T-block theorem's STATEMENT that hide from BOTH the
 * obj_id-keyed crosswalk (no P-row) AND the per-hypothesis (H.1) matrix, so a
 * clause/field dropped or weakened inside them silently makes Lean certify a
 * different statement than the paper. Surfaced as `AUX-` rows for F2.5 check K.
 *
 * Scope decisions:
 *  - **Both regions are seeds.** A predicate hidden under the CONCLUSION (e.g. a
 *    converse's class membership) weakens the proved claim; a predicate hidden
 *    transitively under a HYPOTHESIS can *over-strengthen* it (Lean assumes more
 *    → proves less than the paper). Both are real, so we BFS hypothesis +
 *    conclusion and let the reviewer apply the asymmetric rule per direction.
 *  - **But not the directly-named hypotheses.** A def named as a hypothesis
 *    binder is already a row in the H.1 matrix; re-surfacing it is redundant. We
 *    drop a decl ONLY when it is named exclusively as a direct hypothesis (never
 *    in a conclusion, never reached transitively through another decl's body).
 *  - **Structures count.** A `structure` is an assumption BUNDLE — its fields are
 *    conditions (measurability, membership, identities) — so an untagged build-
 *    inline structure (e.g. the law structure carrying A1 regularity) is surfaced
 *    and its body is walked like any other node.
 *  - **ℝ-valued quantities only when named in a conclusion.** A non-Prop,
 *    non-`∃`-constant `def`/`abbrev` (an ℝ-valued formula — a rate exponent,
 *    estimand, threshold) is surfaced (`flavor: "quantity"`) ONLY when named
 *    DIRECTLY in a conclusion, where its formula defines what is proved (a wrong
 *    constant/exponent/sign mis-states the theorem). Deep arithmetic plumbing
 *    reached only inside other helpers stays out — surfacing every helper would
 *    drown the gate; hypothesis-side quantities are the safe asymmetric direction.
 *
 * Decls that already carry an obj_id (genuine P-blocks) are skipped — already rows.
 */
export async function findHiddenStatementDefs(leanDir: string): Promise<HiddenStatementDef[]> {
  const decls = await parseAllDecls(leanDir);
  // Meaning-bearing nodes: def/abbrev/structure. Theorems/lemmas (proofs) are NOT
  // nodes — they don't constitute the statement's meaning.
  const nodeByName = new Map<string, FullDecl>();
  for (const d of decls) {
    if (
      (d.kind === "def" || d.kind === "abbrev" || d.kind === "structure") &&
      d.name &&
      !nodeByName.has(d.name)
    ) {
      nodeByName.set(d.name, d);
    }
  }
  const theorems = decls.filter((d) => {
    if (d.kind !== "theorem") return false;
    const id = deriveObjId("theorem", d.name, d.commentAbove);
    return id?.startsWith("T-") || id?.startsWith("thm:");
  });
  // BFS the decl-reference graph from each T-block statement (both regions),
  // recording reaching T-ids, the directly-named hypothesis / conclusion node
  // sets, and which nodes are reached transitively (via another node's body).
  const reachedBy = new Map<string, Set<string>>();
  const directHyp = new Set<string>();
  const directConcl = new Set<string>();
  const transitive = new Set<string>();
  const MAX_DEPTH = 8;
  for (const thm of theorems) {
    const tid = deriveObjId("theorem", thm.name, thm.commentAbove)!;
    const { hyp, concl } = splitStatement(statementText(thm.text));
    for (const id of leanIdentifiers(hyp)) directHyp.add(id);
    for (const id of leanIdentifiers(concl)) directConcl.add(id);
    const seen = new Set<string>();
    let frontier = new Set([...leanIdentifiers(hyp), ...leanIdentifiers(concl)]);
    for (let depth = 0; depth < MAX_DEPTH && frontier.size > 0; depth++) {
      const next = new Set<string>();
      for (const id of frontier) {
        if (seen.has(id)) continue;
        seen.add(id);
        const d = nodeByName.get(id);
        if (!d) continue;
        if (!reachedBy.has(id)) reachedBy.set(id, new Set());
        reachedBy.get(id)!.add(tid);
        for (const c of leanIdentifiers(d.text)) {
          // `c !== id`: a decl's own text contains its `def <name>` header, so
          // skip the self-reference — otherwise every reached node marks ITSELF
          // transitive and the direct-hypothesis-only exclusion never fires.
          if (c !== id && nodeByName.has(c)) transitive.add(c); // reached via a decl body
          if (!seen.has(c)) next.add(c);
        }
      }
      frontier = next;
    }
  }
  const out: HiddenStatementDef[] = [];
  for (const [name, tids] of reachedBy) {
    const d = nodeByName.get(name)!;
    if (deriveObjId("def", d.name, d.commentAbove) !== null) continue; // already a P-row
    // Drop decls named ONLY as a direct hypothesis — the H.1 matrix already covers
    // those. Keep anything reached transitively or named in a conclusion.
    if (directHyp.has(name) && !directConcl.has(name) && !transitive.has(name)) continue;
    let flavor: HiddenDefFlavor;
    if (CONSTANT_EXISTENTIAL_RE.test(d.text)) flavor = "const-exist";
    else if (d.kind === "structure") flavor = "structure";
    else if (isPropValued(d.text)) flavor = "predicate";
    // An ℝ-valued computational quantity (rate / estimand / threshold) is surfaced
    // ONLY when named DIRECTLY in a conclusion — there its FORMULA defines what is
    // proved, so a wrong constant/exponent/sign mis-states the theorem. Restricting
    // to directly-conclusion-named keeps deep arithmetic plumbing out of the gate;
    // hypothesis-side quantities are the safe asymmetric direction.
    else if (directConcl.has(name)) flavor = "quantity";
    else continue; // computational helper not named in a conclusion → out of scope
    out.push({
      name,
      file: d.file,
      line: d.line,
      kind: d.kind,
      flavor,
      reachedFrom: [...tids].sort(),
      contentHash: statementHash(d.text),
    });
  }
  out.sort((a, b) => a.name.localeCompare(b.name));
  return out;
}
