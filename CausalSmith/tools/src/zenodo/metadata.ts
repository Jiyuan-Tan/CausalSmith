/** Build Zenodo deposition metadata from a presentation bundle's `meta.json`.
 *
 * Pure: no I/O, no clock, no network — so the exact payload that would be sent is
 * testable and `--dry-run` shows the truth.
 *
 * THE TeX PROBLEM. Bundle titles and abstracts are LaTeX source: they carry inline
 * math (`\(\epsilon\in(0,1/2)\)`), display math (`\[\frac1n+\frac{d^2}{n^2(\log n)^2}\]`),
 * and citation commands (`\citet{...}`). Zenodo renders the description as a small
 * sanitized HTML subset (`p`, `br`, `em`, `strong`, `sub`, `sup`, `ul`, `ol`, `li`, `a`)
 * and has NO math typesetting at all — a KaTeX-rendered span, or raw `\epsilon`, both
 * read as garbage on the record page. So math is flattened to Unicode
 * (`\epsilon` → ε, `^{2}` → `<sup>2</sup>`, `\frac{a}{b}` → `a/b`), which is lossy but
 * legible, and the authoritative typeset form stays in the attached PDF.
 */

import { stripTexComments } from "../shared/tex_text.js";

// ---------------------------------------------------------------------------
// Bundle meta
// ---------------------------------------------------------------------------

/** The fields of a bundle `meta.json` this module reads. The index signature is load
 *  bearing: every writer of this file must preserve keys it does not understand. */
export interface BundleMeta {
  qid?: string;
  spec?: string;
  title?: string;
  tldr?: string;
  abstract?: string;
  area?: string;
  created?: string;
  revised?: string;
  version?: number;
  wp_number?: string | null;
  doi?: string | null;
  version_doi?: string | null;
  score?: number;
  [key: string]: unknown;
}

// ---------------------------------------------------------------------------
// TeX → Unicode
// ---------------------------------------------------------------------------

/** Control words that map to a single character. Ordered longest-first at use time so
 *  `\epsilon` is not eaten by a hypothetical `\eps`. */
const SYMBOLS: Readonly<Record<string, string>> = {
  // VARIANT FORMS ARE DISTINCT CHARACTERS. TeX's `\phi` and `\varphi` are two
  // different glyphs and papers use both in one formula; collapsing them onto "φ"
  // turned `\(\phi\ne\varphi\)` into the false statement "φ ≠ φ" on a permanent
  // record. Unicode's own names settle which is which: U+03D5 GREEK PHI SYMBOL is the
  // closed/loopy form TeX draws for `\phi`, U+03C6 GREEK SMALL LETTER PHI the open one
  // it draws for `\varphi`; likewise U+03F5 GREEK LUNATE EPSILON SYMBOL for `\epsilon`
  // against U+03B5 for `\varepsilon`.
  alpha: "α", beta: "β", gamma: "γ", delta: "δ",
  epsilon: "\u03f5", varepsilon: "\u03b5",
  zeta: "ζ", eta: "η", theta: "θ", vartheta: "\u03d1", iota: "ι",
  kappa: "κ", varkappa: "\u03f0",
  lambda: "λ", mu: "μ", nu: "ν", xi: "ξ", pi: "π", varpi: "\u03d6",
  rho: "ρ", varrho: "\u03f1", sigma: "σ", varsigma: "\u03c2", tau: "τ", upsilon: "υ",
  phi: "\u03d5", varphi: "\u03c6", chi: "χ", psi: "ψ", omega: "ω",
  Gamma: "Γ", Delta: "Δ", Theta: "Θ", Lambda: "Λ", Xi: "Ξ", Pi: "Π",
  Sigma: "Σ", Upsilon: "Υ", Phi: "Φ", Psi: "Ψ", Omega: "Ω",
  times: "×", cdot: "·", cdots: "⋯", ldots: "…", dots: "…", vdots: "⋮",
  pm: "±", mp: "∓", div: "÷", ast: "∗", star: "⋆", circ: "∘", bullet: "•",
  le: "≤", leq: "≤", ge: "≥", geq: "≥", ne: "≠", neq: "≠", equiv: "≡",
  approx: "≈", sim: "∼", simeq: "≃", cong: "≅", propto: "∝",
  ll: "≪", gg: "≫", lesssim: "≲", gtrsim: "≳", asymp: "≍",
  in: "∈", notin: "∉", ni: "∋", subset: "⊂", subseteq: "⊆",
  supset: "⊃", supseteq: "⊇", cup: "∪", cap: "∩", setminus: "∖",
  emptyset: "∅", varnothing: "∅", forall: "∀", exists: "∃", nexists: "∄",
  neg: "¬", lnot: "¬", land: "∧", wedge: "∧", lor: "∨", vee: "∨",
  to: "→", rightarrow: "→", longrightarrow: "⟶", leftarrow: "←",
  Rightarrow: "⇒", Leftarrow: "⇐", leftrightarrow: "↔", Leftrightarrow: "⇔",
  mapsto: "↦", uparrow: "↑", downarrow: "↓",
  infty: "∞", partial: "∂", nabla: "∇", sum: "∑", prod: "∏", int: "∫",
  iint: "∬", oint: "∮", sqrt: "√", angle: "∠", perp: "⊥", parallel: "∥",
  prime: "′", ell: "ℓ", hbar: "ℏ", Re: "ℜ", Im: "ℑ", aleph: "ℵ",
  oplus: "⊕", otimes: "⊗", odot: "⊙", top: "⊤", bot: "⊥",
  lfloor: "⌊", rfloor: "⌋", lceil: "⌈", rceil: "⌉",
  langle: "⟨", rangle: "⟩", "|": "\u2016", "\\": " ", mid: "|", vert: "|", Vert: "\u2016",
  quad: " ", qquad: "  ", ",": " ", ";": " ", ":": " ", "!": "", " ": " ",
  indep: "⫫", independent: "⫫",
};

/** Operator names that survive as plain words (`\log n` → `log n`). */
const OPERATORS = new Set([
  "log", "ln", "exp", "sin", "cos", "tan", "min", "max", "inf", "sup",
  "lim", "limsup", "liminf", "arg", "argmin", "argmax", "det", "dim",
  "ker", "deg", "gcd", "mod", "Pr", "var", "Var", "cov", "Cov", "E",
]);

/**
 * Exact Unicode mappings for TeX's math font macros.
 *
 * WHY EXACTNESS IS THE WHOLE POINT. Typography carries mathematical identity here:
 * `\mathbf{x}` is a vector and `x` is a scalar, `\mathcal{F}` is a sigma-algebra and
 * `F` is a distribution function. The previous version simply dropped the macro and
 * emitted the argument, so `\mathbf{x}=x` rendered as `x=x` — a statement the paper
 * does not make. A font is therefore applied ONLY when every character of the argument
 * has a real code point in the corresponding Unicode math-alphanumeric block; when even
 * one does not, the whole macro is preserved as visible source instead.
 *
 * Each entry gives the block starts for A-Z, a-z and 0-9 (null where the block has no
 * digits) plus the holes: Unicode unified a handful of these letters into the
 * Letterlike Symbols block, so the arithmetic start+offset lands on a reserved code
 * point for exactly those and the exception table supplies the real character.
 */
interface MathFont {
  readonly upper: number | null;
  readonly lower: number | null;
  readonly digit: number | null;
  readonly holes?: Readonly<Record<string, string>>;
}

const MATH_FONTS: Readonly<Record<string, MathFont>> = {
  mathbf: { upper: 0x1d400, lower: 0x1d41a, digit: 0x1d7ce },
  mathit: { upper: 0x1d434, lower: 0x1d44e, digit: null, holes: { h: "\u210e" } },
  mathnormal: { upper: 0x1d434, lower: 0x1d44e, digit: null, holes: { h: "\u210e" } },
  boldsymbol: { upper: 0x1d468, lower: 0x1d482, digit: null },
  bm: { upper: 0x1d468, lower: 0x1d482, digit: null },
  mathsf: { upper: 0x1d5a0, lower: 0x1d5ba, digit: 0x1d7e2 },
  mathbb: {
    upper: 0x1d538, lower: 0x1d552, digit: 0x1d7d8,
    holes: { C: "\u2102", H: "\u210d", N: "\u2115", P: "\u2119", Q: "\u211a", R: "\u211d", Z: "\u2124" },
  },
  mathcal: {
    upper: 0x1d49c, lower: 0x1d4b6, digit: null,
    holes: {
      B: "\u212c", E: "\u2130", F: "\u2131", H: "\u210b", I: "\u2110",
      L: "\u2112", M: "\u2133", R: "\u211b", e: "\u212f", g: "\u210a", o: "\u2134",
    },
  },
  mathscr: {
    upper: 0x1d49c, lower: 0x1d4b6, digit: null,
    holes: {
      B: "\u212c", E: "\u2130", F: "\u2131", H: "\u210b", I: "\u2110",
      L: "\u2112", M: "\u2133", R: "\u211b", e: "\u212f", g: "\u210a", o: "\u2134",
    },
  },
  mathfrak: {
    upper: 0x1d504, lower: 0x1d51e, digit: null,
    holes: { C: "\u212d", H: "\u210c", I: "\u2111", R: "\u211c", Z: "\u2128" },
  },
};

/** Upright text. `\mathrm{Var}` and `\operatorname{supp}` ARE their argument set
 *  upright, and ordinary Latin letters are already upright, so this mapping is exact.
 *
 *  `\mathnormal` is deliberately NOT here: it selects math ITALIC, the default face for
 *  variables, which is a different glyph from upright roman and is what distinguishes a
 *  variable from a multi-letter operator name. It maps through {@link MATH_FONTS}. */
const UPRIGHT_MACROS = new Set(["mathrm", "operatorname"]);

/** Every font macro this converter recognises at all. */
const FONT_MACROS = new Set([...Object.keys(MATH_FONTS), ...UPRIGHT_MACROS]);

/**
 * Render `text` in `font`, or null when any character lacks an exact code point.
 *
 * Null is the important return: it is what makes the caller preserve the source rather
 * than quietly drop a distinction it cannot express.
 */
function applyMathFont(name: string, text: string): string | null {
  if (UPRIGHT_MACROS.has(name)) return /^[\x20-\x7e]*$/.test(text) ? text : null;
  const font = MATH_FONTS[name];
  if (!font || text.length === 0) return null;
  let out = "";
  for (const ch of text) {
    const hole = font.holes?.[ch];
    if (hole !== undefined) { out += hole; continue; }
    const code = ch.codePointAt(0)!;
    if (ch >= "A" && ch <= "Z" && font.upper !== null) out += String.fromCodePoint(font.upper + code - 65);
    else if (ch >= "a" && ch <= "z" && font.lower !== null) out += String.fromCodePoint(font.lower + code - 97);
    else if (ch >= "0" && ch <= "9" && font.digit !== null) out += String.fromCodePoint(font.digit + code - 48);
    else return null;
  }
  return out;
}

const SUPERSCRIPTS: Readonly<Record<string, string>> = {
  "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶",
  "7": "⁷", "8": "⁸", "9": "⁹", "+": "⁺", "-": "⁻", "−": "⁻", "=": "⁼",
  "(": "⁽", ")": "⁾", n: "ⁿ", i: "ⁱ", a: "ᵃ", b: "ᵇ", c: "ᶜ", d: "ᵈ",
  e: "ᵉ", k: "ᵏ", m: "ᵐ", p: "ᵖ", t: "ᵗ", T: "ᵀ", " ": " ",
};

const SUBSCRIPTS: Readonly<Record<string, string>> = {
  "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄", "5": "₅", "6": "₆",
  "7": "₇", "8": "₈", "9": "₉", "+": "₊", "-": "₋", "−": "₋", "=": "₌",
  "(": "₍", ")": "₎", a: "ₐ", e: "ₑ", i: "ᵢ", j: "ⱼ", k: "ₖ", l: "ₗ",
  m: "ₘ", n: "ₙ", o: "ₒ", p: "ₚ", r: "ᵣ", s: "ₛ", t: "ₜ", u: "ᵤ",
  v: "ᵥ", x: "ₓ", " ": " ",
  // Greek letters have NO Unicode subscript forms. They are deliberately absent so
  // `mapAll` fails and the caller falls back to `<sub>ε</sub>` / `_ε`. An earlier
  // draft mapped ε to ᵨ (subscript RHO), which silently rewrote `a_ε` as `aᵨ` — a
  // different constant. Never approximate one symbol with another here.
};

/** Control words rendered with a space on each side: relations and binary operators,
 *  where `x∈ℝ` and `n≥N` read as noise without the breathing room TeX supplies
 *  typographically and Unicode does not. */
const SPACED = new Set([
  "le", "leq", "ge", "geq", "ne", "neq", "equiv", "approx", "sim", "simeq",
  "cong", "propto", "ll", "gg", "lesssim", "gtrsim", "asymp",
  "in", "notin", "ni", "subset", "subseteq", "supset", "supseteq", "mid",
  "to", "rightarrow", "longrightarrow", "leftarrow", "Rightarrow", "Leftarrow",
  "leftrightarrow", "Leftrightarrow", "mapsto",
  "pm", "mp", "times", "div", "cup", "cap", "setminus",
  "oplus", "otimes", "land", "lor", "wedge", "vee", "indep", "independent",
]);

/** Macros whose following `[` or `(` is a DELIMITER being sized, not an option. */
const DELIMITER_MACROS = new Set([
  "left", "right", "big", "Big", "bigg", "Bigg",
  "bigl", "bigr", "Bigl", "Bigr", "biggl", "biggr", "Biggl", "Biggr",
  "bigm", "Bigm", "biggm", "Biggm",
]);

/** Combining marks for the accent macros, applied only over a single atom. */
const ACCENTS: Readonly<Record<string, string>> = {
  hat: "\u0302", widehat: "\u0302", bar: "\u0304", overline: "\u0304",
  tilde: "\u0303", widetilde: "\u0303", vec: "\u20d7", dot: "\u0307", ddot: "\u0308",
};

type Mode = "text" | "html";

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

/** Read one TeX group starting at `i` (which must point at `{`); returns the body and
 *  the index just past the closing brace. Brace-depth aware, so `{a{b}c}` is one group. */
function readGroup(src: string, i: number): { body: string; next: number } {
  let depth = 0;
  for (let j = i; j < src.length; j++) {
    if (src[j] === "\\") { j += 1; continue; }
    if (src[j] === "{") depth += 1;
    else if (src[j] === "}") {
      depth -= 1;
      if (depth === 0) return { body: src.slice(i + 1, j), next: j + 1 };
    }
  }
  // Unbalanced source: take the rest rather than dropping it silently.
  return { body: src.slice(i + 1), next: src.length };
}

/** Read the argument after a script marker: a braced group, a control word, or one
 *  character (`x^2`, `x^{2n}`, `x^\epsilon` are all one argument in TeX). */
function readScriptArg(src: string, i: number): { body: string; next: number } {
  if (src[i] === "{") return readGroup(src, i);
  if (src[i] === "\\") {
    const m = /^\\([A-Za-z]+)/.exec(src.slice(i));
    if (m) return { body: m[0], next: i + m[0].length };
    return { body: src.slice(i, i + 2), next: i + 2 };
  }
  return { body: src[i] ?? "", next: i + 1 };
}

/** Map every character through `table`, or return null when any character has no
 *  mapping — the caller then falls back to a readable `^(...)` / `<sup>` form. */
function mapAll(s: string, table: Readonly<Record<string, string>>): string | null {
  let out = "";
  for (const ch of s) {
    const mapped = table[ch];
    if (mapped === undefined) return null;
    out += mapped;
  }
  return out;
}

/** Flatten a math fragment to Unicode. Recursive, so `\frac{d^2}{n^2(\log n)^2}`
 *  becomes `d²/(n²(log n)²)`. */
function convertMath(src: string, mode: Mode): string {
  // `{a \over b}` is TeX's infix fraction: it divides the GROUP it sits in, so it has
  // to be handled before the left-to-right scan rather than as a token within it.
  const over = findTopLevelOver(src);
  if (over !== null) {
    const lhs = fracSide(convertMath(src.slice(0, over.at), mode));
    const rhs = fracSide(convertMath(src.slice(over.at + over.length), mode));
    return `${lhs}/${rhs}`;
  }
  let out = "";
  let i = 0;
  while (i < src.length) {
    const ch = src[i];

    if (ch === "\\") {
      const word = /^\\([A-Za-z]+)\*?/.exec(src.slice(i));
      if (word) {
        const name = word[1];
        const macroStart = i;
        i += word[0].length;
        // An OPTIONAL argument means a variant this converter does not implement
        // (`\sqrt[3]{x}` is a cube root, not a square root of `[3]x`). Guessing would
        // silently change the mathematics, so the source is preserved instead.
        // DELIMITER macros are exempt: in `\left[x\right]` the bracket is the
        // delimiter being sized, not an option, and treating it as one preserved
        // perfectly ordinary mathematics as unreadable source.
        if (!DELIMITER_MACROS.has(name) && nextNonSpace(src, i) === "[") {
          const raw = captureMacroSource(src, macroStart);
          i = raw.next;
          out += preserveTex(raw.source, mode);
          continue;
        }
        if (name === "frac" || name === "dfrac" || name === "tfrac") {
          // `\frac1n` (single-token args) is as legal as `\frac{a}{b}`.
          while (src[i] === " ") i += 1;
          const a = readScriptArg(src, i); i = a.next;
          while (src[i] === " ") i += 1;
          const b = readScriptArg(src, i); i = b.next;
          const flat = `${fracSide(convertMath(a.body, mode))}/${fracSide(convertMath(b.body, mode))}`;
          out += bracketIfAdjacent(out, flat, src, i);
          continue;
        }
        if (name === "begin") {
          const env = captureEnvironment(src, macroStart);
          if (env) { i = env.next; out += preserveTex(env.source, mode); continue; }
        }
        if (name === "binom" || name === "dbinom" || name === "tbinom") {
          // `C(n, k)` is the one unambiguous flattening of a built-up binomial; the
          // stacked form has no linear equivalent and "n choose k" reads as prose.
          while (src[i] === " ") i += 1;
          const a = readScriptArg(src, i); i = a.next;
          while (src[i] === " ") i += 1;
          const b = readScriptArg(src, i); i = b.next;
          out += `C(${convertMath(a.body, mode).trim()}, ${convertMath(b.body, mode).trim()})`;
          continue;
        }
        if (name === "sqrt") {
          while (src[i] === " ") i += 1;
          const a = readScriptArg(src, i); i = a.next;
          out += bracketIfAdjacent(out, `√${fracSide(convertMath(a.body, mode))}`, src, i);
          continue;
        }
        if (FONT_MACROS.has(name)) {
          while (src[i] === " ") i += 1;
          const a = readScriptArg(src, i);
          const mapped = applyMathFont(name, convertMath(a.body, mode));
          if (mapped === null) {
            // No exact rendering exists, so the distinction the font carries would be
            // silently lost. Show the source instead.
            const raw = captureMacroSource(src, macroStart);
            i = raw.next;
            out += preserveTex(raw.source, mode);
            continue;
          }
          i = a.next;
          // `mapped` came from convertMath, which has already escaped for this mode;
          // escaping again turned `\mathrm{A\&B}` into `A&amp;amp;B`.
          out += mapped;
          continue;
        }
        if (name === "text" || name === "textrm" || name === "mbox" || name === "mathrm" || name === "operatorname") {
          while (src[i] === " ") i += 1;
          const a = readScriptArg(src, i); i = a.next;
          out += mode === "html" ? escapeHtml(a.body) : a.body;
          continue;
        }
        // A combining accent attaches to ONE character. `\overline{A\cup B}` means the
        // bar spans the whole expression; emitting "A∪B" followed by a combining macron
        // puts the bar over the B alone, which is a different statement. Only a single
        // atom is converted; anything wider is shown as source.
        if (ACCENTS[name] !== undefined) {
          const a = readScriptArg(src, i);
          const inner = convertMath(a.body, mode).trim();
          if (isSingleAtom(inner)) { i = a.next; out += `${inner}${ACCENTS[name]}`; continue; }
          const raw = captureMacroSource(src, macroStart);
          i = raw.next;
          out += preserveTex(raw.source, mode);
          continue;
        }
        if (DELIMITER_MACROS.has(name)) {
          // The sized delimiter follows the macro. `\left.` / `\right.` are the "no
          // delimiter" forms and must swallow the dot rather than print it; `\left|`
          // and `\right\|` carry the bars that the normal character path would
          // otherwise have to guess at.
          let j = i;
          while (src[j] === " ") j += 1;
          if (src[j] === ".") { i = j + 1; continue; }
          if (src[j] === "|") { i = j + 1; out += "|"; continue; }
          if (src[j] === "\\" && src[j + 1] === "|") { i = j + 2; out += "\u2016"; continue; }
          continue;
        }
        if (name === "displaystyle" || name === "textstyle" || name === "limits" ||
            name === "nolimits" || name === "label" || name === "nonumber") {
          if (name === "label") { while (src[i] === " ") i += 1; if (src[i] === "{") i = readGroup(src, i).next; }
          continue;
        }
        if (OPERATORS.has(name)) {
          // `n\log n` has no space before `\log`; without one it flattens to `nlogn`.
          if (/[\p{L}\p{N}]$/u.test(out)) out += " ";
          out += mode === "html" ? escapeHtml(name) : name;
          // A control word swallows the space after it in TeX; keep one so
          // `\log n` does not become `logn`.
          if (src[i] === " ") i += 1;
          if (/^[\p{L}\p{N}(]/u.test(src.slice(i))) out += " ";
          continue;
        }
        const sym = SYMBOLS[name];
        if (sym !== undefined) {
          // TeX lets a control word eat the space that terminates it, so the source
          // space carries no meaning; spacing is decided by the symbol's role.
          if (src[i] === " ") i += 1;
          out += SPACED.has(name) ? ` ${sym} ` : sym;
          continue;
        }
        // Unknown control word. Dropping the backslash used to turn `\foo{y}` into
        // `fooy`, which reads as mathematics and is not. Preserve the source.
        const raw = captureMacroSource(src, macroStart);
        i = raw.next;
        out += preserveTex(raw.source, mode);
        continue;
      }
      // Escaped punctuation: `\%`, `\&`, `\_`, `\{`, `\\`.
      const esc = src[i + 1] ?? "";
      i += 2;
      if (esc === "\\") { out += " "; continue; }
      out += SYMBOLS[esc] ?? (mode === "html" ? escapeHtml(esc) : esc);
      continue;
    }

    if (ch === "^" || ch === "_") {
      const a = readScriptArg(src, i + 1);
      i = a.next;
      const inner = convertMath(a.body, mode);
      const table = ch === "^" ? SUPERSCRIPTS : SUBSCRIPTS;
      const mapped = mapAll(inner, table);
      if (mapped !== null) out += mapped;
      else if (mode === "html") out += ch === "^" ? `<sup>${inner}</sup>` : `<sub>${inner}</sub>`;
      else out += inner.length === 1 ? `${ch}${inner}` : `${ch}(${inner})`;
      continue;
    }

    if (ch === "{" ) { const g = readGroup(src, i); i = g.next; out += convertMath(g.body, mode); continue; }
    if (ch === "}") { i += 1; continue; }
    if (ch === "&") { i += 1; out += " "; continue; }

    i += 1;
    out += mode === "html" ? escapeHtml(ch) : ch;
  }
  return out.replace(/[ \t]{2,}/g, " ");
}

/** Position of an `\over`/`\atop` at brace depth 0, or null. */
function findTopLevelOver(src: string): { at: number; length: number } | null {
  let depth = 0;
  for (let i = 0; i < src.length; i++) {
    const ch = src[i];
    if (ch === "\\") {
      const m = /^\\(over|atop)(?![A-Za-z])/.exec(src.slice(i));
      if (m && depth === 0) return { at: i, length: m[0].length };
      i += 1;
      continue;
    }
    if (ch === "{") depth += 1;
    else if (ch === "}") depth -= 1;
  }
  return null;
}

/** The next non-space character at or after `i`, or "" at end of input. */
function nextNonSpace(src: string, i: number): string {
  let j = i;
  while (j < src.length && src[j] === " ") j += 1;
  return src[j] ?? "";
}

/**
 * Capture a macro call verbatim: `\name`, any `[optional]` arguments, and any `{braced}`
 * arguments that follow it. Returns the exact source text so it can be shown rather
 * than interpreted.
 */
function captureMacroSource(src: string, start: number): { source: string; next: number } {
  const word = /^\\([A-Za-z]+)\*?/.exec(src.slice(start));
  if (!word) return { source: src.slice(start, start + 2), next: start + 2 };
  let i = start + word[0].length;
  for (;;) {
    let j = i;
    while (j < src.length && src[j] === " ") j += 1;
    if (src[j] === "[") {
      const close = src.indexOf("]", j);
      if (close === -1) break;
      i = close + 1;
      continue;
    }
    if (src[j] === "{") {
      i = readGroup(src, j).next;
      continue;
    }
    break;
  }
  return { source: src.slice(start, i), next: i };
}

/**
 * Capture a whole `\begin{env}…\end{env}` span, nesting-aware.
 *
 * An environment must be preserved ENTIRE or not at all. Preserving only the
 * `\begin{cases}` token and then converting the body flattens `&` and `\\` into
 * spaces, turning a piecewise definition into a run-on list of clauses that reads as
 * one formula — the exact silent mistranslation this converter is supposed to refuse.
 */
function captureEnvironment(src: string, start: number): { source: string; next: number } | null {
  const open = /^\\begin\s*\{([^{}]*)\}/.exec(src.slice(start));
  if (!open) return null;
  const env = open[1];
  const token = new RegExp(String.raw`\\(begin|end)\s*\{${env.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\}`, "g");
  token.lastIndex = start;
  let depth = 0;
  for (let m = token.exec(src); m !== null; m = token.exec(src)) {
    if (m[1] === "begin") depth += 1;
    else if (--depth === 0) return { source: src.slice(start, m.index + m[0].length), next: m.index + m[0].length };
  }
  return null;
}

/**
 * Show TeX source that this converter will not interpret.
 *
 * Failing closed rather than guessing. A silently mistranslated formula looks correct
 * and is wrong forever on a published record; a visible `\foo{y}` in a monospace span
 * is obviously untranslated, and a reader can go to the PDF, which is the authoritative
 * typeset form anyway. `<code>` is inside Zenodo's allowed tag subset.
 */
function preserveTex(source: string, mode: Mode): string {
  return mode === "html" ? `<code>${escapeHtml(source)}</code>` : source;
}

/**
 * True when `s` is a single atom: one letter or digit plus any combining marks or
 * Unicode script characters attached to it (`d²`, `τ̂ₙ`, `n`).
 *
 * Used to decide when a fraction operand needs parentheses. `1/n` is unambiguous;
 * `ab/cd` is not — TeX set it as a built-up fraction and the flattened form has to say
 * so with brackets or it means something else.
 */
function isSingleAtom(s: string): boolean {
  return /^[\p{L}\p{N}][\p{M}⁰-₟²³¹]*$/u.test(s);
}

/**
 * Bracket a flattened built-up construct when something is written against it.
 *
 * TeX set `\frac{1}{2}n` as a fraction with an `n` beside it; flattened to `1/2n` that
 * reads as 1/(2n). The same trap catches `a/\frac{b}{c}` (a/b/c), `\frac{a}{b}^2`
 * (a/b²) and `\sqrt{2}n` (√2n → √(2n) to a reader). None of these occur in the current
 * 22 bundles, which is exactly why they are worth closing now rather than after one
 * reaches a permanent record.
 *
 * Brackets are added only when an adjacency actually exists: a character already
 * written that binds to the left, or a script/atom/slash coming up on the right.
 */
function bracketIfAdjacent(before: string, flat: string, src: string, at: number): string {
  if (flat.length <= 1) return flat;
  if (isFullyBracketed(flat)) return flat;

  // Division on the left: `a/\frac{b}{c}` flattens to `a/b/c`, which reads as (a/b)/c.
  const leftBinds = before.endsWith("/");

  // On the right, only three things bind: a script, a juxtaposed atom, or a macro that
  // IS an atom. A closing delimiter is not one of them — `\frac{…}{q}\right)` needs no
  // brackets and adding them just makes the record page noisier.
  const next = src.slice(at).replace(/^ +/, "");
  let rightBinds = false;
  if (/^[\^_]/.test(next)) rightBinds = true;
  // A juxtaposed group multiplies: `\frac{1}{n}(a+b)` is (1/n)(a+b), not 1/(n(a+b)).
  else if (/^[\p{L}\p{N}(]/u.test(next)) rightBinds = true;
  else if (next.startsWith("\\")) {
    const m = /^\\([A-Za-z]+)/.exec(next);
    if (m !== null) {
      const name = m[1];
      if (DELIMITER_MACROS.has(name)) {
        // An OPENING delimiter binds (it starts a juxtaposed group); a closing one does
        // not (it ends the group this construct is already inside).
        const after = next.slice(m[0].length).replace(/^ +/, "");
        rightBinds = name === "left" ||
          (!/r$|^right$/.test(name) && /^[([{]|^\\[{|]/.test(after));
      } else {
        rightBinds = name !== "nonumber" && name !== "label" && name !== "end";
      }
    }
  }

  if (!leftBinds && !rightBinds) return flat;
  // `\sqrt n\log n` becomes `(√n)log n` without this: the operator branch only adds a
  // separating space when what precedes it is alphanumeric, and `)` is not.
  const needsSpace = /^\\([A-Za-z]+)/.exec(next);
  const spacer = needsSpace && OPERATORS.has(needsSpace[1]) ? " " : "";
  return `(${flat})${spacer}`;
}

/**
 * Is `s` wrapped in ONE pair of parentheses spanning the whole string?
 *
 * `/^\(.*\)$/` is not that test: `(a+b)(c+d)` matches it while being two groups side by
 * side, so a caller relying on it left `\frac{1}{(a+b)(c+d)}` as the ambiguous
 * `1/(a+b)(c+d)`. This walks the depth and requires the first `(` to close at the last
 * character.
 */
function isFullyBracketed(s: string): boolean {
  if (s.length < 2 || !s.startsWith("(") || !s.endsWith(")")) return false;
  let depth = 0;
  for (let i = 0; i < s.length; i += 1) {
    if (s[i] === "(") depth += 1;
    else if (s[i] === ")") {
      depth -= 1;
      if (depth === 0) return i === s.length - 1;
    }
  }
  return false;
}

/** Parenthesize a fraction operand unless it is a single atom. */
function fracSide(s: string): string {
  const t = s.trim();
  if (t.length === 0) return t;
  if (isSingleAtom(t)) return t;
  if (isFullyBracketed(t)) return t;
  return `(${t})`;
}

/** Split prose into math and non-math runs. `$…$`, `$$…$$`, `\(…\)` and `\[…\]` all
 *  occur in these bundles. */
const MATH_RE = /\$\$[\s\S]*?\$\$|\\\[[\s\S]*?\\\]|\\\([\s\S]*?\\\)|(?<!\\)\$(?:[^$\\]|\\.)*\$/g;

/** Math body plus whether the source asked for DISPLAY math — `\[…\]` and `$$…$$` are
 *  set off on their own line in TeX, so they become their own `<p>` rather than being
 *  spliced mid-sentence. */
function mathBody(tok: string): { body: string; display: boolean } {
  if (tok.startsWith("$$")) return { body: tok.slice(2, -2), display: true };
  if (tok.startsWith("\\[")) return { body: tok.slice(2, -2), display: true };
  if (tok.startsWith("\\(")) return { body: tok.slice(2, -2), display: false };
  return { body: tok.slice(1, -1), display: false };
}

/** Convert the non-math part of a TeX run: text macros, citations, escapes, dashes. */
function convertProse(src: string, mode: Mode): string {
  const emph = (name: string, body: string): string => {
    const inner = convertProse(body, mode);
    if (mode !== "html") return inner;
    if (name === "texttt") return `<code>${inner}</code>`;
    if (name === "textbf" || name === "textsc") return `<strong>${inner}</strong>`;
    return `<em>${inner}</em>`;
  };

  let out = "";
  let i = 0;
  while (i < src.length) {
    const ch = src[i];
    if (ch === "\\") {
      const word = /^\\([A-Za-z]+)\*?/.exec(src.slice(i));
      if (word) {
        const name = word[1];
        let j = i + word[0].length;
        // Citations carry information a reader of the Zenodo page cannot otherwise
        // recover (there is no bibliography on the record page), and dropping them
        // leaves sentences like "as shown by , the rate…". Keeping the key in
        // brackets is ugly but honest; see the WP-C report for the judgment call.
        if (/^(?:citet|citep|cite|citeauthor|citeyear|citealp|citealt)$/.test(name)) {
          if (src[j] === "[") { const k = src.indexOf("]", j); j = k === -1 ? j : k + 1; }
          if (src[j] === "[") { const k = src.indexOf("]", j); j = k === -1 ? j : k + 1; }
          let keys = "";
          if (src[j] === "{") { const g = readGroup(src, j); keys = g.body; j = g.next; }
          i = j;
          const pretty = keys.split(",").map((k) => k.trim()).filter(Boolean).join(", ");
          out += pretty ? `[${mode === "html" ? escapeHtml(pretty) : pretty}]` : "";
          continue;
        }
        // Cross-references have no target on a Zenodo page: keep the bare label.
        if (/^(?:ref|cref|Cref|autoref|eqref|pageref|label)$/.test(name)) {
          let body = "";
          if (src[j] === "{") { const g = readGroup(src, j); body = g.body; j = g.next; }
          i = j;
          if (name !== "label") {
            const bare = body.replace(/^[a-z]+:/, "");
            out += mode === "html" ? escapeHtml(bare) : bare;
          }
          continue;
        }
        if (/^(?:emph|textit|textsl|textbf|textsc|texttt|textrm|textsf|text|mbox)$/.test(name)) {
          let body = "";
          if (src[j] === "{") { const g = readGroup(src, j); body = g.body; j = g.next; }
          i = j;
          out += emph(name, body);
          continue;
        }
        if (name === "footnote" || name === "thanks") {
          if (src[j] === "{") j = readGroup(src, j).next;
          i = j;
          continue;
        }
        if (name === "begin") {
          const env = captureEnvironment(src, i);
          if (env) { i = env.next; out += preserveTex(env.source, mode); continue; }
        }
        const sym = SYMBOLS[name];
        if (sym !== undefined) { i = j; out += sym; if (src[i] === " ") i += 1; continue; }
        // Unknown prose macro: show the source rather than a mangled word.
        const raw = captureMacroSource(src, i);
        i = raw.next;
        out += preserveTex(raw.source, mode);
        continue;
      }
      const esc = src[i + 1] ?? "";
      i += 2;
      if (esc === "\\") { out += mode === "html" ? "<br />" : "\n"; continue; }
      out += mode === "html" ? escapeHtml(esc) : esc;
      continue;
    }
    if (ch === "~") { i += 1; out += " "; continue; }
    if (ch === "{" || ch === "}") { i += 1; continue; }
    if (src.startsWith("---", i)) { i += 3; out += "—"; continue; }
    if (src.startsWith("--", i)) { i += 2; out += "–"; continue; }
    if (src.startsWith("``", i)) { i += 2; out += "“"; continue; }
    if (src.startsWith("''", i)) { i += 2; out += "”"; continue; }
    i += 1;
    out += mode === "html" ? escapeHtml(ch) : ch;
  }
  return out;
}

/** Convert a TeX-bearing string to a single line of plain Unicode text. Use for the
 *  Zenodo `title`, which is not HTML. */
export function texToPlainText(tex: string): string {
  return convertTex(tex, "text").replace(/\s+/g, " ").trim();
}

/** Convert a TeX-bearing string to the small HTML subset Zenodo renders. Paragraphs
 *  (blank lines in the source) become `<p>`; math becomes Unicode. */
export function texToHtml(tex: string): string {
  const paragraphs = convertTex(tex, "html")
    .split(/\n\s*\n/)
    .map((p) => p.replace(/[ \t]*\n[ \t]*/g, " ").replace(/[ \t]{2,}/g, " ").trim())
    .filter((p) => p.length > 0);
  return paragraphs.map((p) => `<p>${p}</p>`).join("\n");
}

function convertTex(tex: string, mode: Mode): string {
  const src = stripTexComments(tex ?? "");
  let out = "";
  let last = 0;
  for (const m of src.matchAll(MATH_RE)) {
    out += convertProse(src.slice(last, m.index), mode);
    const { body, display } = mathBody(m[0]);
    const rendered = convertMath(body, mode).trim();
    out += display ? `\n\n${rendered}\n\n` : rendered;
    last = m.index + m[0].length;
  }
  out += convertProse(src.slice(last), mode);
  return out;
}

// ---------------------------------------------------------------------------
// Zenodo metadata
// ---------------------------------------------------------------------------

export interface RelatedIdentifier {
  identifier: string;
  relation: string;
  scheme?: string;
  resource_type?: string;
}

export interface ZenodoMetadata {
  upload_type: "publication";
  publication_type: "workingpaper";
  title: string;
  description: string;
  creators: { name: string }[];
  publication_date: string;
  access_right: "open";
  license: string;
  version?: string;
  keywords?: string[];
  notes?: string;
  related_identifiers?: RelatedIdentifier[];
  communities?: { identifier: string }[];
}

export interface BuildMetadataOptions {
  /** Bundle directory basename — the site's paper id. */
  readonly bundleId: string;
  /** Site root, e.g. `https://causalsmith.org`. Trailing slash optional. */
  readonly siteBaseUrl: string;
  /** Public code repository. */
  readonly repoUrl?: string;
  /** Zenodo licence id. Defaults to `cc-by-4.0` — see the docstring below. */
  readonly license?: string;
  /** Zenodo community identifiers to submit the record to. */
  readonly communities?: readonly string[];
  /** Overrides the `[TEST]`-prefixing rule; set by the CLI for sandbox runs. */
  readonly titlePrefix?: string;
  /** Deterministic bundle marker, appended to `notes`. It is how a crashed `reserve`
   *  finds the draft it already created (Zenodo's deposit search matches a quoted
   *  phrase against the notes field), so it MUST survive every metadata rewrite. */
  readonly marker?: string;
}

/** The repository's `LICENSE` is Apache-2.0, which licenses the CODE. A Zenodo
 *  `publication` deposit is the PAPER, and Apache-2.0 is not a document licence
 *  (it has no provision for adaptations of prose and is not recognised as an open
 *  *content* licence by SHERPA/DOAJ). The default here is therefore CC-BY-4.0, the
 *  standard preprint/working-paper licence, with the Apache-2.0 grant over the
 *  accompanying Lean sources stated in `notes`. Override with `--license` if the user
 *  decides otherwise. */
export const DEFAULT_LICENSE = "cc-by-4.0";

export const CORPORATE_AUTHOR = "CausalSmith";

function trimSlash(url: string): string {
  return url.replace(/\/+$/, "");
}

/** ISO date or null. Zenodo rejects anything else outright, and a silently wrong
 *  `publication_date` is worse than a loud failure. */
function isoDate(value: unknown): string | null {
  return typeof value === "string" && /^\d{4}-\d{2}-\d{2}$/.test(value.trim())
    ? value.trim()
    : null;
}

/** The paper's canonical page on the site. */
export function paperUrl(siteBaseUrl: string, bundleId: string): string {
  return `${trimSlash(siteBaseUrl)}/papers/${bundleId}`;
}

/**
 * Build the Zenodo metadata payload for a bundle.
 *
 * RELATION TYPES (judgment call, see report). The site's `/papers/<id>` page is the
 * same working paper served as HTML — DataCite defines `IsIdenticalTo` as "the
 * resource is identical to the referenced resource but presented in another format",
 * which is exactly that, so the site URL gets `isIdenticalTo`. The GitHub repository
 * is a different resource that accompanies the paper (the Lean formalization), so it
 * gets `isSupplementedBy` with `resource_type: software`. Using `isSupplementedBy` for
 * the site page would be wrong in the other direction: the landing page does not
 * supplement the paper, it hosts it.
 */
export function buildZenodoMetadata(
  meta: BundleMeta,
  opts: BuildMetadataOptions,
): ZenodoMetadata {
  const rawTitle = typeof meta.title === "string" ? meta.title.trim() : "";
  if (!rawTitle) {
    throw new Error(`Bundle ${opts.bundleId}: meta.json has no non-empty "title"; refusing to deposit.`);
  }
  const rawAbstract = typeof meta.abstract === "string" ? meta.abstract.trim() : "";
  if (!rawAbstract) {
    throw new Error(`Bundle ${opts.bundleId}: meta.json has no non-empty "abstract"; refusing to deposit.`);
  }
  const publicationDate = isoDate(meta.revised) ?? isoDate(meta.created);
  if (!publicationDate) {
    throw new Error(
      `Bundle ${opts.bundleId}: neither "revised" nor "created" is an ISO yyyy-mm-dd date ` +
        `(revised=${JSON.stringify(meta.revised)}, created=${JSON.stringify(meta.created)}).`,
    );
  }

  const title = `${opts.titlePrefix ?? ""}${texToPlainText(rawTitle)}`;
  const description = texToHtml(rawAbstract);

  const keywords = ["causal inference", "formal verification", "Lean 4", "machine-generated research"];
  if (typeof meta.area === "string" && meta.area.trim()) keywords.unshift(meta.area.trim());

  const related: RelatedIdentifier[] = [
    {
      identifier: paperUrl(opts.siteBaseUrl, opts.bundleId),
      relation: "isIdenticalTo",
      scheme: "url",
      resource_type: "publication-workingpaper",
    },
  ];
  if (opts.repoUrl) {
    related.push({
      identifier: trimSlash(opts.repoUrl),
      relation: "isSupplementedBy",
      scheme: "url",
      resource_type: "software",
    });
  }

  const version = typeof meta.version === "number" && Number.isInteger(meta.version) && meta.version >= 1
    ? `v${meta.version}`
    : undefined;

  const wp = typeof meta.wp_number === "string" && meta.wp_number.trim() ? meta.wp_number.trim() : null;

  const out: ZenodoMetadata = {
    upload_type: "publication",
    publication_type: "workingpaper",
    title,
    description,
    creators: [{ name: CORPORATE_AUTHOR }],
    publication_date: publicationDate,
    access_right: "open",
    license: opts.license ?? DEFAULT_LICENSE,
    keywords,
    notes:
      (wp ? `CausalSmith working paper ${wp}. ` : "") +
      "This paper was generated by the CausalSmith automated research pipeline. Its central " +
      "theorem statements are formalized and machine-checked in Lean 4 against the Causalean " +
      "library; the accompanying Lean sources are licensed under Apache-2.0. The prose, " +
      "including the surrounding exposition and discussion, is machine-written and has not " +
      "been peer reviewed." +
      (opts.marker ? `\n\n${opts.marker}` : ""),
    related_identifiers: related,
  };
  if (version) out.version = version;
  if (opts.communities && opts.communities.length > 0) {
    out.communities = opts.communities.map((identifier) => ({ identifier }));
  }
  return out;
}
