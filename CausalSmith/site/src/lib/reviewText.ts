import katex from "katex";
import { texTypography } from "./docmd.js";
import { katexOptions } from "./katexConfig.js";

/**
 * Renders the AI referee report's prose.
 *
 * The referee quotes the manuscript, so its text is LaTeX written for a paper,
 * not for a web page: delimited math, bare math macros loose in a sentence
 * (`the chain R_{n,\ell_1}^\star \le R_{n,\infty}^\star`), backtick spans whose
 * contents are formulas, `\cref`/`\leanref` cross-references, `\texttt{}` with
 * nested braces, `--` en dashes, `~` ties. A macro that reaches the reader is a
 * bug — the reader did not ask to read TeX.
 *
 * The contract this module holds, and the corpus test enforces: NO backslash
 * survives into the rendered output, anywhere, for any input. Three layers get
 * us there:
 *
 *   1. Recognised structure (math, refs, citations, text macros) is rendered.
 *   2. A bare macro run is handed to KaTeX as inline math.
 *   3. Anything KaTeX rejects is TRANSLITERATED — macros become Unicode where
 *      there is an obvious glyph, otherwise the bare command word — and shown
 *      in a `<code>` span, which says "this was notation" without printing
 *      source at the reader.
 *
 * Nothing here can fail a build: every KaTeX call is guarded, and the fallback
 * is pure string work.
 *
 * ACCEPTED LIMITATION. Mathematics a referee typed with NO backslash and NO
 * delimiters — `n^{-4/3}`, `Omega_{n,M}` — is shown exactly as written. That
 * is faithful: it is what the referee typed, and the reader can read it.
 * Guessing where such a run starts and ends from bare text is how a renderer
 * starts eating prose, so this deliberately does not try (audit r4, accepted).
 */

// ── escaping ─────────────────────────────────────────────────────────────

/** Quotes included: this output is also interpolated into title attributes. */
function esc(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

// ── macro → Unicode, for the transliteration fallback ────────────────────

/**
 * Only symbols with an unambiguous single-glyph reading. A macro that is not
 * here degrades to its bare name, which is still readable English ("iffalse",
 * "operatorname") and never a backslash.
 */
const GLYPH: Record<string, string> = {
  alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ε", varepsilon: "ε",
  zeta: "ζ", eta: "η", theta: "θ", vartheta: "ϑ", iota: "ι", kappa: "κ",
  lambda: "λ", mu: "μ", nu: "ν", xi: "ξ", pi: "π", rho: "ρ", varrho: "ϱ",
  sigma: "σ", varsigma: "ς", tau: "τ", upsilon: "υ", phi: "φ", varphi: "φ",
  chi: "χ", psi: "ψ", omega: "ω",
  Gamma: "Γ", Delta: "Δ", Theta: "Θ", Lambda: "Λ", Xi: "Ξ", Pi: "Π",
  Sigma: "Σ", Upsilon: "Υ", Phi: "Φ", Psi: "Ψ", Omega: "Ω",
  le: "≤", leq: "≤", ge: "≥", geq: "≥", neq: "≠", ne: "≠", approx: "≈",
  asymp: "≍", sim: "∼", simeq: "≃", equiv: "≡", propto: "∝",
  ll: "≪", gg: "≫", subset: "⊂", subseteq: "⊆", supset: "⊃", supseteq: "⊇",
  in: "∈", notin: "∉", cup: "∪", cap: "∩", setminus: "∖", emptyset: "∅",
  to: "→", rightarrow: "→", Rightarrow: "⇒", leftarrow: "←", Leftarrow: "⇐",
  leftrightarrow: "↔", Leftrightarrow: "⇔", mapsto: "↦",
  times: "×", cdot: "·", cdots: "⋯", ldots: "…", dots: "…", pm: "±", mp: "∓",
  infty: "∞", partial: "∂", nabla: "∇", forall: "∀", exists: "∃",
  sqrt: "√", sum: "∑", prod: "∏", int: "∫", star: "⋆", ast: "∗",
  perp: "⊥", parallel: "∥", angle: "∠", triangle: "△", otimes: "⊗",
  oplus: "⊕", circ: "∘", bullet: "∙", dagger: "†", ell: "ℓ", hbar: "ℏ",
  Re: "ℜ", Im: "ℑ", aleph: "ℵ", prime: "′", degree: "°", neg: "¬",
  land: "∧", lor: "∨", wedge: "∧", vee: "∨", models: "⊨", vdash: "⊢",
  quad: " ", qquad: " ", ",": " ", ";": " ", ":": " ", "!": "",
};

/** Wrappers whose braces carry meaning only for typesetting. */
const TRANSPARENT = new Set([
  "mathbb", "mathcal", "mathrm", "mathbf", "mathsf", "mathtt", "mathfrak",
  "mathscr", "mathit", "text", "textrm", "textnormal", "mbox", "ensuremath",
  "texttt", "verb", "emph", "textit", "textsl", "textbf", "textsc", "textup",
  "operatorname", "left", "right", "big", "Big", "bigg", "Bigg", "displaystyle",
  "widehat", "hat", "bar", "overline", "tilde", "widetilde", "vec", "dot", "boldsymbol",
]);

/**
 * TeX → readable text, nesting-aware. Used as the fallback when KaTeX cannot
 * parse a run, and by the plain-text citation form.
 *
 * `dropUnknown` distinguishes the two callers. In review prose an unknown
 * command's NAME is informative ("a disabled \iffalse block" → "a disabled
 * iffalse block"), so it is kept. In a citation it is noise, so the command is
 * dropped and only its braced argument survives.
 */
export function texToReadable(src: string, dropUnknown = false): string {
  let out = "";
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === "\\") {
      // `\(`, `\)`, `\[`, `\]` are delimiters, not characters: dropping only
      // the backslash left "(ε)" where the source said "\(\epsilon\)".
      if ("()[]".includes(src[i + 1] ?? "")) {
        i += 2;
        continue;
      }
      const esc2 = /^\\([%&_#$}{ ])/.exec(src.slice(i));
      if (esc2) {
        out += esc2[1];
        i += esc2[0].length;
        continue;
      }
      const m = /^\\([a-zA-Z@]+)/.exec(src.slice(i));
      if (!m) {
        i += 1; // a lone backslash is never content
        continue;
      }
      const name = m[1];
      i += m[0].length;
      // A macro absorbs the space before its own argument, and nothing else:
      // `\iffalse block` must keep the space that separates it from the word.
      if (src[i] === " " && src[i + 1] === "{") i += 1;
      const glyph = GLYPH[name];
      if (glyph !== undefined) {
        out += glyph;
        continue;
      }
      if (TRANSPARENT.has(name)) continue; // its argument speaks for it
      if (!dropUnknown) out += name;
      continue;
    }
    if (c === "{" || c === "}") {
      i += 1; // grouping is not content
      continue;
    }
    if (c === "$") {
      i += 1;
      continue;
    }
    out += c;
    i += 1;
  }
  return out.replace(/\s+/g, " ").trim();
}


// ── mathematics as readable text (the plain-text citation form) ──────────
//
// The transliterator used to drop an operator and concatenate its arguments,
// so `\frac{1}{2}` became "12", `\binom{n}{2}` became "n2" and `\log_2 n`
// became "_2 n" (audit r2). Operators that take arguments now have structured
// forms, and anything NOT in this table makes the whole span fall back to its
// verbatim TeX — a citation that shows `\(\foo{a}{b}\)` is honest; one that
// shows "ab" is wrong.

/** Exact Unicode superscripts. Absent a full set, the `^` marker is kept. */
const SUPERSCRIPT: Record<string, string> = {
  "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴",
  "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹",
  "+": "⁺", "-": "⁻", "−": "⁻", "=": "⁼",
  "(": "⁽", ")": "⁾", n: "ⁿ", i: "ⁱ",
};

const toSuperscript = (s: string): string | null => {
  let out = "";
  for (const c of s) {
    const up = SUPERSCRIPT[c];
    if (!up) return null;
    out += up;
  }
  return out || null;
};

/**
 * The first `needle` at or after `from` that is not escaped by a backslash.
 * −1 when there is none.
 *
 * `Cost $5 versus \$10` has ONE math delimiter, not two: an escape-blind scan
 * closed a span on the currency sign and swallowed the prose between them
 * (audit r3). Shared by the plain-citation scanner, the review-prose scanner
 * and the BibTeX title tokeniser.
 */
export function indexOfUnescaped(s: string, needle: string, from: number): number {
  for (let i = from; i <= s.length - needle.length; i++) {
    if (s[i] === "\\") {
      i += 1; // whatever follows a backslash is escaped, the closer included
      continue;
    }
    if (s.startsWith(needle, i)) return i;
  }
  return -1;
}

/** A bare identifier or number needs no parentheses around it. */
const isAtom = (s: string): boolean => /^[\w.]+$/.test(s.trim());
const paren = (s: string): string => (isAtom(s) ? s.trim() : `(${s.trim()})`);

/** Thrown internally when a span cannot be rendered faithfully. */
const UNRENDERABLE = Symbol("unrenderable");

/**
 * Braces the referee actually wrote (`\{`, `\}`) versus braces that are TeX
 * grouping. Only the first kind is content, and it has to survive the final
 * brace strip in `texLineToPlain`, so it travels as a placeholder.
 */
export const LITERAL_BRACE_OPEN = "\ue004";
export const LITERAL_BRACE_CLOSE = "\ue005";

/**
 * What the last thing rendered was, which decides whether a script may attach
 * to it.
 *
 *   atom   a single letter, digit or symbol (`x`, `2`, `σ`), possibly already
 *          carrying a script (`β_0`) — a script attaches with no parentheses
 *   group  a brace group or an operator's result (`1/2`, `√(n)`) — a script
 *          attaches WITH parentheses
 *   other  anything else: a closing `|`, a literal `}`, a bracket, a big
 *          operator, punctuation. A script here is not something this can
 *          read, so the whole span falls back to verbatim TeX.
 *
 * The previous version tried to infer the base from the rendered string and
 * got `\sigma^2` → "(σ)²" and `|N_i|^2` → "|N_i(|)²" (audit r4). Tracking what
 * was just emitted is both simpler and right.
 */
type BaseKind = "atom" | "group" | "other";

/**
 * Named functions. `\log_2 n` reads "log_2 n": the name IS the symbol the
 * script attaches to, so it counts as an atom even though it is several
 * letters long. Operators that take LIMITS are in BIG_OPERATORS instead.
 */
const FUNCTION_NAMES = new Set([
  "log", "ln", "lg", "exp", "sin", "cos", "tan", "sec", "csc", "cot",
  "arcsin", "arccos", "arctan", "sinh", "cosh", "tanh", "det", "deg", "dim",
  "gcd", "hom", "ker", "Pr", "mod", "bmod", "tr", "rank",
]);

/** Big operators carry limits, which this does not attempt to place. */
const BIG_OPERATORS = new Set([
  "sum", "prod", "coprod", "int", "iint", "iiint", "oint", "bigcup", "bigcap",
  "bigoplus", "bigotimes", "bigvee", "bigwedge", "bigsqcup", "lim", "limsup",
  "liminf", "max", "min", "sup", "inf", "argmax", "argmin",
]);

/**
 * One math span as readable text, or null when it cannot be done faithfully.
 * Null is the caller's signal to print the span's TeX verbatim instead.
 */
export function mathToText(tex: string): string | null {
  try {
    return mathBody(tex, 0);
  } catch (e) {
    if (e === UNRENDERABLE) return null;
    throw e;
  }
}

function mathBody(src: string, depth: number): string {
  if (depth > MAX_DEPTH) throw UNRENDERABLE;
  let out = "";
  let i = 0;
  let base: BaseKind = "other";
  let baseStart = 0;
  const emit = (text: string, kind: BaseKind) => {
    baseStart = out.length;
    base = kind;
    out += text;
  };
  const group = (): string => {
    const at = skipTexSpace(src, i);
    const g = readGroup(src, at);
    if (!g) throw UNRENDERABLE;
    i = g.end;
    return mathBody(g.body, depth + 1);
  };
  const optional = (): string | null => {
    const o = src[i] === "[" ? readOptional(src, i) : null;
    if (!o) return null;
    i = o.end;
    return mathBody(o.body, depth + 1);
  };

  while (i < src.length) {
    const c = src[i];

    if (c === "\\") {
      // `\{` and `\}` are braces the author wrote: content, not grouping.
      if (src[i + 1] === "{" || src[i + 1] === "}") {
        emit(src[i + 1] === "{" ? LITERAL_BRACE_OPEN : LITERAL_BRACE_CLOSE, "other");
        i += 2;
        continue;
      }
      const escLit = /^\\([%&_#$ ])/.exec(src.slice(i));
      if (escLit) {
        emit(escLit[1], "other");
        i += escLit[0].length;
        continue;
      }
      if ("()[]".includes(src[i + 1] ?? "")) {
        i += 2;
        continue;
      }
      const m = /^\\([a-zA-Z@]+)/.exec(src.slice(i));
      if (!m) throw UNRENDERABLE;
      const name = m[1];
      i += m[0].length;
      const takesArg = src[skipTexSpace(src, i)] === "{";

      if (name === "frac" || name === "dfrac" || name === "tfrac") {
        const a2 = group();
        const b2 = group();
        emit(`${paren(a2)}/${paren(b2)}`, "group");
        continue;
      }
      if (name === "binom" || name === "choose") {
        const n = group();
        const k = group();
        emit(`C(${n.trim()}, ${k.trim()})`, "group");
        continue;
      }
      if (name === "sqrt") {
        const index = optional();
        const body2 = group();
        if (index === null) {
          emit(`\u221a(${body2.trim()})`, "group");
          continue;
        }
        const up = toSuperscript(index.trim());
        if (!up) throw UNRENDERABLE; // no exact index: show the source instead
        emit(`${up}\u221a(${body2.trim()})`, "group");
        continue;
      }
      if (name === "operatorname" || name === "mathrm" || name === "text" || name === "textrm") {
        emit(group(), "group");
        continue;
      }
      if (FUNCTION_NAMES.has(name)) {
        emit(name, "atom");
        continue;
      }
      if (BIG_OPERATORS.has(name)) {
        // Limits belong under and over it; this cannot place them.
        emit(GLYPH[name] ?? name, "other");
        continue;
      }
      const glyph = GLYPH[name];
      if (glyph !== undefined && !takesArg) {
        // A Greek letter or relation IS a symbol: `\sigma^2` reads "σ²".
        emit(glyph, /^[\p{L}\p{N}]$/u.test(glyph) ? "atom" : "other");
        continue;
      }
      if (TRANSPARENT.has(name)) {
        if (takesArg) emit(group(), "group");
        continue;
      }
      throw UNRENDERABLE; // an operator this does not understand
    }

    if (c === "^" || c === "_") {
      if (base === "other") throw UNRENDERABLE; // not a base this can read
      i += 1;
      let script: string;
      if (src[i] === "{") script = group();
      else if (src[i] === "\\") {
        const m = /^\\([a-zA-Z@]+)/.exec(src.slice(i));
        if (!m) throw UNRENDERABLE;
        i += m[0].length;
        script = GLYPH[m[1]] ?? m[1];
      } else {
        script = src[i] ?? "";
        i += 1;
      }
      if (base === "group") {
        // `{x+y}^2` → "(x+y)²": the grouping is what the script applies to.
        out = `${out.slice(0, baseStart)}(${out.slice(baseStart).trim()})`;
      }
      const up = c === "^" ? toSuperscript(script.trim()) : null;
      out += up ?? `${c}${paren(script)}`;
      base = "atom"; // a scripted base is itself a base: β_0² is fine
      continue;
    }

    if (c === "{") {
      const g = readGroup(src, i);
      if (!g) throw UNRENDERABLE;
      const body2 = mathBody(g.body, depth + 1);
      // `{}` is TeX's EMPTY group — a separator that keeps two tokens apart,
      // not a thing a script attaches to. Making it the base turned `T{}^2`
      // into "T()²"; leaving the base alone keeps it "T²".
      if (body2) emit(body2, "group");
      i = g.end;
      continue;
    }
    if (c === "}") {
      i += 1;
      continue;
    }
    // A lone letter, digit or Greek symbol is an atom; punctuation is not.
    emit(c, /^[\p{L}\p{N}]$/u.test(c) ? "atom" : "other");
    i += 1;
  }
  return out;
}

/**
 * A TeX-bearing one-liner (a paper title) as readable plain text.
 *
 * Each math span is converted through `mathToText`; when that cannot be done
 * faithfully the span is printed as its own TeX, delimiters included, because
 * a citation showing `\(\foo{a}{b}\)` is honest and one showing "ab" is not.
 * Prose outside the spans keeps its words and loses its markup.
 */
export function texLineToPlain(src: string, typography: (s: string) => string = (s) => s): string {
  // Verbatim spans are collected separately: the tidy-up below strips grouping
  // braces, and a span printed AS SOURCE must keep its own.
  const verbatim: string[] = [];
  const keep = (tex: string) => {
    verbatim.push(tex);
    return `${VERBATIM_OPEN}${verbatim.length - 1}${VERBATIM_CLOSE}`;
  };
  let out = "";
  let i = 0;
  while (i < src.length) {
    const opened = openDelimiter(src, i);
    if (opened) {
      const { open, close } = opened;
      // `$` closers may be escaped; `\)` and `\]` ARE backslash sequences.
      const at = close.startsWith("$")
        ? indexOfUnescaped(src, close, i + open.length)
        : src.indexOf(close, i + open.length);
      if (at >= 0) {
        const body = src.slice(i + open.length, at);
        const whole = src.slice(i, at + close.length);
        const done = mathToText(body);
        out += done ?? keep(whole);
        i = at + close.length;
        continue;
      }
    }
    if (src[i] === "\\") {
      // An accent is a letter, not a command.
      const acc = accentedLetter(src, i);
      if (acc) {
        out += acc.text;
        i = acc.end;
        continue;
      }
      const m = /^\\([a-zA-Z@]+)/.exec(src.slice(i));
      if (m) {
        const name = m[1];
        const first = readArgs(src, i + m[0].length, 1);
        // A text wrapper hands over its words.
        if (first && TEXT_LIKE.has(name)) {
          out += texLineToPlain(readGroup(src, first.starts[0])!.body, typography);
          i = first.end;
          continue;
        }
        // Anything else with arguments is an operator this cannot read, so ALL
        // of its source stands: `\frac{1}{2}` kept only `{1}` before (audit r3).
        const all = readArgs(src, i + m[0].length, Infinity);
        if (all) {
          out += keep(src.slice(i, all.end));
          i = all.end;
          continue;
        }
        // No complete argument. If a brace FOLLOWS, the macro is malformed and
        // its source is preserved verbatim rather than silently dropped.
        const after = skipTexSpace(src, i + m[0].length);
        if (src[after] === "{") {
          out += keep(src.slice(i));
          i = src.length;
          continue;
        }
        const glyph = GLYPH[name];
        out += glyph ?? "";
        i = i + m[0].length;
        continue;
      }
      const lit = /^\\([%&_#${} ])/.exec(src.slice(i));
      if (lit) {
        out += lit[1];
        i += lit[0].length;
        continue;
      }
      i += 1;
      continue;
    }
    out += src[i];
    i += 1;
  }
  const literalBraces = (t: string) =>
    t.split(LITERAL_BRACE_OPEN).join("{").split(LITERAL_BRACE_CLOSE).join("}");
  return literalBraces(
    typography(out.replace(/[{}]/g, "").replace(/\s+/g, " ").trim()),
  ).replace(
      new RegExp(`${VERBATIM_OPEN}(\\d+)${VERBATIM_CLOSE}`, "g"),
      (_m, n: string) => verbatim[Number(n)],
    );
}

// Private-use placeholders, absent from any title, so a verbatim span can pass
// through the brace/whitespace tidy-up untouched.
const VERBATIM_OPEN = "\ue002";
const VERBATIM_CLOSE = "\ue003";

/**
 * TeX accents → the Unicode letter, for plain text. BibTeX keeps the accent
 * macro verbatim instead; only the reading form resolves it (audit r4).
 */
const ACCENTS: Record<string, string> = {
  '"a': "\u00e4", '"o': "\u00f6", '"u': "\u00fc", '"A': "\u00c4", '"O': "\u00d6", '"U': "\u00dc",
  '"e': "\u00eb", '"i': "\u00ef", '"y': "\u00ff",
  "'a": "\u00e1", "'e": "\u00e9", "'i": "\u00ed", "'o": "\u00f3", "'u": "\u00fa", "'y": "\u00fd",
  "'A": "\u00c1", "'E": "\u00c9", "'I": "\u00cd", "'O": "\u00d3", "'U": "\u00da", "'c": "\u0107",
  "`a": "\u00e0", "`e": "\u00e8", "`i": "\u00ec", "`o": "\u00f2", "`u": "\u00f9",
  "`A": "\u00c0", "`E": "\u00c8", "`O": "\u00d2",
  "^a": "\u00e2", "^e": "\u00ea", "^i": "\u00ee", "^o": "\u00f4", "^u": "\u00fb",
  "~n": "\u00f1", "~a": "\u00e3", "~o": "\u00f5", "~N": "\u00d1",
  "=a": "\u0101", "=e": "\u0113", "=o": "\u014d", "=u": "\u016b",
  ".z": "\u017c", ".e": "\u0117",
  "cc": "\u00e7", "cC": "\u00c7", "cs": "\u015f",
  "vs": "\u0161", "vc": "\u010d", "vz": "\u017e", "vS": "\u0160", "vC": "\u010c", "vZ": "\u017d",
  "ua": "\u0103", "ug": "\u011f", "Ho": "\u0151", "Hu": "\u0171",
  "ra": "\u00e5", "rA": "\u00c5", "ka": "\u0105", "ke": "\u0119", "lL": "\u0141",
};

/** `\"o` / `\"{o}` / `\c{c}` → the accented letter, or null. */
export function accentedLetter(src: string, i: number): { text: string; end: number } | null {
  const m = /^\\([`'^"~=.]|[uvHcdbkrt])\s*(?:\{([A-Za-z])\}|([A-Za-z]))/.exec(src.slice(i));
  if (!m) return null;
  const letter = m[2] ?? m[3];
  const mapped = ACCENTS[`${m[1]}${letter}`];
  return mapped ? { text: mapped, end: i + m[0].length } : null;
}

/** TeX allows whitespace between a macro and its arguments. */
function skipTexSpace(s: string, i: number): number {
  let j = i;
  while (j < s.length && (s[j] === " " || s[j] === "\t" || s[j] === "\n")) j++;
  return j;
}

/**
 * Reads up to `max` contiguous balanced `{…}` arguments, TeX whitespace
 * allowed between them. Null when there is not even one.
 */
function readArgs(
  s: string,
  from: number,
  max: number,
): { starts: number[]; end: number } | null {
  const starts: number[] = [];
  let j = from;
  while (starts.length < max) {
    const at = skipTexSpace(s, j);
    if (s[at] !== "{") break;
    const g = readGroup(s, at);
    if (!g) break;
    starts.push(at);
    j = g.end;
  }
  return starts.length ? { starts, end: j } : null;
}

/** Wrappers whose argument is prose to be kept. */
const TEXT_LIKE = new Set([
  "text", "textrm", "textnormal", "textit", "textbf", "textsc", "textsl",
  "texttt", "emph", "mbox", "mathrm", "operatorname",
]);

/** The math delimiter opening at `i`, if any. */
function openDelimiter(s: string, i: number): { open: string; close: string } | null {
  if (s.startsWith("\\(", i)) return { open: "\\(", close: "\\)" };
  if (s.startsWith("\\[", i)) return { open: "\\[", close: "\\]" };
  if (s.startsWith("$$", i)) return { open: "$$", close: "$$" };
  if (s[i] === "$") return { open: "$", close: "$" };
  return null;
}

// ── math ─────────────────────────────────────────────────────────────────

/**
 * KaTeX's own error rendering. `throwOnError` covers a PARSE failure, but a
 * command KaTeX knows and refuses — an untrusted `\href`, an unsupported HTML
 * extension — is drawn in this colour with its arguments dropped and no throw,
 * so `\href{…}{click}` published a red "\href" where the label should have
 * been (audit r2). Output carrying it is not a rendering, it is a corruption.
 */
const KATEX_FAILED = /katex-error|#cc0000/;

/**
 * KaTeX, or the source shown as source. Never throws.
 *
 * FAIL CLOSED: when a formula cannot be rendered faithfully the reader is
 * shown its TeX, escaped, in a `<code>` span. That is honest — "this is
 * notation the renderer could not draw" — where a transliteration would read
 * as different content.
 */
function renderMath(tex: string, display: boolean): string {
  const body = tex.trim();
  if (!body) return "";
  const asSource = () => `<code class="rv-tex">${esc(body)}</code>`;
  try {
    const html = katex.renderToString(body, { ...katexOptions(display, true), strict: false });
    return KATEX_FAILED.test(html) ? asSource() : html;
  } catch {
    return asSource();
  }
}

// ── prose ────────────────────────────────────────────────────────────────

/**
 * Plain prose between the structured pieces.
 *
 * The typographic conversions run on the RAW text and the HTML escaping after:
 * escaping turns `'` into an entity, so `''` would never match a quote rule
 * once escaping had run.
 *
 * Braces are KEPT. Every brace that is TeX grouping has already been consumed
 * by the scanner as part of a macro's argument, so a brace arriving here is one
 * the referee typed as content — set-builder notation, "{-1,1}-valued" —
 * and deleting it would corrupt the sentence.
 */
function prose(s: string, stripGroups = false): string {
  const t = stripGroups ? s.replace(/[{}]/g, "") : s;
  // Dashes and ties go through the shared, code/URL/identifier-aware pass:
  // `https://x--y.test/a_b~c` is a URL, not typography (audit r2).
  return esc(texTypography(t.replace(/``/g, "\u201c").replace(/''/g, "\u201d")));
}

// ── the scanner ──────────────────────────────────────────────────────────

/** Reads a balanced `{…}` starting at `i` (which must point at `{`). */
function readGroup(src: string, i: number): { body: string; end: number } | null {
  if (src[i] !== "{") return null;
  let depth = 0;
  for (let j = i; j < src.length; j++) {
    if (src[j] === "\\") {
      j++;
      continue;
    }
    if (src[j] === "{") depth++;
    else if (src[j] === "}") {
      depth--;
      if (depth === 0) return { body: src.slice(i + 1, j), end: j + 1 };
    }
  }
  return null; // unbalanced: the caller treats the brace as stray prose
}

/** Reads a `[…]` optional argument starting at `i`, if there is one. */
function readOptional(src: string, i: number): { body: string; end: number } | null {
  if (src[i] !== "[") return null;
  const close = src.indexOf("]", i + 1);
  return close < 0 ? null : { body: src.slice(i + 1, close), end: close + 1 };
}

const URL_MACROS = /^\\(href|url)\b/;
// `\label{…}` is deliberately NOT here. It DECLARES a name where the others
// USE one, so resolving it puts a number ("Theorem 3") where the referee asked
// for a declaration — "add \label{thm:a} to the statement" became "add Theorem
// 3 to the statement", which is advice the referee never gave. A declaration
// has no reader-facing text at all, so it takes the fail-closed path and is
// shown as its own escaped source.
const REF_MACROS = /^\\(ref|cref|Cref|eqref|autoref|labelcref|vref|leanref)\b/;
const CITE_MACROS = /^\\(cite|citet|citep|citeauthor|citeyear|citealt|citealp|citenum|textcite|parencite)\b/;
const TEXT_MACROS: Record<string, "code" | "em" | "strong" | "plain" | "math"> = {
  texttt: "code", verb: "code",
  emph: "em", textit: "em", textsl: "em",
  textbf: "strong", textsc: "strong",
  text: "plain", textrm: "plain", textnormal: "plain", mbox: "plain",
  ensuremath: "math",
};

/**
 * Consumes a run of math starting at a macro: the macro and its arguments,
 * scripts, adjacent alphanumerics, and further macros separated by one space.
 *
 * The run stops at ordinary prose. `\mathcal G_n and its` takes `\mathcal G_n`
 * and leaves ` and its` — a single letter after one space belongs to the
 * formula (`\mathcal G`), a word does not.
 */
function readMathRun(src: string, start: number, openDepth = 0): number {
  let i = start;
  let first = true;
  let depth = openDepth;
  for (;;) {
    if (src[i] === "\\" && /[a-zA-Z@]/.test(src[i + 1] ?? "")) {
      // A structural macro is NOT mathematics. Swallowing `\cref{…}` into the
      // run made KaTeX reject the whole formula and print "crefobj:ass:…" at
      // the reader (audit, 2026-09-21).
      const rest = src.slice(i);
      const name = /^\\([a-zA-Z@]+)/.exec(rest)![1];
      if (
        !first &&
        (REF_MACROS.test(rest) || CITE_MACROS.test(rest) || URL_MACROS.test(rest) || name in TEXT_MACROS)
      ) {
        break;
      }
      i += 1;
      while (i < src.length && /[a-zA-Z@]/.test(src[i])) i++;
    } else if (src[i] === "\\" && (src[i + 1] === "{" || src[i + 1] === "}")) {
      // `\{ … \}` is a set: track its depth rather than swallowing the group
      // whole, so a `\cref` inside it still ends the run instead of being
      // handed to KaTeX and printed as "crefobj:…" (audit, 2026-09-21).
      depth += src[i + 1] === "{" ? 1 : -1;
      i += 2;
    } else if (src[i] === "\\" && /[|,;:!\\ ]/.test(src[i + 1] ?? "")) {
      i += 2; // `\,` `\|` `\;` — spacing and delimiters, still math
    } else if (!first && /[(),.+\-*/=<>|']/.test(src[i] ?? "")) {
      i += 1; // math punctuation sitting against the formula
    } else if (src[i] === "}" && depth > 0) {
      depth--;
      i += 1;
    } else if (src[i] === "{") {
      const g = readGroup(src, i);
      if (!g) {
        depth++; // unbalanced here, but the head may close it
        i += 1;
      } else i = g.end;
    } else if (depth > 0 && src[i] !== undefined) {
      // Inside a group opened before the macro, every character belongs to the
      // formula — `R_{n,\ell_1}` must not stop at the closing brace's contents.
      i += 1;
    } else if (src[i] === "[") {
      const o = readOptional(src, i);
      if (!o) break;
      i = o.end;
    } else if (src[i] === "^" || src[i] === "_") {
      i += 1;
      if (src[i] === "{") {
        const g = readGroup(src, i);
        if (!g) break;
        i = g.end;
      } else if (src[i] === "\\") {
        i += 1;
        while (i < src.length && /[a-zA-Z@]/.test(src[i])) i++;
      } else if (i < src.length) i += 1;
    } else if (!first && /[A-Za-z0-9]/.test(src[i] ?? "")) {
      while (i < src.length && /[A-Za-z0-9]/.test(src[i])) i++;
    } else if (
      src[i] === " " &&
      // one space, then either another macro or a lone symbol letter
      (/^\\[a-zA-Z@]/.test(src.slice(i + 1, i + 3)) ||
        /^[A-Za-z](?![A-Za-z])/.test(src.slice(i + 1, i + 3)))
    ) {
      i += 1;
      continue; // the next iteration consumes what follows the space
    } else break;
    first = false;
  }
  return i;
}

/**
 * How far BACK the formula already started, in characters, when a macro is
 * reached mid-expression.
 *
 * `the chain R_{n,\ell_1}^\star \le …` reaches `\ell` with `R_{n,` already
 * banked as prose. Rendering from the macro alone published `R_{n,` as text
 * and the rest as math — a formula torn in half (audit, 2026-09-21).
 *
 * Only a token that is ALREADY formula-shaped is reclaimed: it must carry a
 * `_`, `^`, `{` or `\`. "AsympSeq/" carries none, so `(AsympSeq/\asymp)` keeps
 * its word as words.
 */
/** `{` minus `}`, counting `\{`/`\}` too — KaTeX needs both kinds matched.
 *  Zero means the string is at least brace-parsable. */
function braceBalance(s: string): number {
  let d = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === "\\") {
      if (s[i + 1] === "{") d++;
      else if (s[i + 1] === "}") d--;
      i++;
      continue;
    }
    if (s[i] === "{") d++;
    else if (s[i] === "}") d--;
  }
  return d;
}

function mathRunBack(before: string): number {
  let s = before.length;
  while (s > 0 && !/\s/.test(before[s - 1])) s--;
  const token = before.slice(s);
  if (!token || !/[_^{\\]/.test(token)) return 0;
  return token.length;
}

/**
 * The serialised form of a URL we are willing to LINK, or null.
 *
 * A prefix test is not validation: `https://trusted.test\n@evil.test/` starts
 * with `https://` and resolves to evil.test (audit r3). So the string is
 * rejected outright if it carries whitespace or a control character, then
 * PARSED, then required to be http(s), and what is emitted is the parser's own
 * serialisation — never the raw text.
 */
function httpUrl(raw: string): string | null {
  const s = raw.trim();
  // eslint-disable-next-line no-control-regex
  if (!s || /[\s\u0000-\u001f\u007f]/.test(s)) return null;
  try {
    const u = new URL(s);
    return u.protocol === "http:" || u.protocol === "https:" ? u.href : null;
  } catch {
    return null;
  }
}

/** Deeper than any real referee sentence; shallow enough to never overflow. */
const MAX_DEPTH = 64;

/** The words a paper uses to name the thing a cross-reference points at. */
const KIND_WORDS = new Set([
  "theorem", "proposition", "lemma", "corollary", "definition", "assumption",
  "section", "subsection", "appendix", "equation", "remark", "example",
  "figure", "table", "algorithm", "claim", "setup", "condition", "chapter",
  "part", "step", "property", "fact", "note",
]);

/**
 * Is position `i` inside a quotation?
 *
 * A cross-reference the referee put in quotes is the referee QUOTING the
 * manuscript's source — "the sentence \"Theorem~\ref{…}\" should read" — so
 * resolving it silently rewrites the quotation into something the paper does
 * not say (audit r4). Straight quotes are paired only when the field really
 * holds a pair; curly and TeX quotes are matched by their last opener.
 */
function insideQuotes(src: string, i: number): boolean {
  const before = src.slice(0, i);
  // A straight `"` opens a quotation only if the SAME field closes it. A lone
  // one is an inch mark, a prime or a second \u2014 `The 5" margin \u2026 \ref{a}` \u2014
  // and counting it as an opener silently swallowed every reference in the
  // rest of the field (audit r5).
  let open = -1;
  for (let k = 0; k < before.length; k++) {
    if (before[k] === "\\") {
      k += 1;
      continue;
    }
    if (before[k] !== '"') continue;
    if (open >= 0) open = -1; // this one closes the quotation
    else if (nextStraightQuote(src, k + 1) >= 0) open = k;
  }
  if (open >= 0) return true;
  const open2 = Math.max(before.lastIndexOf("\u201c"), before.lastIndexOf("``"));
  if (open2 < 0) return false;
  const close = Math.max(before.lastIndexOf("\u201d"), before.lastIndexOf("''"));
  return close < open2;
}

/** The next unescaped straight quote at or after `from`, or -1. */
function nextStraightQuote(src: string, from: number): number {
  for (let k = from; k < src.length; k++) {
    if (src[k] === "\\") {
      k += 1;
      continue;
    }
    if (src[k] === '"') return k;
  }
  return -1;
}

/** "Theorems" → "theorem", "Corollaries" → "corollary", "Appendices" → "appendix". */
function singularKind(word: string): string {
  const w = word.toLowerCase();
  if (w.endsWith("ies")) return `${w.slice(0, -3)}y`;
  if (w.endsWith("ices")) return `${w.slice(0, -4)}ix`;
  if (w.endsWith("s") && !w.endsWith("ss")) return w.slice(0, -1);
  return w;
}

/** The words that carry a coordinated list of references from one to the next. */
const LIST_WORDS = new Set(["and", "or", "to", "through"]);

/**
 * The kind word that GOVERNS a cross-reference appearing at the end of
 * `preceding`, or null when the sentence has not named a kind.
 *
 * One kind word governs a whole list: "See Theorems~\ref{a} and \ref{b}" says
 * "theorem" once and means it for both, so the scan walks back over the
 * numbers already emitted and the connectors between them ("and", ",", "or",
 * an en dash, "to", "through") before it looks the word up. Plurals are
 * singularised first, or "Theorems" would miss and the reader would get
 * "Theorems Theorem 3 and Theorem 4".
 */
function governingKind(preceding: string): string | null {
  let s = preceding;
  for (let guard = 0; guard < 32; guard += 1) {
    const t = s.replace(/[~\s,;:–—-]+$/u, "");
    const word = /[A-Za-z]+$/.exec(t)?.[0];
    if (word) {
      const kind = singularKind(word);
      if (KIND_WORDS.has(kind)) return kind;
      if (!LIST_WORDS.has(word.toLowerCase())) return null;
      s = t.slice(0, t.length - word.length);
      continue;
    }
    // Not a word: a number this rendering already emitted ("Theorems 3 and ").
    const num = /[\w.]*\d[\w.]*$/.exec(t)?.[0];
    if (!num) return null;
    s = t.slice(0, t.length - num.length);
  }
  return null;
}

/**
 * A resolved label with the kind word the sentence has already said removed.
 *
 * "Theorem~\ref{thm:x}" resolves to "Theorem 3", and printing that whole label
 * gives "Theorem Theorem 3". Worse, a paper that labels a theorem with a
 * section-style name gives "Section Theorem 3", which asserts something false.
 * So when the sentence already names a kind, only the number is emitted —
 * whether or not the two kinds agree.
 */
function refNumber(label: string): string {
  const parts = /^([A-Za-z]+)\s+(.+)$/.exec(label.trim());
  return parts ? parts[2] : label;
}

/**
 * Is the text written since the previous cross-reference nothing but the
 * punctuation that continues a list? Then that reference's governing word
 * still governs this one.
 */
function continuesList(buf: string, end: number): boolean {
  if (end < 0 || end > buf.length) return false;
  return /^[\s~]*(?:[,;][\s~]*)?(?:and|or|to|through|[–—-])?[\s~]*$/i.test(
    buf.slice(end),
  );
}

/** Joins resolved cross-reference labels the way a sentence would. */
function joinLabels(parts: string[]): string {
  if (parts.length <= 1) return parts[0] ?? "";
  if (parts.length === 2) return `${parts[0]} and ${parts[1]}`;
  return `${parts.slice(0, -1).join(", ")} and ${parts[parts.length - 1]}`;
}

/**
 * Renders one referee string to HTML.
 *
 * @param labels obj_id → paper label ("Theorem 3"), from the bundle crosswalk,
 *   so a cross-reference resolves to the number the reader sees in the paper.
 */
export function renderReviewText(
  src: string,
  labels: Record<string, string> = {},
  /** True while rendering a macro's ARGUMENT, where a brace is grouping rather
   *  than the set-builder notation it is out in the open. */
  inArgument = false,
  /** Recursion guard — see MAX_DEPTH. */
  depth = 0,
): string {
  if (!src) return "";
  // 5,000 nested `\emph{` overflowed the build process's stack, which broke
  // the one promise this module makes (audit r2). Past a depth no real prose
  // reaches, the remaining source is shown as source.
  if (depth > MAX_DEPTH) return `<code class="rv-tex">${esc(src)}</code>`;
  const out: string[] = [];
  let buf = "";
  const flush = () => {
    if (buf) {
      out.push(prose(buf, inArgument));
      buf = "";
    }
  };
  const label = (raw: string): string => {
    const id = raw.trim();
    const bare = id.replace(/^obj:/, "");
    return labels[bare] ?? labels[id] ?? bare;
  };
  // A coordinated list of references — "Theorems 3 and 4" — is governed by the
  // one kind word the REFEREE wrote in front of it. `listEnd` is where the last
  // reference left off in `buf`, so a kind word this renderer itself inserted
  // ("Compare Theorem 3 and \ref{lem:x}") is never mistaken for the referee's.
  let listGoverned = false;
  let listEnd = -1;

  let i = 0;
  while (i < src.length) {
    const c = src[i];

    // `…` — a code span, which in this corpus is as often a formula as an
    // identifier. Math wins when KaTeX can parse it; otherwise it is code.
    // ``…'' is TeX's quotation, and it must be read before the code-span rule
    // or the pair would open and close an empty span and eat the quote.
    if (src.startsWith("``", i)) {
      buf += "\u201c";
      i += 2;
      continue;
    }
    if (c === "`") {
      const end = src.indexOf("`", i + 1);
      if (end > i) {
        const body = src.slice(i + 1, end);
        flush();
        out.push(
          /\\[a-zA-Z@]|[_^]/.test(body)
            ? renderMath(body, false)
            : `<code>${esc(body)}</code>`,
        );
        i = end + 1;
        continue;
      }
    }

    if (c === "$") {
      const display = src.startsWith("$$", i);
      // An ESCAPED dollar is a currency sign, not a closer (audit r3).
      const close = indexOfUnescaped(src, display ? "$$" : "$", i + (display ? 2 : 1));
      // …and `$5 and $6 each` is two prices, not one formula: a `$` against a
      // digit whose partner trails a space is currency on both ends (r4).
      // Unless the span is MATHEMATICS — `$1/n $`, `$0 < \epsilon < 1 $` — in
      // which case a macro or an operator inside it says so, and the price
      // rule must stand down or the formula is published as loose `$` (r5).
      const span = close > i ? src.slice(i + 1, close) : "";
      if (
        !display &&
        /\d/.test(src[i + 1] ?? "") &&
        close > i &&
        /\s/.test(src[close - 1] ?? "") &&
        !/\\[a-zA-Z]|[\^_=<>/]/.test(span)
      ) {
        buf += "$";
        i += 1;
        continue;
      }
      if (close > i) {
        flush();
        out.push(renderMath(src.slice(i + (display ? 2 : 1), close), display));
        i = close + (display ? 2 : 1);
        continue;
      }
      // An unmatched delimiter IS currency: "price is $5" must keep its $.
      buf += "$";
      i += 1;
      continue;
    }

    if (c === "\\") {
      const next = src[i + 1];
      if (next === "(" || next === "[") {
        const closer = next === "(" ? "\\)" : "\\]";
        const close = src.indexOf(closer, i + 2);
        if (close > i) {
          flush();
          out.push(renderMath(src.slice(i + 2, close), next === "["));
          i = close + 2;
          continue;
        }
      }
      // `\{` opens a math group (`\min\{1,d^2/n\}`); the other escapes are
      // literal characters.
      if (next && "%&_#$".includes(next)) {
        buf += next;
        i += 2;
        continue;
      }
      const rest = src.slice(i);
      const name = /^\\([a-zA-Z@]+)/.exec(rest)?.[1];
      if (!name) {
        // `\{ … \}` is a math group, not a literal brace — it is how the
        // referee writes a set. Everything else after a lone backslash is not
        // content at all.
        if (next === "{") {
          const end = readMathRun(src, i);
          if (end > i) {
            flush();
            out.push(renderMath(src.slice(i, end), false));
            i = end;
            continue;
          }
        }
        if (next === "}") {
          i += 2;
          continue;
        }
        i += 1;
        continue;
      }

      // `\href{url}{label}` / `\url{url}` — handled HERE, never handed to
      // KaTeX, which refuses an untrusted target and prints the command name
      // in red with the label dropped (audit r2). Only http(s) becomes a link;
      // every other scheme is text, so `javascript:` can never be a target.
      if (URL_MACROS.test(rest)) {
        const want = name === "url" ? 1 : 2;
        const args = readArgs(src, i + 1 + name.length, want);
        if (!args) {
          // Malformed: its own source, escaped, rather than brace syntax.
          flush();
          out.push(`<code class="rv-tex">${esc(src.slice(i, i + 1 + name.length))}</code>`);
          i += 1 + name.length;
          continue;
        }
        const bodies = args.starts.map((at) => readGroup(src, at)!.body);
        const target = bodies[0];
        const shown = name === "url" ? target.trim() : (bodies[1] ?? target);
        const safe = httpUrl(target);
        flush();
        out.push(
          safe
            ? `<a href="${esc(safe)}" rel="noopener nofollow">${renderReviewText(shown, labels, true, depth + 1)}</a>`
            : renderReviewText(shown, labels, true, depth + 1),
        );
        i = args.end;
        continue;
      }

      if (REF_MACROS.test(rest)) {
        // Inside quotation marks the referee is showing the manuscript's
        // SOURCE, so it is shown as source rather than resolved (audit r4).
        if (insideQuotes(src, i)) {
          const quoted = readArgs(src, i + 1 + name.length, 2);
          const end = quoted ? quoted.end : i + 1 + name.length;
          flush();
          out.push(`<code class="rv-tex">${esc(src.slice(i, end))}</code>`);
          i = end;
          continue;
        }
        let j = i + 1 + name.length;
        const groups: string[] = [];
        while (groups.length < 2) {
          while (src[j] === " " && groups.length === 0) j++;
          const g = readGroup(src, j);
          if (!g) break;
          groups.push(g.body);
          j = g.end;
        }
        if (groups.length === 0) {
          // "Maintain the current use of \cref and \Cref when revising" — the
          // referee is naming the command, so name it back rather than delete it.
          flush();
          out.push(`<code>${esc(name)}</code>`);
          i += 1 + name.length;
          continue;
        }
        // `\leanref{id}{display}` — the second argument IS the reader's text.
        if (groups.length === 2) {
          flush();
          out.push(renderReviewText(groups[1], labels, true, depth + 1));
        } else {
          const governed = continuesList(buf, listEnd)
            ? listGoverned
            : governingKind(buf) !== null;
          const resolved = groups[0]
            .split(",")
            .map(label)
            .filter(Boolean)
            .map((l) => (governed ? refNumber(l) : l));
          buf += joinLabels(resolved);
          listGoverned = governed;
          listEnd = buf.length;
        }
        i = j;
        continue;
      }

      if (CITE_MACROS.test(rest)) {
        let j = i + 1 + name.length;
        const opts: string[] = [];
        for (;;) {
          const o = readOptional(src, j);
          if (!o) break;
          opts.push(o.body);
          j = o.end;
        }
        const g = readGroup(src, j);
        if (!g) {
          i += 1 + name.length;
          continue;
        }
        const keys = g.body.split(",").map((k) => k.trim()).filter(Boolean).join(", ");
        const loc = opts.filter((o) => o.trim()).join(", ");
        buf += loc ? `${keys} (${loc})` : keys;
        i = g.end;
        continue;
      }

      const kind = TEXT_MACROS[name];
      if (kind) {
        const at = skipTexSpace(src, i + 1 + name.length);
        const g = readGroup(src, at);
        if (g) {
          if (kind === "math") {
            flush();
            out.push(renderMath(g.body, false));
          } else if (kind === "plain") {
            // Recursing keeps nested markup working inside \text{…}.
            flush();
            out.push(renderReviewText(g.body, labels, true, depth + 1));
          } else if (kind === "code") {
            // Code is literal: `\texttt{--help}` is a flag, not an en dash.
            flush();
            out.push(`<code>${esc(g.body)}</code>`);
          } else {
            flush();
            out.push(`<${kind}>${renderReviewText(g.body, labels, true, depth + 1)}</${kind}>`);
          }
          i = g.end;
          continue;
        }
        // No COMPLETE argument. If a brace follows, the macro is malformed and
        // its source is preserved rather than dropped along with its name
        // (audit r3); otherwise the bare command word is not content.
        flush();
        const end = src[at] === "{" ? at + 1 : i + 1 + name.length;
        out.push(`<code class="rv-tex">${esc(src.slice(i, end))}</code>`);
        i = end;
        continue;
      }

      // Anything else is mathematics that happens to be sitting in a sentence.
      // The formula may have started before the macro, in text already banked
      // as prose — take that part back so the whole expression renders as one.
      const back = mathRunBack(buf);
      let head = back > 0 ? buf.slice(buf.length - back) : "";
      // A `{` opened in the reclaimed head has to be closed by the forward run,
      // or KaTeX is handed `R_{n,\ell_1` and the whole formula degrades.
      const open = braceBalance(head);
      let end = readMathRun(src, i, Math.max(open, 0));
      if (braceBalance(head + src.slice(i, end)) !== 0) {
        head = ""; // reclaiming made it worse: render from the macro alone
        end = readMathRun(src, i);
        if (braceBalance(src.slice(i, end)) !== 0) {
          // Still unbalanced: never hand KaTeX a truncated group.
          flush();
          out.push(`<code class="rv-tex">${esc(src.slice(i, end))}</code>`);
          i = end;
          continue;
        }
      } else if (back > 0) buf = buf.slice(0, buf.length - back);
      flush();
      out.push(renderMath(head + src.slice(i, end), false));
      i = end;
      continue;
    }

    buf += c;
    i += 1;
  }
  flush();
  return out.join("");
}
