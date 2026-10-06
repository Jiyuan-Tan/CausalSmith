/**
 * Citation strings for a working paper — the ONE place BibTeX and the plain-text
 * form are built, so the Cite panel on the landing page, the Cite panel on the
 * paper page, and anything that follows cannot drift apart.
 *
 * Pure: no filesystem, no Astro, no KaTeX. Everything the citation needs is
 * passed in, including the site origin (which comes from Astro's configured
 * `site` — never a hardcoded domain, because the same tree is built for
 * causalsmith.org, a GitHub Pages project path, and local dev).
 *
 * Every identity field is OPTIONAL. A bundle with no working-paper number, no
 * version and no DOI still produces a correct citation; the missing pieces are
 * simply omitted (the site must keep working against bundles emitted before the
 * numbering/DOI pipeline existed).
 */

import { indexOfUnescaped, texLineToPlain } from "./reviewText.js";

/** The paper's citable identity, as carried by `meta.json`. */
export interface CitationMeta {
  /** Bundle id — the citation key's fallback when there is no WP number. */
  id: string;
  /** The title AS THE PAPER WRITES IT (`meta.title`), not the site's Title
   *  Case display form: a citation reproduces the PDF, and brace-protecting
   *  capitals the site added would bake a display convention into everyone's
   *  .bib file. May carry TeX math. */
  title: string;
  /** `CSWP-<year>-<NNN>`, once assigned; null/absent before that. */
  wpNumber?: string | null;
  /** ISO date of v1. Always present — it is the series' publication date. */
  created: string;
  /** Integer ≥ 1; absent on bundles that predate version tracking. */
  version?: number | null;
  /** ISO date of the current version (== `created` for v1). */
  revised?: string | null;
  /** `meta.authorship` — who the bundle says wrote the paper, when anyone did. Null/absent on
   *  every bundle that carries the series' default corporate author. */
  authorship?: string | null;
  /** Zenodo CONCEPT DOI — one per paper, arXiv-style. Never the version DOI
   *  (`meta.version_doi`): the version is carried by `vN`, exactly as arXiv
   *  does it, and between reserve and publish a version DOI does not resolve.
   *  Passed through `conceptDoi` before it is shown anywhere. */
  doi?: string | null;
  /** Lean verification pin, abbreviated to 7 in the note. */
  commit: string;
}

/** Where the paper lives and who publishes it. */
export interface CitationContext {
  /** `Astro.site` as a string (origin + optional path), or null in a build with
   *  no `site` configured — in which case the citation simply carries no URL. */
  site: string | null;
  /** `import.meta.env.BASE_URL` with the trailing slash removed. */
  base?: string;
  /** Who to cite. Defaults to the corporate author (the PDFs say "CausalSmith"); a bundle that
   *  records `meta.authorship` names a person, and {@link citationAuthor} is what resolves the
   *  two so the panel, the plain text and the Scholar tag cannot disagree. */
  author?: string;
  institution?: string;
}

export const DEFAULT_AUTHOR = "CausalSmith";
const DEFAULT_INSTITUTION = "CausalSmith Working Papers";

const MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];

/**
 * A real calendar date, or null.
 *
 * `meta.json` is data, not a promise: a field can be the wrong type or a
 * non-date like `2026-13-45`, and printing it raw put it in front of the
 * reader (audit r4). The parse is done on the STRING — never `new Date` on the
 * whole value, which would shift the day in a negative-offset timezone — and
 * the UTC round-trip is what rejects a day that does not exist.
 */
export function validDate(v: unknown): string | null {
  if (typeof v !== "string") return null;
  const m = /^(\d{4})-(\d{2})-(\d{2})(?:[T ]|$)/.exec(v.trim());
  if (!m) return null;
  const [y, mo, d] = [Number(m[1]), Number(m[2]), Number(m[3])];
  const utc = new Date(Date.UTC(y, mo - 1, d));
  if (utc.getUTCFullYear() !== y || utc.getUTCMonth() !== mo - 1 || utc.getUTCDate() !== d) {
    return null;
  }
  return `${m[1]}-${m[2]}-${m[3]}`;
}

/** A non-empty string, or null — anything else is treated as absent. */
export function validText(v: unknown): string | null {
  const t = typeof v === "string" ? v.trim() : "";
  return t ? t : null;
}

/** An integer version ≥ 1, or null. */
export function validVersion(v: unknown): number | null {
  return typeof v === "number" && Number.isInteger(v) && v >= 1 ? v : null;
}

/** `2026-08-27` → `27 Aug 2026`; anything that is not a real date → "". */
export function formatDate(iso: string | null | undefined): string {
  const ok = validDate(iso);
  if (!ok) return "";
  const m = /^(\d{4})-(\d{2})-(\d{2})/.exec(ok)!;
  return `${Number(m[3])} ${MONTHS[Number(m[2]) - 1]} ${m[1]}`;
}

/** Four-digit year of an ISO date; empty when it is not one. */
export function yearOf(iso: string | null | undefined): string {
  return validDate(iso)?.slice(0, 4) ?? "";
}

/** BibTeX `month` value — the three-letter macro, unbraced (`month = jul`). */
function bibMonth(iso: string): string | null {
  const m = /^\d{4}-(\d{2})/.exec(validDate(iso) ?? "");
  const name = m ? MONTHS[Number(m[1]) - 1] : null;
  return name ? name.toLowerCase() : null;
}

/** The paper's canonical page, absolute, from Astro's configured `site`. */
export function paperUrl(meta: CitationMeta, ctx: CitationContext): string | null {
  if (!ctx.site) return null;
  const base = (ctx.base ?? "").replace(/\/+$/, "");
  try {
    return new URL(`${base}/papers/${meta.id}/`.replace(/^\/+/, "/"), ctx.site).href;
  } catch {
    return null;
  }
}

/**
 * A DOI the site is willing to PRINT, or null.
 *
 * Only a published Zenodo concept DOI qualifies: `10.5281/zenodo.<digits>`.
 * Everything else is treated as absent and silently omitted — in particular
 * the sandbox prefix `10.5072`, which a deposit run against Zenodo's sandbox
 * writes into `meta.json` and which resolves to nothing. Printing one would be
 * worse than printing none: a citation carrying a dead DOI is wrong in a way
 * the reader cannot see. A bad value is never a build failure, because the
 * bundle is otherwise a perfectly good paper.
 */
const CONCEPT_DOI = /^10\.5281\/zenodo\.\d+$/;

export function conceptDoi(doi: unknown): string | null {
  const text = validText(doi);
  if (!text) return null;
  const bare = text.replace(/^(?:https?:\/\/)?(?:dx\.)?doi\.org\//, "");
  return CONCEPT_DOI.test(bare) ? bare : null;
}

/** `https://doi.org/<doi>` — the resolver form every style guide wants. Null
 *  for anything `conceptDoi` rejects. */
export function doiUrl(doi: unknown): string | null {
  const bare = conceptDoi(doi);
  return bare ? `https://doi.org/${bare}` : null;
}

/** FNV-1a, so a capped key stays deterministic without a crypto import. */
function shortHash(s: string): string {
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 0x01000193) >>> 0;
  }
  return h.toString(36).padStart(7, "0").slice(0, 7);
}

/**
 * BibTeX entry key — PERMANENT, and derived only from the bundle id.
 *
 * A key is not decoration: it is what a reader types in `\cite{}` and what
 * their .bib file is keyed on. Deriving it from `wp_number` meant that the day
 * the numbering pipeline assigned one, every existing bibliography silently
 * broke (audit, 2026-09-21). The bundle id is immutable, so the key is too,
 * before and after the number and the DOI arrive.
 *
 * Long ids are capped deterministically: a 40-character prefix plus a hash of
 * the whole id, so two long ids can never collide.
 */
export function citationKey(meta: CitationMeta): string {
  const safe = meta.id.replace(/[^A-Za-z0-9_-]/g, "_");
  const body = safe.length <= 48 ? safe : `${safe.slice(0, 40)}_${shortHash(safe)}`;
  return `causalsmith_${body}`;
}

// ── title handling ───────────────────────────────────────────────────────
// Two problems, both real in this corpus: titles carry TeX math (`\(\epsilon\)`)
// which BibTeX wants in `$…$`, and they carry capitals a style file would
// silently lowercase ("Chebyshev", "POMDPs", "CR2"). Math spans are tokenized
// first so the capital-protection pass can never reach inside a formula.

/**
 * A BibTeX field value must always CLOSE. The earlier version escaped only
 * `&%#_` and left prose braces, dollars and backslashes alone, so a title
 * containing `M{alformed` produced a `title = {M{alformed}` field that never
 * closed and a `.bib` file the reader could not parse (audit, 2026-09-21).
 *
 * So the title is TOKENISED first — balanced math, then macros with their
 * arguments — and only the prose between tokens is escaped, exactly once. A
 * construct that is not balanced is not TeX the author meant; it is a literal
 * character, and it is escaped as one.
 */

/** Balanced `\(…\)`, `\[…\]`, `$…$`, `$$…$$` starting at `i`, or null. */
function readMathToken(s: string, i: number): { tex: string; end: number } | null {
  const pairs: [string, string, boolean][] = [
    ["\\(", "\\)", false],
    ["\\[", "\\]", true],
    ["$$", "$$", true],
    ["$", "$", false],
  ];
  for (const [open, close, display] of pairs) {
    if (!s.startsWith(open, i)) continue;
    const from = i + open.length;
    // A `$` closer must be UNESCAPED: in "Cost $5 versus \$10" the second
    // dollar is a currency sign, and an escape-blind indexOf closed the span
    // on it, leaving one unescaped delimiter in the field (audit r2). `\)` and
    // `\]` ARE backslash sequences, so they are matched literally.
    const at = close.startsWith("$") ? indexOfUnescaped(s, close, from) : s.indexOf(close, from);
    if (at < 0) continue; // unbalanced: not a math token at all
    const body = s.slice(from, at);
    if (!body.trim()) continue;
    const d = display ? "$$" : "$";
    return { tex: `${d}${body}${d}`, end: at + close.length };
  }
  return null;
}

/** A macro with its balanced arguments (`\emph{a {b} c}`), or null. */
function readMacroToken(s: string, i: number): { tex: string; end: number } | null {
  const m = /^\\([a-zA-Z@]+)/.exec(s.slice(i));
  if (!m) return null;
  let j = i + m[0].length;
  for (;;) {
    if (s[j] !== "{") break;
    let depth = 0;
    let k = j;
    for (; k < s.length; k++) {
      if (s[k] === "\\") {
        k++;
        continue;
      }
      if (s[k] === "{") depth++;
      else if (s[k] === "}") {
        depth--;
        if (depth === 0) break;
      }
    }
    if (depth !== 0) return null; // unbalanced argument: not a usable macro
    j = k + 1;
  }
  return { tex: s.slice(i, j), end: j };
}

/** One prose character, escaped exactly once so the field still closes. */
function escapeBibChar(c: string): string {
  return "&%#_{}$".includes(c) ? `\\${c}` : c;
}

/**
 * Brace-protects a word so a style file cannot recase it. Whole-word braces
 * (`{Chebyshev}`) rather than per-letter (`{C}hebyshev`): both work, this one
 * stays readable in the .bib file the reader copies. The FIRST word is left
 * alone — every style capitalizes a title's first word anyway, and bracing it
 * only adds noise.
 */
function protectWord(word: string, isFirst: boolean): string {
  const m = /^([(["'`]*)([\s\S]*?)([)\]"'`.,;:!?]*)$/.exec(word);
  if (!m) return word;
  const [, lead, core, trail] = m;
  if (!core) return word;
  const needs = isFirst ? /[A-Z]/.test(core.slice(1)) : /[A-Z]/.test(core);
  return needs ? `${lead}{${core}}${trail}` : word;
}

/**
 * A title ready for a BibTeX `title = {…}` field: always balanced, always
 * closing, with the author's capitals protected and their math preserved.
 */
export function bibtexTitle(title: string): string {
  type Part = { text: string; verbatim: boolean };
  const parts: Part[] = [];
  let prose = "";
  const flush = () => {
    if (prose) {
      parts.push({ text: prose, verbatim: false });
      prose = "";
    }
  };

  let i = 0;
  while (i < title.length) {
    const c = title[i];
    if (c === "\\" || c === "$") {
      const math = readMathToken(title, i);
      if (math) {
        flush();
        parts.push({ text: math.tex, verbatim: true });
        i = math.end;
        continue;
      }
      if (c === "\\") {
        // An ACCENT is TeX a .bib file must keep: `H{\"o}lder` survives a style
        // file, "Hölder" does not (audit r4). Braced so the case is protected.
        const accent = /^\\([`'^"~=.]|[uvHcdbkrt]\b)\s*(\{[^{}]*\}|[A-Za-z])/.exec(title.slice(i));
        if (accent) {
          flush();
          parts.push({ text: `{${accent[0]}}`, verbatim: true });
          i += accent[0].length;
          continue;
        }
        // An already-escaped special stays escaped — exactly once.
        if (title[i + 1] && "&%#_{}$\\".includes(title[i + 1])) {
          flush();
          parts.push({ text: `\\${title[i + 1]}`, verbatim: true });
          i += 2;
          continue;
        }
        const macro = readMacroToken(title, i);
        if (macro) {
          flush();
          parts.push({ text: macro.tex, verbatim: true });
          i = macro.end;
          continue;
        }
        i += 1; // a trailing or meaningless backslash would break the field
        continue;
      }
      // An unmatched `$` is a dollar sign, not the start of mathematics.
      prose += escapeBibChar("$");
      i += 1;
      continue;
    }
    prose += escapeBibChar(c);
    i += 1;
  }
  flush();

  // Capital protection runs per word, over the prose parts only, with the word
  // counter shared so "first word" means first word of the whole title.
  let word = 0;
  return parts
    .map((p) => (p.verbatim ? p.text : p.text.replace(/\S+/g, (w) => protectWord(w, word++ === 0))))
    .join("");
}

/**
 * Title as running prose (the Cite panel's plain-text tab, `<meta>` tags).
 *
 * Operators keep their meaning: `\frac{1}{2}` reads "1/2", not "12" (audit
 * r2). A span the converter cannot read faithfully is printed as its own TeX
 * rather than flattened into something that says something else.
 */
export function texToPlain(s: string): string {
  // Typography is applied to the PROSE only. A span kept as verbatim source
  // must keep its own `--` as well, or what is preserved is no longer the
  // source (audit r3) — `texLineToPlain` holds those spans aside for us.
  return texLineToPlain(s, (prose) =>
    prose.replace(/---/g, "—").replace(/--/g, "–"),
  );
}

// ── the two citation forms ───────────────────────────────────────────────

/**
 * Who the citation names.
 *
 * `meta.authorship` wins when the bundle records one — it is the paper's own statement of
 * authorship, and the PDF's byline already says it, so a citation that said "CausalSmith"
 * instead would credit the series for someone's work. An explicit `ctx.author` (a build-level
 * override) comes next, and the corporate default last.
 *
 * ONE function, used by BibTeX, the plain-text form and the Scholar `citation_author` tag, so
 * the three cannot name different authors for the same paper.
 */
export function citationAuthor(meta: CitationMeta, ctx: CitationContext = { site: null }): string {
  return validText(meta.authorship) ?? validText(ctx.author) ?? DEFAULT_AUTHOR;
}

/** The `note` field: version/revision when known, always the Lean pin. */
function noteOf(meta: CitationMeta): string {
  const bits: string[] = [];
  const version = validVersion(meta.version);
  const revised = validDate(meta.revised);
  const created = validDate(meta.created);
  // "revised" is a claim about history. A v1 paper has none, and its `revised`
  // field simply repeats `created`, so it reads as a date, not a revision.
  const reallyRevised = revised !== null && (version === null || version > 1) && revised !== created;
  if (version !== null) {
    bits.push(
      reallyRevised
        ? `Version ${version}, revised ${formatDate(revised)}.`
        : `Version ${version}${created || revised ? `, ${formatDate(revised ?? created)}` : ""}.`,
    );
  } else if (reallyRevised) {
    bits.push(`Revised ${formatDate(revised)}.`);
  }
  bits.push(
    `Machine-generated; formal statements verified in Lean 4 at commit ${meta.commit.slice(0, 7)}`,
  );
  return bits.join(" ");
}

/**
 * `@techreport` — the entry type for a numbered working paper. Fields are
 * emitted only when they exist, so an unnumbered, DOI-less bundle still yields
 * a valid entry (title/author/year/institution/url/note).
 */
export function bibtex(meta: CitationMeta, ctx: CitationContext): string {
  const rows: [string, string][] = [];
  rows.push(["title", `{${bibtexTitle(meta.title)}}`]);
  // DOUBLE braces mean "this is one indivisible name" — right for the corporate author, wrong
  // for a person: `{{Ada Lovelace}}` is a lab, and every style file that abbreviates or sorts
  // by surname would print "Lovelace, Ada" as "Ada Lovelace" and file it under A. So a human
  // name from `meta.authorship` gets SINGLE braces and is parsed as "First Last"; only the
  // corporate default stays double-braced.
  const author = citationAuthor(meta, ctx);
  rows.push(["author", author === DEFAULT_AUTHOR ? `{{${author}}}` : `{${author}}`]);
  const year = yearOf(meta.created);
  if (year) rows.push(["year", `{${year}}`]);
  const month = bibMonth(meta.created);
  if (month) rows.push(["month", month]);
  rows.push(["institution", `{${ctx.institution ?? DEFAULT_INSTITUTION}}`]);
  const number = validText(meta.wpNumber);
  if (number) rows.push(["number", `{${number}}`]);
  const doi = conceptDoi(meta.doi);
  if (doi) rows.push(["doi", `{${doi}}`]);
  const url = paperUrl(meta, ctx);
  if (url) rows.push(["url", `{${url}}`]);
  rows.push(["note", `{${noteOf(meta)}}`]);

  const pad = Math.max(...rows.map((r) => r[0].length));
  const body = rows.map(([k, v]) => `  ${k.padEnd(pad)} = ${v}`).join(",\n");
  return `@techreport{${citationKey(meta)},\n${body}\n}`;
}

/** The same citation as a sentence, for readers who do not use BibTeX. */
export function plainCitation(meta: CitationMeta, ctx: CitationContext): string {
  const author = citationAuthor(meta, ctx);
  const year = yearOf(meta.created);
  const title = texToPlain(meta.title).replace(/\.$/, "");
  const series = seriesLabel(meta, ctx);
  const version = validVersion(meta.version);
  const dated = formatDate(meta.revised) || formatDate(meta.created);
  const versionBit = version !== null ? `, version ${version}${dated ? ` (${dated})` : ""}` : "";
  const link = doiUrl(meta.doi) ?? paperUrl(meta, ctx);
  const head = `${author}${year ? ` (${year})` : ""}. “${title}.” ${series}${versionBit}.`;
  return link ? `${head} ${link}` : head;
}

/** Singular series name for the numbered form ("CausalSmith Working Paper 8"). */
export function seriesLabel(meta: CitationMeta, ctx: CitationContext): string {
  const inst = ctx.institution ?? DEFAULT_INSTITUTION;
  const number = validText(meta.wpNumber);
  return number ? `${inst.replace(/Papers$/, "Paper")} ${number}` : inst;
}
