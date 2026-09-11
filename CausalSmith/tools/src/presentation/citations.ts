/**
 * Citation pool discipline: the bib is collected before drafting (P0), writers
 * may only cite pool keys, and every entry is verified against an external
 * record (existence + metadata fields — the common hallucination is a real
 * title with wrong fields). Claim-support checking is a separate P3 gate.
 */

export interface BibEntry {
  key: string;
  type: string;
  fields: Record<string, string>;
}

export interface ExternalRecord {
  title: string;
  authorFamily: string;
  /** Canonical BibTeX-style author list when the registry supplies full authors. */
  author?: string;
  year: number;
  /** True when fetched by a DOI/arXiv id (the source is the entry's OWN identifier, so the
   *  record is the right work by construction). A title-query record is never authoritative. */
  authoritative?: boolean;
}

interface OpenAlexItem {
  title?: string;
  publication_year?: number;
  authorships?: Array<{ author?: { display_name?: string } }>;
}

function fromOpenAlex(item: OpenAlexItem | undefined): ExternalRecord | null {
  const title = item?.title?.trim() ?? "";
  const authors = (item?.authorships ?? [])
    .map((a) => a.author?.display_name?.trim() ?? "")
    .filter(Boolean);
  const first = authors[0]?.split(/\s+/) ?? [];
  const year = item?.publication_year ?? 0;
  if (!title || first.length === 0 || year <= 0) return null;
  return {
    title,
    authorFamily: first[first.length - 1] ?? "",
    author: authors.join(" and "),
    year,
  };
}

/** Rewrite only identity-confirmed bibliographic fields. The citation key, type, DOI/eprint,
 * and all unrelated fields are preserved. Title-query records are intentionally ineligible. */
export function canonicalizeBibEntry(bib: string, key: string, rec: ExternalRecord): string | null {
  if (!rec.authoritative) return null;
  // NB the escaper class: `[.*+?^${}()|[\]\\]` — the earlier spelling closed the
  // class one char early, so NO special char was escaped unless followed by `]`,
  // and a bib key containing `.`/`+` built a wrong regex that silently no-oped
  // the canonicalization.
  const startRe = new RegExp(`@([A-Za-z]+)\\s*\\{\\s*${key.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*,`, "i");
  const match = startRe.exec(bib);
  if (!match) return null;
  const start = match.index;
  const brace = bib.indexOf("{", start);
  let depth = 0;
  let end = -1;
  for (let i = brace; i < bib.length; i++) {
    if (bib[i] === "{") depth++;
    else if (bib[i] === "}" && --depth === 0) { end = i + 1; break; }
  }
  if (end < 0) return null;
  let block = bib.slice(start, end);
  const values: Record<string, string | undefined> = {
    title: rec.title || undefined,
    author: rec.author,
    year: rec.year > 0 ? String(rec.year) : undefined,
  };
  for (const [field, value] of Object.entries(values)) {
    if (!value) continue;
    const safe = value
      .replace(/[{}]/g, "")
      // Crossref occasionally returns HTML entities in titles. A literal `&`
      // is an alignment token in TeX, so canonical metadata must remain valid
      // BibTeX after normalization.
      .replace(/&amp;/gi, "&")
      .replace(/(?<!\\)&/g, "\\&");
    // Function replacements ONLY: `safe` is external registry text and titles
    // like "Sharp $1$-Wasserstein bounds" contain `$1`/`$&`, which a STRING
    // replacement expands as capture references — silently corrupting the
    // written references.bib.
    const fieldRe = new RegExp(`(\\b${field}\\s*=\\s*)(?:\\{(?:[^{}]|\\{[^{}]*\\})*\\}|\"[^\"]*\"|[^,}]+)`, "i");
    if (fieldRe.test(block)) block = block.replace(fieldRe, (_m, lead: string) => `${lead}{${safe}}`);
    else block = block.replace(/}\s*$/, () => `,\n  ${field} = {${safe}}\n}`);
  }
  return bib.slice(0, start) + block + bib.slice(end);
}

/**
 * Sentinel: the external registry could not be reached (transient 429/5xx/network
 * failure), as opposed to `null` which means "reached, but no matching record".
 * The distinction matters because an entry that carries a well-formed DOI/arXiv id
 * whose registry is merely unreachable must NOT be laundered into a confident
 * "hallucinated citation" rejection — that would hard-fail an emit on a network blip.
 */
export const UNREACHABLE = Symbol("registry-unreachable");

export type Lookup = (e: BibEntry) => Promise<ExternalRecord | typeof UNREACHABLE | null>;

export interface Verification {
  key: string;
  verdict: "exact" | "minor" | "major";
  detail: string;
}

export function parseBib(bib: string): BibEntry[] {
  const out: BibEntry[] = [];
  for (const entry of scanBibEntries(bib)) {
    const fields: Record<string, string> = {};
    for (const [name, value] of scanBibFields(entry.body)) fields[name.toLowerCase()] = value.trim();
    out.push({ key: entry.key.trim(), type: entry.type.toLowerCase(), fields });
  }
  return out;
}

function scanBibEntries(bib: string): Array<{ type: string; key: string; body: string }> {
  const entries: Array<{ type: string; key: string; body: string }> = [];
  let i = 0;
  while (i < bib.length) {
    const at = bib.indexOf("@", i);
    if (at < 0) break;
    let j = at + 1;
    const type = /^[A-Za-z]+/.exec(bib.slice(j))?.[0];
    if (!type) {
      i = j;
      continue;
    }
    j += type.length;
    while (/\s/.test(bib[j] ?? "")) j++;
    if (bib[j] !== "{") {
      i = j;
      continue;
    }
    // why: balance the ENTIRE `@type{...}` block FIRST (string-aware), so a special entry with no key
    // comma (`@string{JASA = "..."}`) can't scan its "key" past its own `}` into the next real entry.
    const braceStart = j;
    j++;
    let depth = 1;
    let quote = false;
    for (; j < bib.length; j++) {
      const ch = bib[j];
      if (ch === "\\") {
        j++;
      } else if (ch === '"') {
        quote = !quote;
      } else if (!quote && ch === "{") {
        depth++;
      } else if (!quote && ch === "}") {
        depth--;
        if (depth === 0) break;
      }
    }
    if (depth !== 0) break; // unterminated block — nothing safe to parse past here
    const inner = bib.slice(braceStart + 1, j); // between the outer braces
    const t = type.toLowerCase();
    // Skip BibTeX meta forms — they are not keyed reference entries.
    if (t !== "string" && t !== "comment" && t !== "preamble") {
      const comma = inner.indexOf(","); // bib keys contain no comma, so the first comma splits key|body
      if (comma >= 0) entries.push({ type, key: inner.slice(0, comma), body: inner.slice(comma + 1) });
      // else: a keyed entry with no fields — nothing to record
    }
    i = j + 1;
  }
  return entries;
}

function scanBibFields(body: string): Array<[string, string]> {
  const fields: Array<[string, string]> = [];
  let i = 0;
  while (i < body.length) {
    while (i < body.length && /[\s,]/.test(body[i])) i++;
    const name = /^[A-Za-z][A-Za-z0-9_-]*/.exec(body.slice(i))?.[0];
    if (!name) {
      i++;
      continue;
    }
    i += name.length;
    while (/\s/.test(body[i] ?? "")) i++;
    if (body[i] !== "=") continue;
    i++;
    while (/\s/.test(body[i] ?? "")) i++;
    let value = "";
    if (body[i] === "{") {
      const start = ++i;
      let depth = 1;
      for (; i < body.length; i++) {
        if (body[i] === "\\") {
          i++;
        } else if (body[i] === "{") {
          depth++;
        } else if (body[i] === "}") {
          depth--;
          if (depth === 0) break;
        }
      }
      value = body.slice(start, i);
      i++;
    } else if (body[i] === '"') {
      const start = ++i;
      for (; i < body.length; i++) {
        if (body[i] === "\\") i++;
        else if (body[i] === '"') break;
      }
      value = body.slice(start, i);
      i++;
    } else {
      const start = i;
      while (i < body.length && body[i] !== ",") i++;
      value = body.slice(start, i);
    }
    fields.push([name, value]); // why: valid BibTeX allows one-line entries and quoted values, not only newline-closed braced fields.
  }
  return fields;
}

export function citedKeys(tex: string): Set<string> {
  const keys = new Set<string>();
  // `[A-Za-z]*` covers the whole natbib family (`\citealp`, `\citeauthor`,
  // `\citeyearpar`, `\Citet`, …): a key cited only through a variant this regex
  // missed skipped external verification entirely while still compiling.
  const re = /\\[Cc]ite[A-Za-z]*\*?(?:\[[^\]]*\])*\{([^}]+)\}/g;
  let m: RegExpExecArray | null;
  while ((m = re.exec(tex))) for (const k of m[1].split(",")) keys.add(k.trim());
  return keys;
}

/** LaTeX accent commands and Unicode diacritics both reduce to the base letter, so a registry's
 *  "Sävje"/"Erdős" matches an entry's `S\"avje`/`Erd\H{o}s`; `\o`, `\l`, `\ss`, `\ae` map to their
 *  ASCII spellings. Every other non-alphanumeric character is dropped as before. */
const LATEX_LETTERS: Record<string, string> = { o: "o", O: "O", l: "l", L: "L", ss: "ss", ae: "ae", AE: "AE", oe: "oe", OE: "OE", aa: "a", AA: "A", i: "i", j: "j" };
const asciiLetters = (s: string): string =>
  s
    // Punctuation accents (\"a \'{e} \^o) take the next letter directly; letter-named accents (\H{o}
    // \v{s} \c{c} \u a) need a brace or space after them — otherwise \beta, \textit, \rho, \vec lose
    // their first letter.
    .replace(/\\(?:[`'^"~=.]|[uvHtcdbkr](?=[\s{]))\s*\{?\\?([A-Za-z])\}?/g, "$1")
    .replace(/\\(ss|ae|AE|oe|OE|aa|AA|o|O|l|L|i|j)\b\{?\}?/g, (_m, k: string) => LATEX_LETTERS[k] ?? k)
    .normalize("NFKD")
    .replace(/[\u0300-\u036f]/g, "")
    // Letters with no canonical decomposition: dotless ı (Turkish names such as Varıcı), ł, ø, ß, æ, œ, đ, ð, þ.
    .replace(/ı/g, "i").replace(/ł/g, "l").replace(/Ł/g, "L").replace(/ø/g, "o").replace(/Ø/g, "O").replace(/ß/g, "ss").replace(/ẞ/g, "SS").replace(/æ/g, "ae").replace(/Æ/g, "AE").replace(/œ/g, "oe").replace(/Œ/g, "OE").replace(/đ/g, "d").replace(/Đ/g, "D").replace(/ð/g, "d").replace(/Ð/g, "D").replace(/þ/g, "th").replace(/Þ/g, "Th");
const norm = (s: string) =>
  asciiLetters(s)
    .toLowerCase()
    .replace(/[^a-z0-9 ]/g, "")
    .replace(/\s+/g, " ")
    .trim();

/** Every author's family name in a BibTeX author field, normalized. */
const bibAuthorFamilies = (authors: string): string[] =>
  authors.split(/\s+and\s+/i).map((a) => {
    const one = a.trim();
    const comma = one.indexOf(",");
    if (comma >= 0) return norm(one.slice(0, comma));
    const words = one.split(/\s+/).filter(Boolean);
    return norm(words[words.length - 1] ?? "");
  }).filter(Boolean);

/** A registry's family name confirms the entry when it IS one of the entry's family names or the
 * trailing whole word of one ("erven" for "van erven": most adapters take the last word of a full
 * name). Any position: registries do not always list the authors in the entry's order. Whole-word
 * only, so "li" never confirms "lin". */
const authorFamilyMatches = (e: BibEntry, rec: ExternalRecord): boolean => {
  const fam = norm(rec.authorFamily);
  if (!fam) return false;
  // Either side may carry the fuller name: a particle family in the entry ("van erven" ⊇ "erven"),
  // or a registry that put the whole name in the family slot ("jiantao jiao" ⊇ "jiao").
  return bibAuthorFamilies(e.fields.author ?? "").some((f) => f === fam || f.endsWith(" " + fam) || fam.endsWith(" " + f));
};

/** Title identity ignores spacing as well as case and punctuation: registries carry typos such as
 * "ofN-way" for "of N-way", and spaces never distinguish works. */
// A leading article is not identity ("An Orthogonal Basis…" is "Orthogonal basis…").
const titleKey = (s: string): string => norm(stripRegistryMarkup(s)).replace(/^(?:a|an|the) /, "").replace(/ /g, "");
// A subtitle follows a colon, a dash, or a question mark ("…Demonstrate? Causal Inference…").
const titleCore = (title: string): string => titleKey(title.split(/\s*[:–—?]\s*/, 1)[0] ?? "");

/** Same title, or an exact short/full-title relation: one side IS the other's pre-subtitle title.
 * Crossref stores books under the short title; arXiv and publishers vary the subtitle. Two titles
 * that merely share a core but carry different subtitles are different works. */
const titleRelated = (a: string, b: string): boolean =>
  titleKey(a) === titleKey(b) ||
  ((substantive(a) || substantive(b)) && titleCore(a) !== "" && (titleKey(a) === titleCore(b) || titleKey(b) === titleCore(a)));

/** Three or more words: registries hold author-less records titled "Introduction", "Comment",
 * "Erratum" in every year, and a one-word short title relates to any "Word: subtitle" entry. Only a
 * substantive title may confirm a work without an author or through the short/full relation. */
const substantive = (title: string): boolean => norm(title).split(" ").filter(Boolean).length >= 3;

export async function verifyEntry(e: BibEntry, lookup: Lookup): Promise<Verification> {
  // A work no registry indexes under its own identity (an unindexed monograph, a title shared with
  // a review of it) can only be confirmed by hand: the orchestrator records what confirmed it in a
  // `verifiedby` field and the entry is kept on that authority, visibly. P0 strips the field from
  // fresh model output, so it only ever reaches here from a hand edit.
  const handVerified = e.fields.verifiedby?.trim();
  if (handVerified) return { key: e.key, verdict: "minor", detail: `hand-verified (${handVerified})` };
  const rec = await lookup(e);
  // A registry the check needed did not answer (429/5xx/network, or a non-JSON body): the work may
  // well be indexed there. Kept as a transient caveat (P0 keeps it, P4 does not abort) rather than
  // laundered into a hallucination rejection; the next run re-verifies.
  if (rec === UNREACHABLE) {
    return {
      key: e.key,
      verdict: "minor",
      detail: "external registry unreachable (transient); metadata unverified this run",
    };
  }
  if (!rec) {
    const id = e.fields.doi
      ? `DOI ${e.fields.doi} is not in Crossref`
      : e.fields.eprint ? `arXiv id ${e.fields.eprint} resolves to nothing` : "";
    return {
      key: e.key,
      verdict: "major",
      detail: id ? `no external record found: ${id} and no registry lists the title` : "no external record found",
    };
  }
  const titleOk = titleKey(rec.title) === titleKey(e.fields.title ?? "");
  const year = parseInt(e.fields.year ?? "0", 10);
  const yearOk = Math.abs(rec.year - year) <= 1;
  // A registry record that lists no author cannot contradict the entry; it corroborates nothing
  // either, so it never yields "exact" and its caveat says the author went unverified.
  const famKnown = norm(rec.authorFamily) !== "";
  const famOk = famKnown && authorFamilyMatches(e, rec);
  const titleVariantOk = titleRelated(rec.title, e.fields.title ?? "");
  if (titleOk && yearOk && famOk) return { key: e.key, verdict: "exact", detail: "" };
  // Title and author together identify the work; a year gap (edition, print vs online, an
  // unparsable year) is a field caveat for the orchestrator, with the record's year named.
  if (titleOk && famOk) {
    return { key: e.key, verdict: "minor", detail: `year ${e.fields.year ?? ""} vs record ${rec.year} — check the edition/year` };
  }
  // A short/full-title relation with the year corroborating and the author agreeing (or absent) is
  // the same work: a registry subtitle discrepancy (Crossref keeps only a book's short title), never
  // a wrong-source drop. A same-author record for a genuinely different work still fails below.
  if ((famOk || (!famKnown && substantive(rec.title))) && yearOk && titleVariantOk) {
    return {
      key: e.key,
      verdict: "minor",
      detail: !famKnown
        ? `registry record lists no author; title and year agree — author unverified`
        : rec.authoritative
          ? `id-confirmed source; entry title differs from registry ("${rec.title}") — fix title/fields from record`
          : `entry title differs from registry ("${rec.title}"); author and year agree — check the subtitle`,
    };
  }
  // Same title, different identity: the registry hit is another work (a review, a namesake). Never
  // "fix" the entry from it; the halt names the record so the orchestrator can adjudicate.
  if (titleOk) {
    return {
      key: e.key,
      verdict: "major",
      detail: `title matches but author or year does not (record: ${rec.authorFamily || "no author"} ${rec.year}; entry: ${bibAuthorFamilies(e.fields.author ?? "")[0] ?? "no author"} ${e.fields.year ?? ""})`,
    };
  }
  return { key: e.key, verdict: "major", detail: "title does not match external record" };
}

const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));
let lastFetch = 0;

/**
 * Fetch outcome, distinguishing a definitive "absent" (a non-retryable 4xx — the
 * work is not in this registry) from a transient "unreachable" (429/5xx/network,
 * retries exhausted — we could not reach the registry). Callers must not treat the
 * latter as evidence the citation is wrong.
 */
type Fetched =
  | { ok: true; response: Response }
  | { ok: false; unreachable: boolean; status?: number };

async function politeFetch(url: string): Promise<Fetched> {
  for (let attempt = 0; attempt < 3; attempt++) {
    const wait = lastFetch + 1000 - Date.now();
    if (wait > 0) await sleep(wait);
    lastFetch = Date.now();
    try {
      const r = await fetch(url, {
        headers: {
          "User-Agent":
            process.env.CAUSALSMITH_CONTACT ??
            "causalean/0.1 (+https://github.com/Jiyuan-Tan/AutoID)",
        },
      });
      if (r.ok) return { ok: true, response: r };
      if (r.status < 500 && r.status !== 429) return { ok: false, unreachable: false, status: r.status }; // definitive 4xx
    } catch {
      // network error — retry
    }
    await sleep(1000 * 2 ** attempt);
  }
  return { ok: false, unreachable: true }; // retries exhausted → transient
}

interface CrossrefItem {
  title?: string[];
  author?: { family?: string; given?: string }[];
  issued?: { "date-parts"?: number[][] };
}

/** Registry titles carry publisher markup (IEEE wraps formulas in `<inline-formula>` /
 *  `<tex-math>`, entities appear escaped); strip it before any comparison. */
export function stripRegistryMarkup(title: string): string {
  return title
    .replace(/<[^>]+>/g, " ")
    .replace(/&amp;/g, "&").replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&quot;/g, "\"").replace(/&#39;/g, "'")
    .replace(/\s+/g, " ").trim();
}

function fromCrossref(it: CrossrefItem | undefined | null): ExternalRecord | null {
  if (!it) return null;
  return {
    title: stripRegistryMarkup(it.title?.[0] ?? ""),
    authorFamily: it.author?.[0]?.family ?? "",
    author: it.author?.map((a) => [a.family, a.given].filter(Boolean).join(", ")).filter(Boolean).join(" and ") || undefined,
    year: it.issued?.["date-parts"]?.[0]?.[0] ?? 0,
  };
}

function fromArxivFeed(xml: string): ExternalRecord | null {
  // first <title> is the feed title; the entry title is the second
  const titles = [...xml.matchAll(/<title>([\s\S]*?)<\/title>/g)].map((m) => m[1].trim());
  const title = titles[1] ?? "";
  const names = [...xml.matchAll(/<name>([^<]+)<\/name>/g)].map((m) => m[1].trim());
  const fam = names[0]?.split(" ").pop() ?? "";
  const year = parseInt(xml.match(/<published>(\d{4})/)?.[1] ?? "0", 10);
  return title ? { title, authorFamily: fam, author: names.join(" and "), year } : null;
}

/** Record fetch result: the parsed record (null if none) plus whether the miss was transient. */
type RecFetch = { rec: ExternalRecord | null; unreachable: boolean };

async function arxivById(eprint: string): Promise<RecFetch> {
  // models emit "arXiv:2305.04116" / "2305.04116v2"; the API wants the bare id
  const id = eprint.replace(/^\s*arxiv:\s*/i, "").trim();
  for (let attempt = 0; attempt < 2; attempt++) {
    const r = await politeFetch(`https://export.arxiv.org/api/query?id_list=${encodeURIComponent(id)}`);
    // arXiv answers 403 (not 429) when it throttles a client: transient, not a missing id.
    if (!r.ok) return { rec: null, unreachable: r.unreachable || r.status === 403 };
    const rec = fromArxivFeed(await r.response.text());
    if (rec) return { rec, unreachable: false };
    // arXiv intermittently answers a valid id with an empty feed; one retry separates that from
    // an id that resolves to nothing.
    if (attempt === 0) await sleep(3000);
  }
  return { rec: null, unreachable: false };
}

async function arxivByTitle(title: string): Promise<RecFetch> {
  // arXiv-only preprints are invisible to Crossref; ti:"…" search covers them
  const q = encodeURIComponent(`ti:"${title.replace(/"/g, "")}"`);
  const r = await politeFetch(
    `https://export.arxiv.org/api/query?search_query=${q}&max_results=1`,
  );
  if (!r.ok) return { rec: null, unreachable: r.unreachable };
  return { rec: fromArxivFeed(await r.response.text()), unreachable: false };
}

function decodeHtmlMetadata(value: string): string {
  let out = value;
  // Some publisher pages double-encode numeric entities (`&amp;#228;`). Two
  // passes recover the intended Unicode without adding an HTML-parser dependency.
  for (let pass = 0; pass < 2; pass++) {
    out = out
      .replace(/&#x([0-9a-f]+);/gi, (_m, hex: string) => String.fromCodePoint(parseInt(hex, 16)))
      .replace(/&#([0-9]+);/g, (_m, dec: string) => String.fromCodePoint(parseInt(dec, 10)))
      .replace(/&quot;/gi, '"')
      .replace(/&apos;/gi, "'")
      .replace(/&lt;/gi, "<")
      .replace(/&gt;/gi, ">")
      .replace(/&amp;/gi, "&");
  }
  return out.trim();
}

function htmlMetaValues(html: string, name: string): string[] {
  const values: string[] = [];
  for (const tag of html.match(/<meta\b[^>]*>/gi) ?? []) {
    const attrs = new Map<string, string>();
    const attrRe = /([\w:-]+)\s*=\s*(["'])(.*?)\2/g;
    let match: RegExpExecArray | null;
    while ((match = attrRe.exec(tag))) attrs.set(match[1].toLowerCase(), match[3]);
    if (attrs.get("name")?.toLowerCase() === name.toLowerCase() && attrs.has("content")) {
      values.push(decodeHtmlMetadata(attrs.get("content")!));
    }
  }
  return values;
}

function trustedJmlrUrl(raw: string | undefined): string | null {
  if (!raw) return null;
  try {
    const url = new URL(raw);
    if (url.protocol !== "https:") return null;
    if (url.hostname !== "jmlr.org" && url.hostname !== "www.jmlr.org") return null;
    if (!/^\/papers\/v\d+\/[A-Za-z0-9._-]+\.html$/.test(url.pathname)) return null;
    return url.toString();
  } catch {
    return null;
  }
}

async function jmlrByUrl(url: string): Promise<RecFetch> {
  const fetched = await politeFetch(url);
  if (!fetched.ok) return { rec: null, unreachable: fetched.unreachable };
  const html = await fetched.response.text();
  const title = htmlMetaValues(html, "citation_title")[0] ?? "";
  const authors = htmlMetaValues(html, "citation_author");
  const year = parseInt(htmlMetaValues(html, "citation_publication_date")[0] ?? "0", 10);
  if (!title || authors.length === 0 || !Number.isFinite(year) || year <= 0) {
    return { rec: null, unreachable: false };
  }
  const first = authors[0].trim().split(/\s+/);
  return {
    rec: {
      title,
      authorFamily: first[first.length - 1] ?? "",
      author: authors.join(" and "),
      year,
    },
    unreachable: false,
  };
}

/**
 * Production lookup: DOI → Crossref; arXiv id → arXiv API; else title query
 * (Crossref, then arXiv and OpenAlex exact-title search).
 * A title-query candidate is accepted only when title, an author family, and year match —
 * a wrong-paper hit from one source must not mask a right-paper hit from the
 * next, and verifyEntry re-checks the returned record anyway.
 */
export async function defaultLookup(e: BibEntry): Promise<ExternalRecord | typeof UNREACHABLE | null> {
  const titleMatches = (rec: ExternalRecord | null) => rec !== null && titleRelated(rec.title, e.fields.title ?? "");
  const workMatches = (rec: ExternalRecord | null) => rec !== null && titleMatches(rec) && authorFamilyMatches(e, rec);
  const yearMatches = (rec: ExternalRecord) => {
    const year = parseInt(e.fields.year ?? "0", 10);
    return Number.isFinite(year) && Math.abs(rec.year - year) <= 1;
  };
  const identityMatches = (rec: ExternalRecord | null) => workMatches(rec) && yearMatches(rec!);
  // A record without an author can be the work (registries omit book authors); it ranks below any
  // author-confirmed candidate.
  const authorlessMatches = (rec: ExternalRecord | null) =>
    rec !== null && norm(rec.authorFamily) === "" && substantive(rec.title) && titleMatches(rec) && yearMatches(rec);
  const getJson = async (url: string): Promise<{ json: unknown; unreachable: boolean }> => {
    const r = await politeFetch(url);
    if (!r.ok) return { json: null, unreachable: r.unreachable };
    // A 200 whose body is not JSON is a rate-limit interstitial or an outage page: transient.
    try { return { json: await r.response.json(), unreachable: false }; } catch { return { json: null, unreachable: true }; }
  };
  const jmlrUrl = trustedJmlrUrl(e.fields.url);
  const hasAuthId = Boolean(e.fields.doi || e.fields.eprint || jmlrUrl);
  let authUnreachable = false; // an authoritative id was present but its registry was unreachable
  try {
    if (e.fields.doi) {
      const { json, unreachable } = await getJson(
        `https://api.crossref.org/works/${encodeURIComponent(e.fields.doi)}`,
      );
      authUnreachable ||= unreachable;
      const rec = fromCrossref((json as { message?: CrossrefItem } | null)?.message);
      if (rec) return { ...rec, authoritative: true }; // DOI is authoritative; mismatch = field error, not wrong source
    }
    if (e.fields.eprint) {
      const { rec, unreachable } = await arxivById(e.fields.eprint);
      authUnreachable ||= unreachable;
      if (rec) return { ...rec, authoritative: true }; // eprint id is authoritative too
    }
    if (jmlrUrl) {
      const { rec, unreachable } = await jmlrByUrl(jmlrUrl);
      authUnreachable ||= unreachable;
      // JMLR's canonical article page supplies Highwire citation metadata. It
      // identifies the work directly, unlike a loose title query whose first
      // result may be an unrelated newer paper.
      if (rec) return { ...rec, authoritative: true };
    }
    // The entry carries a well-formed DOI/arXiv id but we could not REACH its registry (transient).
    // Do NOT fall back to a title query: its top hit is often a DIFFERENT paper, whose title mismatch
    // would be laundered into a confident "major" rejection that hard-fails the emit. Signal transient
    // instead → non-blocking. (A definitively-absent id — reachable 4xx / empty arXiv feed — leaves
    // authUnreachable false and still falls through to the title fallback, so fabricated ids are caught.)
    if (hasAuthId && authUnreachable) return UNREACHABLE;
    // No identifier (or identifier definitively did not resolve): search by title.
    const authMissed = hasAuthId; // reachable registries, no record for the id
    const candidates: (ExternalRecord | null)[] = [];
    let titleUnreachable = false; // a registry the title search needed answered 429/5xx/network
    const crossref = await getJson(
      `https://api.crossref.org/works?rows=10&query.title=${encodeURIComponent(e.fields.title ?? "")}`,
    );
    titleUnreachable ||= crossref.unreachable;
    const crossrefItems = (crossref.json as { message?: { items?: CrossrefItem[] } } | null)?.message?.items ?? [];
    candidates.push(...crossrefItems.map(fromCrossref));
    if (!candidates.some(identityMatches) && e.fields.title) {
      const arxiv = await arxivByTitle(e.fields.title);
      titleUnreachable ||= arxiv.unreachable;
      candidates.push(arxiv.rec);
    }
    if (!candidates.some(identityMatches) && e.fields.title) {
      const openAlex = await getJson(
        // Commas and colons are OpenAlex filter syntax; the search is tokenized, so punctuation carries nothing.
        `https://api.openalex.org/works?filter=title.search:${encodeURIComponent(e.fields.title.replace(/[^\p{L}\p{N}]+/gu, " ").trim())}&per-page=10`,
      );
      titleUnreachable ||= openAlex.unreachable;
      const openAlexItems = (openAlex.json as { results?: OpenAlexItem[] } | null)?.results ?? [];
      candidates.push(...openAlexItems.map(fromOpenAlex));
    }
    // Prefer the same work at another year (edition, print vs online) over an unrelated top hit.
    const best = candidates.find(identityMatches) ?? candidates.find(workMatches) ?? candidates.find(authorlessMatches);
    if (best) return best;
    // No match, but a registry the search needed did not answer: the work may well be indexed
    // there. Transient, non-blocking — never launder a rate limit into a confident rejection.
    if (titleUnreachable) return UNREACHABLE;
    // An id that resolved to nothing is the finding; an unrelated top hit for the title would
    // only turn it into a misleading "title does not match".
    if (authMissed && !candidates.some((c) => c !== null && titleKey(c.title) === titleKey(e.fields.title ?? ""))) return null;
    return candidates[0] ?? null;
  } catch {
    return null;
  }
}
