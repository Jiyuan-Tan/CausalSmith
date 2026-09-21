/**
 * Paper identity: version history, and the arXiv-style page-1 stamp.
 *
 * ## Why the values live in their own generated file
 *
 * `paper.tex` is DERIVED by the P2 assembly from the authored sources and is digest-protected
 * (`p2_assembly_manifest.json`), so nothing downstream may edit its body. A DOI, though,
 * arrives AFTER the paper is compiled and deposited — and it has to reach page 1. Writing it
 * into `paper.tex` would either require a reassembly (which re-drafts prose) or a hand-edit of
 * a protected derived file.
 *
 * So the stamp is split in two:
 *   * `paper_macros.tex` (template-owned, refreshed by P4 on every emit) holds the FORMAT —
 *     package loads, the shipout hook, fonts, colour, placement, field order. A layout fix ships with the
 *     template and needs no bundle regeneration.
 *   * `paper_stamp.tex` (generated here) holds only the VALUES — number, version, area,
 *     revised date, DOI, link target. It is `\input` from the template under `\IfFileExists`,
 *     so a bundle without it still compiles exactly as before.
 *
 * `paper_stamp.tex` is deliberately NOT one of the digest's authored inputs (the digest covers
 * `outline.md`, `front_matter.tex`, `appendix_proofs.tex`, `sections/*.tex`, `proofs/*.tex`),
 * so rewriting it and re-running `latexmk` cannot trip `assertP2AssemblyFresh`.
 */
import { createHash } from "node:crypto";
import { readFile, writeFile } from "node:fs/promises";
import { join } from "node:path";
import process from "node:process";
import { assertCalendarIsoDate, isCalendarIsoDate, isoParts, utcToday } from "./iso_date.js";
import { resolveWpNumber } from "./wp_registry.js";
import { writeTextAtomic } from "../shared/json_atomic.js";

export { utcToday } from "./iso_date.js";

/** sha256 of a file's exact bytes. This is what `versions[].paper_sha256` records and what
 *  P5's `manuscript_sha256` must agree with, so the site can match a review to a version. */
export async function fileSha256(path: string): Promise<string> {
  return createHash("sha256").update(await readFile(path)).digest("hex");
}

const MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"] as const;
const MONTHS_LONG = [
  "January", "February", "March", "April", "May", "June",
  "July", "August", "September", "October", "November", "December",
] as const;

/** `2026-08-27` → `27 Aug 2026` (the stamp's compact arXiv-style form). Formatted from the
 *  string, never through `Date`/`toLocaleDateString`: both would import the host's timezone
 *  and locale into a published PDF. */
export function stampDate(iso: string): string {
  const { y, m, d } = isoParts(iso);
  return `${d} ${MONTHS[m - 1]} ${y}`;
}

/** `2026-08-27` → `27 August 2026` (the pinned `\date{}` on the title block). */
export function titleDate(iso: string): string {
  const { y, m, d } = isoParts(iso);
  return `${d} ${MONTHS_LONG[m - 1]} ${y}`;
}

// ---------------------------------------------------------------------------
// version history

/** The later of two calendar dates (ISO strings sort chronologically). */
function maxIsoDate(a: string, b: string): string {
  return a >= b ? a : b;
}

/** Whole days `date` falls after `reference`; 0 when it is the same day or earlier. */
function daysAhead(date: string, reference: string): number {
  const ms = Date.parse(`${date}T00:00:00.000Z`) - Date.parse(`${reference}T00:00:00.000Z`);
  return ms <= 0 ? 0 : Math.round(ms / 86_400_000);
}

export type VersionEntry = { v: number; date: string; paper_sha256?: string | null };

export type VersionState = { version: number; revised: string; versions: VersionEntry[] };

/**
 * The version history after an emit whose `paper.tex` hashes to `sha`.
 *
 * A bump happens only when the manuscript actually changed: a `--from P4` re-emit that
 * recompiles the same bytes must not invent a v4. The comparison is against the LAST recorded
 * entry's hash; a history whose last entry has no hash yet (the backfill can only recover a
 * date from git, not the historical bytes of earlier rounds) adopts `sha` in place rather than
 * bumping, because "unknown" is not evidence of a change.
 *
 * Every date is validated as a real calendar date, and the history must move FORWARD: a new
 * version may not be dated before `created` or before the version it follows. A backwards
 * revision date is not a cosmetic defect — it is what a reader cites, and "v2, dated before v1"
 * is unreadable. The usual cause is a wrong host clock or a hand-edited `created`, so this fails
 * the emit rather than quietly writing the contradiction into the published record.
 */
export function nextVersionState(
  prev: { version?: unknown; revised?: unknown; versions?: unknown },
  sha: string,
  today: string,
  created: string,
  /** Other hashes that identify the SAME manuscript — from `manuscriptEquivalentShas`, which
   *  treats the date pin as the no-op it is. Stateless: it does not matter which run pinned. */
  opts: { equivalentShas?: readonly string[] } = {},
): VersionState {
  assertCalendarIsoDate("meta.json created", created);
  assertCalendarIsoDate("emit date", today);
  // A recorded entry is either well-formed or a defect to report — never silently dropped, which
  // would renumber the history and could hand v3's number to a fourth revision.
  const history: VersionEntry[] = Array.isArray(prev.versions)
    ? prev.versions.map((raw, i): VersionEntry => {
        const entry = raw as { v?: unknown; date?: unknown; paper_sha256?: unknown };
        if (typeof entry.v !== "number" || !Number.isInteger(entry.v) || entry.v < 1) {
          throw new Error(`meta.json versions[${i}].v is not a positive integer: ${JSON.stringify(entry.v)}`);
        }
        assertCalendarIsoDate(`meta.json versions[${i}].date`, entry.date);
        return {
          v: entry.v,
          date: entry.date as string,
          paper_sha256: typeof entry.paper_sha256 === "string" ? entry.paper_sha256 : null,
        };
      })
    : [];
  history.sort((a, b) => a.v - b.v);
  // The series must be COMPLETE: 1, 2, 3, … with no gap, no repeat. A history of [v1, v3] would
  // be accepted, the next change would append v4, and "v2" would be permanently missing from a
  // record readers cite by version number.
  for (const [i, entry] of history.entries()) {
    if (entry.v !== i + 1) {
      throw new Error(
        `meta.json versions must be a contiguous series starting at 1; found ` +
          `[${history.map((e) => e.v).join(", ")}]. Correct meta.json by hand.`,
      );
    }
    const floor = i === 0 ? created : history[i - 1]!.date;
    if (entry.date < floor) {
      throw new Error(
        `meta.json version history moves backwards: v${entry.v} is dated ${entry.date}, before ` +
          `${i === 0 ? `created ${created}` : `v${history[i - 1]!.v} (${history[i - 1]!.date})`}. Correct meta.json by hand.`,
      );
    }
  }
  // The top-level fields are what the site and the stamp read; the history is what they must
  // summarise. They are written together, so a disagreement is a hand-edit that got half done —
  // and the half that is wrong would be the half on page 1. Checked only when recorded, since a
  // bundle being stamped for the first time legitimately has neither.
  const newest = history[history.length - 1];
  if (newest) {
    if (prev.version !== undefined && prev.version !== null && prev.version !== newest.v) {
      throw new Error(
        `meta.json version is ${JSON.stringify(prev.version)} but its newest history entry is v${newest.v}. ` +
          "Correct meta.json by hand.",
      );
    }
    if (prev.revised !== undefined && prev.revised !== null && prev.revised !== newest.date) {
      throw new Error(
        `meta.json revised is ${JSON.stringify(prev.revised)} but its newest history entry (v${newest.v}) is ` +
          `dated ${newest.date}. Correct meta.json by hand.`,
      );
    }
  }
  if (history.length === 0) {
    // First time this bundle is stamped. Its v1 is its publication date, not today: the paper
    // existed before the field did, and re-dating it to the emit would erase its own history.
    // An empty history cannot support a version above 1: there is no v1 entry for a v2 to
    // follow, and synthesising one would invent a revision date the paper never had. Some of its
    // history is simply missing, and only a human knows what it was.
    if (prev.version !== undefined && prev.version !== null && prev.version !== 1) {
      throw new Error(
        `meta.json records version ${JSON.stringify(prev.version)} but an empty versions list. That is ` +
          "incomplete legacy state, not a v1 — restore the history by hand (or set version to 1 if the " +
          "paper has only ever had one).",
      );
    }
    const priorVersion = 1;
    const revised = isCalendarIsoDate(prev.revised) ? prev.revised : created;
    if (revised < created) {
      throw new Error(`meta.json revised ${revised} is before created ${created}. Correct meta.json by hand.`);
    }
    return { version: priorVersion, revised, versions: [{ v: priorVersion, date: revised, paper_sha256: sha }] };
  }
  const last = history[history.length - 1]!;
  if (last.paper_sha256 == null || last.paper_sha256 === sha || opts.equivalentShas?.includes(last.paper_sha256)) {
    // Adopt the canonical hash in place — including when the match came through the pin
    // equivalence, so the reconciliation happens once rather than on every later emit.
    last.paper_sha256 = sha;
    return { version: last.v, revised: last.date, versions: history };
  }
  // The new version is dated at the LATEST of the emit date, `created`, and the version being
  // revised — so a revision can never predate what it revises, and an operator in a timezone
  // already on tomorrow's date (UTC+14 at 2026-09-20 UTC records 2026-09-21) can still ship a
  // same-local-day revision instead of hitting a failure they cannot act on.
  //
  // That tolerance is exactly one day. A recorded date further ahead than any timezone explains
  // is clock skew or corruption, and adopting it would push the published record arbitrarily far
  // into the future.
  const floor = maxIsoDate(created, last.date);
  if (daysAhead(floor, today) > 1) {
    throw new Error(
      `P4 blocked: this bundle records ${floor === created ? `created ${created}` : `v${last.v} dated ${last.date}`}, ` +
        `which is ${daysAhead(floor, today)} days after today (${today} UTC). That is past any timezone offset — ` +
        "check the host clock and the bundle's recorded dates before emitting.",
    );
  }
  const bumped: VersionEntry = { v: last.v + 1, date: maxIsoDate(today, floor), paper_sha256: sha };
  history.push(bumped);
  return { version: bumped.v, revised: bumped.date, versions: history };
}

/**
 * The short cluster label a bundle id implies — `stat_…` ⇒ `Stat`.
 *
 * DERIVED from the id, never read back from `meta.json`: it is shown in the byline, in the page-1
 * stamp and in the landing page's grouping, and those three must agree. P4 and the restamp tool
 * share this one function so a recompile can never relabel a paper.
 */
export function areaForBundleId(bundleId: string): string {
  return (
    {
      stat: "Stat",
      pid: "Partial ID",
      eid: "Exact ID",
      exp: "Experimentation",
      panel: "Panel",
    }[bundleId.split("_")[0]!] ?? "Others"
  );
}

// ---------------------------------------------------------------------------
// the generated stamp file

export type StampValues = {
  /** e.g. `CSWP-2026-008` in the default series, or null when the bundle has no number yet
   *  (then no stamp is drawn). */
  wpNumber: string | null;
  version: number;
  /** short cluster label, e.g. `Stat` */
  area: string;
  /** ISO date of the current version */
  revised: string;
  /** concept DOI, e.g. `10.5281/zenodo.123` */
  doi?: string | null;
  /** link target used when there is no DOI (the paper's page on the site); optional */
  siteUrl?: string | null;
};

/** LaTeX-escape a value destined for a `\renewcommand*` body. The inputs are machine-generated
 *  slugs and dates, but a title-cased area or a hand-set DOI must not be able to inject TeX.
 *  `^` and `~` have no `\<char>` escape in text mode — they are accents/ties — so they get their
 *  text-symbol commands instead of a backslash that would silently eat the next character. */
function texEscape(value: string): string {
  return value
    .replace(/[\\{}]/g, "")
    .replace(/\^/g, "\\textasciicircum{}")
    .replace(/~/g, "\\textasciitilde{}")
    .replace(/([&%$#_])/g, "\\$1");
}

/** A URL for `\href`: only `%` and `#` need protecting, and hyperref handles the rest. */
function urlEscape(value: string): string {
  return value.replace(/([%#\\{}])/g, "\\$1");
}

export const STAMP_FILE = "paper_stamp.tex";

/**
 * A DOI fit to PRINT on page 1: a published Zenodo production DOI.
 *
 * Zenodo's sandbox mints `10.5072/…` DOIs that resolve nowhere. They are perfectly valid state
 * for `meta.doi` to hold while a deposit is being rehearsed, but a PDF is a permanent artifact —
 * a stamped sandbox DOI would ship a dead citation that no later edit can recall. So the stamp
 * prints the DOI only on the production prefix and otherwise falls back to the paper's page; the
 * site applies the same test, so page 1 and the Cite panel can never disagree.
 *
 * Tested against the RAW stored value, with no trim. The field is externally owned, so it is
 * stored exactly as the depositor wrote it; a value carrying stray whitespace is not a DOI this
 * code may quietly repair into validity and then print. It simply is not stamped, and P4's state
 * note says so, which surfaces the malformed value instead of hiding it behind a correct-looking
 * page 1.
 */
export const PRODUCTION_DOI_RE = /^10\.5281\/zenodo\.\d+$/;

export function isProductionDoi(doi: unknown): doi is string {
  return typeof doi === "string" && PRODUCTION_DOI_RE.test(doi);
}

/**
 * Link target for a bundle that has no DOI yet: its page on the site. The production origin is
 * the one the site workflow deploys to (`SITE_URL` in `.github/workflows/site.yml`); override it
 * with `CAUSALSMITH_SITE_URL` (set it empty to stamp no link at all).
 */
export function paperSiteUrl(bundleId: string, env: NodeJS.ProcessEnv = process.env): string {
  const base = (env.CAUSALSMITH_SITE_URL ?? "https://causalsmith.org").replace(/\/+$/, "");
  return base === "" ? "" : `${base}/papers/${bundleId}`;
}

/**
 * The full text of `paper_stamp.tex`. Values only — the format lives in `paper_macros.tex`.
 * A bundle with no number gets a file that defines nothing visible, so the hook stays inert.
 */
export function renderStampTex(v: StampValues): string {
  // Only a production Zenodo DOI is printed and linked; a sandbox or malformed value leaves the
  // stamp DOI-less and pointing at the paper's page (see PRODUCTION_DOI_RE). The raw stored value
  // is used verbatim — this is a display decision, never a normalisation of persistent state.
  const doi = isProductionDoi(v.doi) ? v.doi : "";
  const link = doi ? `https://doi.org/${doi}` : (v.siteUrl?.trim() || "");
  const id = v.wpNumber ? `${v.wpNumber}v${v.version}` : "";
  return [
    "% GENERATED by CausalSmith P4 — paper identity stamp values. Do not hand-edit.",
    "%",
    "% Field order on the stamp (owned by paper_macros.tex):",
    "%   <number>v<version> · doi:<doi> · [<Area>] <date>   — the DOI is never the last token, so a",
    "%   text extractor cannot run it into whatever follows. Without a DOI that part is omitted.",
    "% Format lives in paper_macros.tex; only the values are here, and this file is NOT one of",
    "% the P2 assembly digest's authored inputs. A DOI arriving after publication therefore needs",
    "% this file rewritten plus a `latexmk` recompile — never a redraft or a reassembly.",
    `\\renewcommand*{\\csstampid}{${texEscape(id)}}`,
    `\\renewcommand*{\\csstamparea}{${texEscape(v.area)}}`,
    `\\renewcommand*{\\csstampdate}{${texEscape(stampDate(v.revised))}}`,
    `\\renewcommand*{\\csstampdoi}{${texEscape(doi)}}`,
    `\\renewcommand*{\\csstamplink}{${urlEscape(link)}}`,
    `\\renewcommand*{\\cspaperdate}{${texEscape(titleDate(v.revised))}}`,
    "",
  ].join("\n");
}

/**
 * Make a bundle's `paper.tex` preamble honour the pinned date.
 *
 * P2 now assembles `\date{\cspaperdate}`, but every bundle shipped before this change carries a
 * literal `\date{\today}` whose PDF date drifts on every recompile. `paper.tex` is derived, yet
 * it is NOT covered by the assembly digest (which hashes the authored sources), and P4 already
 * rewrites it for scope footnotes, cleveref repair and commit stamping — so normalising this one
 * preamble token here is in keeping, and it means a legacy bundle gets a pinned date from a plain
 * recompile instead of a reassembly that would drop its paper.tex-only revisions.
 *
 * The two directions are generated from ONE token pair so they cannot drift apart, and
 * `unpinDateCommand` is the exact inverse. That matters: the inverse is what lets any later run
 * recognise a pinned manuscript as the same paper as the unpinned bytes a previous record was
 * hashed from, WITHOUT having to know whether this run is the one that did the pinning. See
 * `manuscriptEquivalentShas`.
 *
 * Both are idempotent and neither touches a date pinned some other way.
 */
const DATE_UNPINNED = "\\date{\\today}";
const DATE_PINNED = "\\date{\\cspaperdate}";

export function pinDateCommand(tex: string): string {
  return tex.split(DATE_UNPINNED).join(DATE_PINNED);
}

/** The exact inverse of `pinDateCommand`. */
export function unpinDateCommand(tex: string): string {
  return tex.split(DATE_PINNED).join(DATE_UNPINNED);
}

/**
 * Every hash that identifies this manuscript as THIS manuscript.
 *
 * `canonical` is the hash of the FILE BYTES as they now sit on disk — never of a re-encoded
 * string. That matters because P5's `manuscript_sha256` and the backfill both hash the raw file:
 * a `readFile(..., "utf8")` round-trip replaces any byte that is not valid UTF-8 with U+FFFD, so
 * a string-derived digest would silently disagree with every other record of the same file.
 *
 * `equivalents` are the other hashes that mean "the same paper": the same bytes with the date pin
 * undone, and the bytes as they were BEFORE this run pinned them (which matters only for the odd
 * case of a file already containing both date forms, where undoing the pin does not reproduce
 * what was recorded). The token substitution runs on the BUFFER — both tokens are pure ASCII — so
 * producing a candidate cannot disturb bytes elsewhere in the file either.
 *
 * Why this is stateless, and why that is the whole point: the pin rewrites `paper.tex` without
 * changing a word of the paper, so the pinned and unpinned bytes are the same work. The rule used
 * to be expressed as "the hash this run saw before it pinned", which holds only inside the run
 * that does the pinning. An emit that pinned the file and then failed before writing meta.json —
 * a LaTeX error, a Lean build failure, an interrupted run — left a pinned file on disk beside a
 * record of the unpinned hash, and the NEXT emit, having pinned nothing itself, had no way to
 * see they were the same paper. It bumped the version and re-dated a manuscript nobody had
 * touched. All 22 shipped bundles are in exactly that starting state, so this was on the path of
 * the very first re-emit of any of them.
 */
const DATE_UNPINNED_BYTES = Buffer.from(DATE_UNPINNED, "utf8");
const DATE_PINNED_BYTES = Buffer.from(DATE_PINNED, "utf8");

/** Byte-exact token substitution: everything outside the ASCII token is passed through untouched,
 *  including bytes no UTF-8 decoder would survive. */
function replaceBytes(buf: Buffer, find: Buffer, repl: Buffer): Buffer {
  const parts: Buffer[] = [];
  for (let i = 0; ; ) {
    const at = buf.indexOf(find, i);
    if (at < 0) {
      parts.push(buf.subarray(i));
      break;
    }
    parts.push(buf.subarray(i, at), repl);
    i = at + find.length;
  }
  return parts.length === 1 ? buf : Buffer.concat(parts);
}

const sha256Bytes = (buf: Buffer) => createHash("sha256").update(buf).digest("hex");

export function manuscriptEquivalentShas(
  currentBytes: Buffer,
  prePinBytes: Buffer,
): ManuscriptShas {
  const canonical = sha256Bytes(currentBytes);
  const equivalents = [
    sha256Bytes(replaceBytes(currentBytes, DATE_PINNED_BYTES, DATE_UNPINNED_BYTES)),
    sha256Bytes(prePinBytes),
  ].filter((h) => h !== canonical);
  return { canonical, equivalents };
}

/** The hash the record now uses, plus the other hashes that identify the SAME manuscript. */
export type ManuscriptShas = { canonical: string; equivalents: string[] };

// ---------------------------------------------------------------------------
// keeping P5's report pointed at the manuscript it was written for

/** The ONE review file whose hash may be re-pointed. `p5_review_history/` is an archive of
 *  reports as they were written and is never touched. */
export const REVIEW_FILE = "p5_review.json";

/**
 * Would {@link adoptReviewManuscriptSha} rewrite this bundle's `p5_review.json`, and why?
 *
 * The pin equivalence means one manuscript has several hashes: the pinned bytes, the same bytes
 * with `\date{\today}` restored, and whatever was on disk before this run pinned. The identity
 * record adopts the CANONICAL one. A `p5_review.json` written before that adoption carries one
 * of the equivalents — the same manuscript, spelled differently — and the site compares the two
 * by raw equality (`site/src/lib/review.ts`), so the reader is told the referee read "an earlier
 * draft" of a paper that has not changed a character.
 *
 * A hash that is neither canonical nor an equivalent is a report about a genuinely different
 * manuscript, and saying so is the whole point of the field. It is left exactly as it is.
 */
export async function reviewShaNeedsAdoption(bundleDir: string, shas: ManuscriptShas): Promise<boolean> {
  const current = await currentReviewSha(bundleDir);
  if (current === null || current === shas.canonical) return false;
  return shas.equivalents.includes(current);
}

/** The stored `manuscript_sha256`, or null when there is no review, no field, or unreadable JSON. */
async function currentReviewSha(bundleDir: string): Promise<string | null> {
  const raw = await readFile(join(bundleDir, REVIEW_FILE), "utf8").catch(() => null);
  if (raw === null) return null;
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw);
  } catch {
    return null; // a report nobody can parse is not one this tool repairs
  }
  if (parsed === null || typeof parsed !== "object" || Array.isArray(parsed)) return null;
  const sha = (parsed as { manuscript_sha256?: unknown }).manuscript_sha256;
  return typeof sha === "string" ? sha : null;
}

/**
 * Re-point `p5_review.json`'s `manuscript_sha256` at the hash the identity just adopted, when it
 * already names the same manuscript under a different hash. Returns true when it rewrote.
 *
 * ONLY that field moves. The file is re-serialised from its own parse, so every other key — the
 * score, the prose, the reviewer, anything a later stage added — survives by not being named, and
 * the formatting the rest of the tree writes (2-space JSON, trailing newline) is reproduced. The
 * write is atomic: a torn review is a page of garbage on the public site.
 *
 * Callers must already hold the bundle's emit lock — this is a write to a shipped bundle.
 */
export async function adoptReviewManuscriptSha(bundleDir: string, shas: ManuscriptShas): Promise<boolean> {
  if (!(await reviewShaNeedsAdoption(bundleDir, shas))) return false;
  const path = join(bundleDir, REVIEW_FILE);
  const parsed = JSON.parse(await readFile(path, "utf8")) as Record<string, unknown>;
  parsed.manuscript_sha256 = shas.canonical;
  await writeTextAtomic(path, `${JSON.stringify(parsed, null, 2)}\n`);
  return true;
}

// ---------------------------------------------------------------------------
// the whole step, as P4 (and a future `--restamp`) performs it

/**
 * The citation identity of a bundle: exactly the `meta.json` keys P4 OWNS and may write.
 *
 * `doi`, `version_doi`, `authorship`, `score` and `score_rationale` are deliberately absent. They
 * belong to the Zenodo tool, the user and P5, and P4's only duty towards them is to leave them
 * alone — which it now does by construction, because it never names them in the merge.
 */
export type PaperIdentity = {
  wp_number: string;
  version: number;
  revised: string;
  versions: VersionEntry[];
  /** the raw stored `meta.doi` this emit's stamp was rendered against (read-only, for reporting) */
  stampedDoi: string | null;
  /** the hash this identity ADOPTED, and the other spellings of the same manuscript it displaces —
   *  what `adoptReviewManuscriptSha` needs to keep P5's report pointed at the right draft. */
  manuscriptShas: ManuscriptShas;
};

/**
 * Pin the date, settle the version, and (re)write `paper_stamp.tex` — everything the compile
 * needs, in the order it needs it. Runs BEFORE `latexmk`, because the stamp file is a compile
 * input.
 *
 * `doi` is READ from the bundle's current `meta.json` to render the stamp, and never written
 * back: it and `version_doi` belong to the Zenodo tool. A Zenodo reservation becomes immutable
 * the moment a PDF is compiled against it — the identifier is printed on page 1 of a file readers
 * may already hold, and Zenodo will not re-point a published DOI — so no stage here may clear,
 * normalise or re-derive it. Not naming them in the write is a stronger guarantee than copying
 * them forward carefully.
 *
 * Nothing in this bundle directory is removed here. In particular `zenodo.json` — the deposit
 * sidecar `bin/zenodo_deposit.ts` writes (deposition id, conceptrecid, state, environment) — is
 * neither read nor rewritten by any presentation stage, and it is not one of the P2 assembly
 * digest's authored inputs, so an emit can neither destroy it nor be blocked by it.
 */
export async function ensurePaperIdentity(args: {
  outDir: string;
  repoRoot: string;
  /** the `doc/presentation/<id>` directory name — the registry's key */
  bundleId: string;
  area: string;
  created: string;
  /** the previous `meta.json`, or `{}` on a first emit */
  prevMeta: Record<string, unknown>;
  /** the working-paper series, resolved ONCE by the caller (see local_config.paperSeriesPrefix) */
  seriesPrefix: string;
  today?: string;
}): Promise<PaperIdentity> {
  const { outDir, repoRoot, bundleId, area, created, prevMeta, seriesPrefix } = args;
  const today = args.today ?? utcToday();
  const paperPath = join(outDir, "paper.tex");

  // 1. Pin the title-block date (a no-op once done, and on any paper P2 assembled since). The
  // file is read as BYTES; the decode is only used to decide whether a pin is needed, so a file
  // that is not valid UTF-8 is never rewritten by a round-trip.
  const prePinBytes = await readFile(paperPath);
  const before = prePinBytes.toString("utf8");
  const pinned = pinDateCommand(before);
  const wrotePin = pinned !== before;
  if (wrotePin) await writeFile(paperPath, pinned, "utf8");
  const currentBytes = wrotePin ? await readFile(paperPath) : prePinBytes;

  // 2. Version: bump only when the manuscript's bytes actually moved. The equivalence is computed
  // from what is on disk NOW, so it holds whether or not this run is the one that pinned — see
  // `manuscriptEquivalentShas`.
  const { canonical: sha, equivalents } = manuscriptEquivalentShas(currentBytes, prePinBytes);
  const state = nextVersionState(prevMeta, sha, today, created, { equivalentShas: equivalents });

  // 3. Number: the REGISTRY decides, under its own shared-filesystem lock. A meta.json value is
  // only ever a claim to be checked against it — see resolveWpNumber for what disagreement does.
  const wpNumber = await resolveWpNumber(repoRoot, bundleId, created, prevMeta.wp_number, seriesPrefix);

  // Read-only: the raw stored value, used to decide what page 1 shows. Never written back.
  const doi = typeof prevMeta.doi === "string" ? prevMeta.doi : null;

  // 4. The stamp file the preamble \inputs.
  await writeFile(
    join(outDir, STAMP_FILE),
    renderStampTex({
      wpNumber,
      version: state.version,
      area,
      revised: state.revised,
      doi,
      siteUrl: paperSiteUrl(bundleId),
    }),
    "utf8",
  );

  return {
    wp_number: wpNumber, version: state.version, revised: state.revised, versions: state.versions,
    stampedDoi: doi, manuscriptShas: { canonical: sha, equivalents },
  };
}
