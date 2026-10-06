/**
 * Re-stamp a shipped paper bundle: rewrite `paper_stamp.tex`, recompile, and replace nothing else.
 *
 * ## Why a LaTeX-only path exists at all
 *
 * A concept DOI arrives AFTER the paper has been compiled and deposited, and it has to reach page
 * 1. The only two ways to get there were a full P4 re-emit — which re-runs the model, the Lean
 * build and the gates, costs hours, and is entitled to bump the version — or a hand edit of a
 * derived, digest-protected file. Neither is acceptable for "print six more characters in the
 * margin".
 *
 * So this is the third way: take the bundle exactly as it shipped, refresh the template-owned
 * macros, settle the identity, regenerate the one small VALUES file the preamble `\input`s, run
 * `latexmk`, and then PROVE that nothing but the stamp moved before any of it is allowed near the
 * real directory.
 *
 * ## The three rules that make it safe
 *
 * **1. Everything happens in a scratch copy first.** The whole bundle is copied to local disk
 * under `os.tmpdir()`, and the compile, the rewrite and the verification all run there. A failing
 * compile, a failed check or a crash therefore cannot leave the shipped bundle half-restamped —
 * the real directory is not touched until every check has passed. It is also why the copy is of
 * the WHOLE directory rather than the handful of files LaTeX names: `paper.tex` inputs `sections/`,
 * `proofs/`, the figures and the bibliography, and a compile against a partial copy would be a
 * compile of a different paper.
 *
 * **2. The version must not move.** A restamp is not a revision — the manuscript is unchanged, and
 * a bumped `v` would re-date a paper nobody edited and hand a reader a citation that disagrees
 * with the one already in circulation. `ensurePaperIdentity` already guarantees this through the
 * stateless pin equivalence (`manuscriptEquivalentShas`), so the assertion here is a tripwire, not
 * a mechanism: if the guarantee ever stops holding, this fails loudly instead of quietly
 * publishing a v3 of a v2.
 *
 * **3. The PDF is verified against the one that shipped.** Same page count; page 1 carries the
 * stamp (and the DOI, when there is a published one); pages 2..N have byte-identical TEXT. That
 * last check is the one that matters: the stamp is drawn as background shipout material, so it
 * occupies no space and must not reflow a single line. A pagination change is exactly what a
 * stale template or a moved TeX Live would produce, and it would republish a different document
 * under an unchanged version number.
 *
 * ## What it may write
 *
 * Only `paper.pdf`, `paper.tex`, `paper_macros.tex`, `paper_stamp.tex`, any `latexmk` byproduct
 * the bundle already tracks, the identity fields of `meta.json`, and — when the pin adoption
 * would otherwise strand it — the single `manuscript_sha256` field of `p5_review.json`. It never
 * reassembles (P2 re-drafts prose), never touches `p2_assembly_manifest.json`, `sections/`,
 * `proofs/`, `p5_review_history/` or `zenodo.json`, and never names `doi`, `version_doi`, `score`
 * or `authorship` in its metadata write.
 *
 * The copy-back is ATOMIC PER BUNDLE: everything is staged beside its destination and renamed
 * into place, PDF last, so an interrupt can leave the bundle unchanged or fully flipped but never
 * a truncated `paper.pdf`. See {@link flipBundleAtomically}.
 *
 * DRY RUN IS THE DEFAULT everywhere: `restampBundle` writes nothing unless `write` is set.
 */
import { execFile } from "node:child_process";
import { createHash } from "node:crypto";
import { cp, mkdtemp, open, readFile, readdir, rm } from "node:fs/promises";
import os from "node:os";
import { basename, join } from "node:path";
import process from "node:process";
import { promisify } from "node:util";
import {
  assertBundleEmitLockHeld, isHoldingBundleEmitLock, withBundleEmitLock,
} from "./emit_lock.js";
import { assertCalendarIsoDate } from "./iso_date.js";
import { readBundleMeta, updateBundleMeta } from "./meta_store.js";
import { LatexCompileError, MACROS_FILE, compilePaper, refreshPaperMacros } from "./paper_compile.js";
import {
  REVIEW_FILE, STAMP_FILE, adoptReviewManuscriptSha, areaForBundleId, ensurePaperIdentity,
  isProductionDoi, reviewShaNeedsAdoption, type VersionEntry,
} from "./paper_stamp.js";
import { readWpRegistry } from "./wp_registry.js";
import { renameWithRetry } from "../shared/json_atomic.js";
import { extractPdfPages, findDoi, type PdfPagesResult } from "../zenodo/pdf_text.js";

const execFileP = promisify(execFile);

export const PAPER_TEX = "paper.tex";
export const PAPER_PDF = "paper.pdf";

/**
 * Suffix of the staging files the copy-back writes beside their destinations.
 *
 * Gitignored (see the presentation byproducts block in the repo `.gitignore`) — a run that dies
 * between staging and rename must not leave something for `git status` to report, and the next
 * run sweeps them anyway.
 */
export const RESTAMP_TMP_SUFFIX = ".restamp-tmp";

/**
 * `latexmk` byproducts this tool is willing to refresh — and only when the bundle ALREADY tracks
 * them. Most bundles gitignore every one of these (see the LaTeX auxiliaries block in the repo
 * `.gitignore`), in which case the copy-back set is just the four paper files. A bundle that has
 * deliberately committed its `.bbl` is a different matter: leaving that stale beside a recompiled
 * PDF would be its own inconsistency.
 */
const LATEXMK_BYPRODUCTS = [
  "paper.aux", "paper.log", "paper.out", "paper.fls", "paper.fdb_latexmk",
  "paper.bbl", "paper.blg", "paper.toc", "paper.synctex.gz",
] as const;

/** Files that may ever be copied back, in report order. */
export function copyBackCandidates(tracked: ReadonlySet<string>): string[] {
  return [PAPER_PDF, PAPER_TEX, MACROS_FILE, STAMP_FILE, ...LATEXMK_BYPRODUCTS.filter((f) => tracked.has(f))];
}

export type RestampVerdict =
  /** verified, and `--write` applied the change */
  | "written"
  /** verified, and `--write` would have applied a change */
  | "would-write"
  /** verified, and there is nothing left to do (the idempotent second run) */
  | "unchanged"
  | "compile-failed"
  | "verify-failed"
  /** refused before the compile — bad `created`, no registry number, unreadable metadata */
  | "blocked";

export interface RestampResult {
  readonly bundleDir: string;
  readonly bundleId: string;
  readonly wpNumber: string | null;
  readonly version: number | null;
  readonly revised: string | null;
  /** the raw stored `meta.doi` the stamp was rendered against */
  readonly doi: string | null;
  readonly pages: number | null;
  readonly verdict: RestampVerdict;
  readonly ok: boolean;
  /** files copied back (empty on a dry run, and on an unchanged bundle) */
  readonly written: readonly string[];
  readonly detail: string;
}

export interface RestampOptions {
  /** the CausalSmith package root — the working-paper registry lives under it */
  readonly repoRoot: string;
  /** the working-paper series, resolved ONCE by the caller (`paperSeriesPrefix()`) */
  readonly seriesPrefix: string;
  /** false (the default) verifies and reports; true copies the verified result back */
  readonly write?: boolean;
  /**
   * The caller already holds this bundle's emit lock.
   *
   * The lock is NOT re-entrant — `proper-lockfile` answers `ELOCKED` to its own holder just as it
   * does to anyone else — so a caller that took it and then called in here would wait ten minutes
   * for itself and fail. When this is unset the answer is taken from the async context via
   * `isHoldingBundleEmitLock()`, which is the same signal the lock-ordering guards use, so nesting
   * is safe by default and the flag is only needed to assert a hold acquired elsewhere.
   */
  readonly emitLockHeld?: boolean;
  /** emit date; defaults to today (UTC) inside `ensurePaperIdentity` */
  readonly today?: string;
  /** test seam: the compile. Production uses `compilePaper`, exactly as P4 does. */
  readonly compile?: (outDir: string) => Promise<void>;
  /** test seam: per-page PDF text. */
  readonly readPages?: (pdfPath: string) => Promise<PdfPagesResult>;
  /** test seam: which files the bundle tracks in git. */
  readonly trackedFiles?: (bundleDir: string) => Promise<ReadonlySet<string>>;
  /** test seam: `paper.pdf` as git HEAD holds it — the self-heal hint for a corrupt shipped PDF. */
  readonly headPaperPdf?: (bundleDir: string) => Promise<Buffer | null>;
  /** test seam: fires inside the copy-back, once after every file is staged and once before each
   *  rename. Throwing from it is how a test simulates an interrupt at exactly that point. */
  readonly onFlipStep?: FlipStep;
}

/** See {@link RestampOptions.onFlipStep}. */
export type FlipStep = (step: { phase: "staged" | "rename"; name?: string }) => Promise<void> | void;

// ---------------------------------------------------------------------------
// text comparison

/**
 * Page text reduced to what a reader would call the same page: line endings unified, runs of
 * horizontal space collapsed, blank lines dropped.
 *
 * Not a byte comparison, on purpose. Two runs of the same TeX source can differ in trailing
 * spaces or in how an extractor spells a word break, and refusing a restamp over that would make
 * the tool unusable while catching nothing real. What must not differ is the sequence of words
 * per page — that is what reflow, a lost float or a changed template shows up as.
 */
export function normalizePageText(text: string): string {
  return text
    .replace(/\r\n?/g, "\n")
    .split("\n")
    .map((line) => line.replace(/[ \t   ]+/g, " ").trim())
    .filter((line) => line !== "")
    .join("\n");
}

/** Is `token` on the page, allowing for an extractor that broke it across a line? The stamp id
 *  contains no spaces, so the whitespace-stripped form is a sound second look. */
export function pageCarriesToken(pageText: string, token: string): boolean {
  if (pageText.includes(token)) return true;
  const strip = (s: string) => s.replace(/[\s­]+/g, "");
  return strip(pageText).includes(strip(token));
}

// ---------------------------------------------------------------------------

/** Names git tracks directly inside `bundleDir`. An untracked bundle (or no git at all) yields
 *  the empty set, which means "copy back the four paper files and nothing else" — the safe answer. */
async function gitTrackedNames(bundleDir: string): Promise<ReadonlySet<string>> {
  try {
    const { stdout } = await execFileP("git", ["ls-files", "-z", "--", "."], {
      cwd: bundleDir,
      maxBuffer: 16 * 1024 * 1024,
    });
    return new Set(stdout.split("\0").filter((name) => name !== ""));
  } catch {
    return new Set<string>();
  }
}

/** `paper.pdf` as git HEAD holds it, or null when git cannot produce it (no repo, untracked
 *  bundle, no commit). `HEAD:./paper.pdf` resolves relative to the cwd, so no repo-root maths. */
async function gitHeadPaperPdf(bundleDir: string): Promise<Buffer | null> {
  try {
    const { stdout } = await execFileP("git", ["show", `HEAD:./${PAPER_PDF}`], {
      cwd: bundleDir,
      encoding: "buffer",
      maxBuffer: 256 * 1024 * 1024,
    });
    return stdout.length > 0 ? stdout : null;
  } catch {
    return null;
  }
}

/** Would `extractPdfPages` have something to work with? Cheap structural screen, used only to
 *  decide whether the COMMITTED file is a plausible repair for an unreadable shipped one. */
function looksLikePdf(bytes: Buffer): boolean {
  return bytes.length > 0 && bytes.subarray(0, 1024).toString("latin1").includes("%PDF-");
}

const sha256 = (buf: Buffer) => createHash("sha256").update(buf).digest("hex");

/** Bytes of a file, or null when it is not there. */
async function readMaybe(path: string): Promise<Buffer | null> {
  return readFile(path).catch(() => null);
}

/**
 * Delete every stray `*.restamp-tmp` in the bundle. Run at the START of a restamp (self-heal: a
 * previous run may have been killed between staging and rename) and in the copy-back's `finally`.
 * Best effort by design — a tmp file nobody can delete is not a reason to refuse the restamp.
 */
async function sweepRestampTmp(bundleDir: string): Promise<void> {
  const names = await readdir(bundleDir).catch(() => [] as string[]);
  await Promise.all(
    names
      .filter((name) => name.endsWith(RESTAMP_TMP_SUFFIX))
      .map((name) => rm(join(bundleDir, name), { force: true }).catch(() => {})),
  );
}

/**
 * Replace `names` in the shipped bundle with the verified scratch copies — as ONE flip.
 *
 * `copyFile` was the wrong primitive: it TRUNCATES the destination and then streams into it, so
 * an interrupt, an ENOSPC or an NFS EIO anywhere in the middle leaves a real, shipped `paper.pdf`
 * truncated to whatever had landed. That file is then unreadable, which makes the next restamp's
 * verification fail (`shipped PDF: …`) and refuse to repair it — and in git it looks like an
 * ordinary restamp of a binary, so review sees a changed PDF and nothing else.
 *
 * So every file is written to `<bundleDir>/<name>.<pid>.restamp-tmp` FIRST — same directory,
 * therefore same filesystem, therefore `rename(2)` is atomic — fsynced, and only then renamed
 * into place. A failure before the renames leaves the bundle byte-identical; a failure between
 * two renames leaves a bundle that is internally consistent as far as it got, and the next run
 * re-derives and finishes it.
 *
 * The PDF is renamed LAST, deliberately. The sources are what a rebuild is derived FROM: a bundle
 * carrying a new `paper.pdf` beside the old `paper.tex`/`paper_stamp.tex` claims a document its
 * own sources do not produce, and the verification here compares against the shipped PDF, so it
 * would then be comparing against something nothing on disk explains.
 */
async function flipBundleAtomically(
  work: string,
  bundleDir: string,
  names: readonly string[],
  onStep?: FlipStep,
): Promise<void> {
  const ordered = [...names.filter((n) => n !== PAPER_PDF), ...names.filter((n) => n === PAPER_PDF)];
  const staged: { tmp: string; dest: string }[] = [];
  try {
    for (const name of ordered) {
      const tmp = join(bundleDir, `${name}.${process.pid}${RESTAMP_TMP_SUFFIX}`);
      const bytes = await readFile(join(work, name));
      const handle = await open(tmp, "w");
      try {
        await handle.writeFile(bytes);
        // Cheap here (a handful of small files plus one PDF) and it is the difference between
        // "the rename published the new bytes" and "the rename published a name whose data is
        // still in the page cache when the node goes down".
        await handle.sync();
      } finally {
        await handle.close();
      }
      staged.push({ tmp, dest: join(bundleDir, name) });
    }
    await onStep?.({ phase: "staged" });
    for (const { tmp, dest } of staged) {
      await onStep?.({ phase: "rename", name: basename(dest) });
      await renameWithRetry(tmp, dest);
    }
  } finally {
    // Whatever happened, no staging file survives this call — including the ones already renamed,
    // for which this is a no-op.
    await Promise.all(staged.map(({ tmp }) => rm(tmp, { force: true }).catch(() => {})));
  }
}

/**
 * Restamp one bundle.
 *
 * Takes the bundle's emit lock for the whole operation (unless the caller already holds it), for
 * the same reason P4 does: it reads `paper.pdf` and `meta.json` to decide what is true, and then
 * writes files that describe that decision. A concurrent emit in between would make the
 * verification a statement about a PDF that no longer exists.
 */
export async function restampBundle(bundleDir: string, opts: RestampOptions): Promise<RestampResult> {
  const run = () => restampInScratch(bundleDir, opts);
  if (opts.emitLockHeld ?? isHoldingBundleEmitLock(bundleDir)) return run();
  return withBundleEmitLock(bundleDir, run, { wait: true });
}

async function restampInScratch(bundleDir: string, opts: RestampOptions): Promise<RestampResult> {
  const bundleId = basename(bundleDir);
  const compile = opts.compile ?? compilePaper;
  const readPages = opts.readPages ?? extractPdfPages;
  // Self-heal before anything else: a run killed between staging and rename left `*.restamp-tmp`
  // files behind, and they are debris, not state. Sweeping here (not only in the copy-back's
  // `finally`, which that run never reached) is what makes "just run it again" the whole recovery
  // procedure. Unconditional — a DRY RUN clears them too, because they are nobody's data.
  await sweepRestampTmp(bundleDir);
  const tracked = await (opts.trackedFiles ?? gitTrackedNames)(bundleDir);

  const base = {
    bundleDir, bundleId,
    wpNumber: null as string | null, version: null as number | null, revised: null as string | null,
    doi: null as string | null, pages: null as number | null, written: [] as string[],
  };
  const blocked = (detail: string): RestampResult =>
    ({ ...base, verdict: "blocked", ok: false, detail });

  const meta = await readBundleMeta(bundleDir);
  const doi = typeof meta.doi === "string" ? meta.doi : null;
  let created: string;
  try {
    created = assertCalendarIsoDate(`${bundleId}/meta.json created`, meta.created);
  } catch (err) {
    return blocked(err instanceof Error ? err.message : String(err));
  }

  // A dry run must have NO durable effect, and `resolveWpNumber` allocates and persists a number
  // when the registry has none for this bundle. That allocation is permanent — numbers are never
  // reissued — so a preview is not allowed to cause it. A bundle in that state has never been
  // emitted with an identity; P4 or the backfill is what settles it.
  if (!opts.write) {
    const registry = await readWpRegistry(opts.repoRoot, opts.seriesPrefix);
    if (registry[bundleId] === undefined) {
      return blocked(
        `no working-paper number is recorded for ${bundleId} in the registry. Restamping it would ` +
          `MINT one, which is permanent, so the dry run refuses. Run the backfill (or P4) first.`,
      );
    }
  }

  const priorHistory: unknown[] = Array.isArray(meta.versions) ? meta.versions : [];
  const priorLastV = priorHistory.length > 0
    ? Number((priorHistory[priorHistory.length - 1] as { v?: unknown }).v)
    : 1;

  const scratch = await mkdtemp(join(os.tmpdir(), "cs-restamp-"));
  try {
    const work = join(scratch, bundleId);
    // The WHOLE bundle: paper.tex inputs sections/, proofs/, the figures and the bibliography, so
    // a partial copy would compile a different document. Lock sentinels come along harmlessly —
    // nothing in the scratch copy takes a lock.
    await cp(bundleDir, work, { recursive: true });

    await refreshPaperMacros(work);
    // Pins `\date{\today}`, settles the version, and writes paper_stamp.tex — the same call P4
    // makes, with the shipped meta.json as prior state and the REAL bundle id, so the registry
    // lookup and the site link both address the paper rather than the scratch directory.
    const identity = await ensurePaperIdentity({
      outDir: work,
      repoRoot: opts.repoRoot,
      bundleId,
      area: areaForBundleId(bundleId),
      created,
      prevMeta: meta,
      seriesPrefix: opts.seriesPrefix,
      today: opts.today,
    });

    // Tripwire, not a mechanism — see rule 2 in the module docstring.
    const expectedLength = Math.max(priorHistory.length, 1);
    if (identity.version !== priorLastV || identity.versions.length !== expectedLength) {
      throw new Error(
        `restamp: ${bundleId} would move from v${priorLastV} (${priorHistory.length} recorded ` +
          `version(s)) to v${identity.version} (${identity.versions.length}). A restamp recompiles ` +
          `an unchanged manuscript and must never bump the version: a reader already holds a PDF ` +
          `citing v${priorLastV}. Nothing was written. Investigate the pin equivalence in ` +
          `paper_stamp.ts before re-running.`,
      );
    }

    const stampId = `${identity.wp_number}v${identity.version}`;
    const row = {
      ...base,
      wpNumber: identity.wp_number,
      version: identity.version,
      revised: identity.revised,
      doi,
    };

    try {
      await compile(work);
    } catch (err) {
      if (!(err instanceof LatexCompileError)) throw err;
      return {
        ...row, verdict: "compile-failed", ok: false,
        detail: `latexmk failed; the bundle was not touched.\n${err.log.slice(-2000)}`,
      };
    }

    // ---- verification, against the PDF that actually shipped -------------------------------
    const fresh = await readPages(join(work, PAPER_PDF));
    if (fresh.pages === null) {
      return { ...row, verdict: "verify-failed", ok: false, detail: `recompiled PDF: ${fresh.reason}` };
    }
    // A zero-page document reaches here as an EMPTY array, not as a failure — `extractPdfPages`
    // separates "nobody could read it" from "it has no pages" on purpose. Indexing page 1 of it
    // used to hand `undefined` to the token check and raise a TypeError out of the middle of the
    // verifier, which is a crash where a verdict belongs.
    if (fresh.pages.length === 0) {
      return {
        ...row, verdict: "verify-failed", ok: false,
        detail: `the recompiled PDF has 0 pages (read via ${fresh.method}), so there is no page 1 to stamp.`,
      };
    }
    const shippedPdf = join(bundleDir, PAPER_PDF);
    const shipped = await readPages(shippedPdf);
    if (shipped.pages === null || shipped.pages.length === 0) {
      const why = shipped.pages === null
        ? shipped.reason
        : `it has 0 pages (read via ${shipped.method})`;
      // SELF-HEAL, or at least name the cure. An unreadable shipped PDF beside a perfectly
      // readable committed one is the signature of a copy-back that was interrupted mid-write
      // (the reason this tool no longer uses `copyFile`), and the repair is one git command —
      // not the "recompile and investigate" a generic verify-failure sends the operator to.
      const head = await (opts.headPaperPdf ?? gitHeadPaperPdf)(bundleDir);
      const detail = head !== null && looksLikePdf(head)
        ? `the SHIPPED paper.pdf is corrupt — ${why} — but git HEAD holds a readable one. ` +
          `Nothing was written. Restore it with:  git checkout -- ${shippedPdf}  and re-run.`
        : `shipped PDF: ${why}`;
      return { ...row, verdict: "verify-failed", ok: false, detail };
    }
    const verified = { ...row, pages: fresh.pages.length };

    if (fresh.pages.length !== shipped.pages.length) {
      return {
        ...verified, verdict: "verify-failed", ok: false,
        detail:
          `page count changed: the shipped paper.pdf has ${shipped.pages.length} page(s), the ` +
          `recompile has ${fresh.pages.length}. The stamp is background shipout material and ` +
          `cannot reflow the document, so this is a template or TeX-distribution difference.`,
      };
    }
    if (!pageCarriesToken(fresh.pages[0]!, stampId)) {
      return {
        ...verified, verdict: "verify-failed", ok: false,
        detail: `page 1 of the recompiled PDF does not carry the stamp "${stampId}" (read via ${fresh.method}).`,
      };
    }
    if (isProductionDoi(doi) && !findDoi(fresh.pages[0]!, doi)) {
      return {
        ...verified, verdict: "verify-failed", ok: false,
        detail: `page 1 of the recompiled PDF does not carry the published DOI ${doi} (read via ${fresh.method}).`,
      };
    }
    for (let i = 1; i < fresh.pages.length; i += 1) {
      if (normalizePageText(fresh.pages[i]!) !== normalizePageText(shipped.pages[i]!)) {
        return {
          ...verified, verdict: "verify-failed", ok: false,
          detail:
            `page ${i + 1} differs from the shipped PDF. Only page 1 may change in a restamp, so ` +
            `this recompile is not the same document — refusing to replace it.`,
        };
      }
    }

    // ---- what would actually change -------------------------------------------------------
    const candidates = copyBackCandidates(tracked);
    const changedFiles: string[] = [];
    for (const name of candidates) {
      if (name === PAPER_PDF) continue; // decided from the page text, not the bytes
      const [next, current] = await Promise.all([
        readMaybe(join(work, name)),
        readMaybe(join(bundleDir, name)),
      ]);
      if (next === null) continue; // the compile did not produce it
      if (current === null || !next.equals(current)) changedFiles.push(name);
    }
    // `latexmk` embeds a creation timestamp, so two compiles of identical sources produce
    // different BYTES. Copying on that alone would make every run "change" the bundle forever and
    // churn a 2 MB binary in git for nothing. The PDF is therefore replaced only when its page-1
    // text is not already what this restamp produces — which is the thing a reader can see.
    const page1Same = normalizePageText(shipped.pages[0]!) === normalizePageText(fresh.pages[0]!);
    const page1Stamped = pageCarriesToken(shipped.pages[0]!, stampId) &&
      (!isProductionDoi(doi) || findDoi(shipped.pages[0]!, doi));
    if (!(page1Same && page1Stamped)) changedFiles.unshift(PAPER_PDF);

    // The identity patch. `versions[-1].paper_sha256` is the hash of the PINNED paper.tex bytes —
    // the file this run is about to copy back — so the record describes the manuscript that is
    // actually on disk. P5's `manuscript_sha256` and the site both match against it.
    const pinnedSha = sha256(await readFile(join(work, PAPER_TEX)));
    const last = identity.versions[identity.versions.length - 1] as VersionEntry;
    if (last.paper_sha256 !== pinnedSha) {
      throw new Error(
        `restamp: internal inconsistency for ${bundleId} — the settled identity records ` +
          `${String(last.paper_sha256)} for v${last.v} but the pinned paper.tex hashes to ${pinnedSha}.`,
      );
    }
    const patch = {
      wp_number: identity.wp_number,
      version: identity.version,
      revised: identity.revised,
      versions: identity.versions,
    };
    const metaChanged =
      JSON.stringify([meta.wp_number, meta.version, meta.revised, meta.versions]) !==
      JSON.stringify([patch.wp_number, patch.version, patch.revised, patch.versions]);

    // P5's report names the manuscript it was written for by hash. The identity above has just
    // ADOPTED the pinned hash; a report carrying one of the equivalent spellings of the SAME
    // manuscript would then read "written for an earlier draft" on the site, which compares the
    // two by raw equality. Re-pointing that one field is part of this restamp, not a later
    // repair — see `adoptReviewManuscriptSha`, which leaves a genuinely different hash alone.
    const reviewNeedsAdoption = await reviewShaNeedsAdoption(bundleDir, identity.manuscriptShas);
    const reportedFiles = reviewNeedsAdoption ? [...changedFiles, REVIEW_FILE] : changedFiles;

    if (changedFiles.length === 0 && !metaChanged && !reviewNeedsAdoption) {
      return { ...verified, verdict: "unchanged", ok: true, detail: "already restamped; nothing to do." };
    }
    if (!opts.write) {
      return {
        ...verified, verdict: "would-write", ok: true,
        detail: `would replace ${reportedFiles.join(", ") || "(no files)"}` +
          `${metaChanged ? " and update meta.json identity" : ""}.`,
      };
    }

    // ---- the only writes this tool makes --------------------------------------------------
    // Last checkpoint before touching the shipped bundle: a lost emit lock means another process
    // may already be rewriting these files, and the verification above would describe a PDF that
    // no longer exists.
    assertBundleEmitLockHeld(bundleDir);
    try {
      await flipBundleAtomically(work, bundleDir, changedFiles, opts.onFlipStep);
    } finally {
      await sweepRestampTmp(bundleDir);
    }
    if (metaChanged) {
      // Re-reads under the bundle's own lock and merges: doi, version_doi, score, authorship and
      // every key this code has never heard of survive by simply not being named.
      await updateBundleMeta(bundleDir, (current) => { Object.assign(current, patch); });
    }
    if (reviewNeedsAdoption) await adoptReviewManuscriptSha(bundleDir, identity.manuscriptShas);
    return {
      ...verified, verdict: "written", ok: true, written: reportedFiles,
      detail: `replaced ${changedFiles.join(", ") || "(no files)"}` +
        `${metaChanged ? "; meta.json identity updated" : ""}` +
        `${reviewNeedsAdoption ? `; ${REVIEW_FILE} manuscript_sha256 re-pointed at the pinned manuscript` : ""}.`,
    };
  } finally {
    await rm(scratch, { recursive: true, force: true }).catch(() => {});
  }
}

// ---------------------------------------------------------------------------
// reporting

/** Column headings for {@link formatRestampRow}. */
export const RESTAMP_TABLE_HEADER =
  ["bundle", "number", "v", "revised", "doi", "pages", "verdict"] as const;

/** One fixed-width table row: bundle, number, version, date, doi|—, pages, verdict. */
export function formatRestampRow(r: RestampResult, bundleWidth: number): string {
  const pad = (s: string, w: number) => (s.length >= w ? s : s + " ".repeat(w - s.length));
  return [
    pad(r.bundleId, bundleWidth),
    pad(r.wpNumber ?? "—", 13),
    pad(r.version === null ? "—" : `v${r.version}`, 4),
    pad(r.revised ?? "—", 10),
    pad(r.doi ?? "—", 22),
    pad(r.pages === null ? "—" : String(r.pages), 5),
    r.verdict,
  ].join("  ");
}
