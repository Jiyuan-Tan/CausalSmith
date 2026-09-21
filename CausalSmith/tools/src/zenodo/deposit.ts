/** The deposit operations, as plain async functions over an injectable context.
 *
 * They live here rather than in `bin/zenodo_deposit.ts` so the interesting behaviour is
 * unit-testable against a fake `fetch` and a temp directory, with no process spawn.
 *
 * ## The one invariant everything serves
 *
 * **A paper has exactly one concept DOI, forever.** It is printed on page 1 of a PDF
 * that, once published, can never be corrected.
 *
 * ## How that is achieved, after two audits
 *
 * The first attempt defended the invariant with a guard at each point where it could
 * break. Each guard was right and each gap between guards was a new finding: a lost
 * response here, a concurrent process there, a status code misread as evidence. The
 * structure below replaces most of those guards with two mechanisms.
 *
 * **1. One lock per command.** Every mutating subcommand holds an exclusive per-bundle
 * lock (`.zenodo.lock`) for its whole duration, network included. Two processes cannot
 * both decide that no draft exists, because they cannot both be inside the decision.
 * Concurrency stops being something the logic reasons about.
 *
 * **2. Reconcile first.** {@link reconcile} runs at the start of every mutating
 * subcommand. It asks Zenodo what is actually true and repairs local state before
 * anything else happens. That turns the entire class of "the operation succeeded
 * remotely but the local write failed" from a set of special cases into a non-event:
 * whatever went wrong, **re-running any command fixes it**. It is also why an ambiguous
 * POST is never replayed — the operator is told to re-run, and the re-run reconciles.
 *
 * Ordering rules that fall out of this and must not be reversed:
 *  - Lock order is zenodo-lock → meta-lock, never the reverse.
 *  - `publish` writes the SIDECAR before `meta.json`: a crash between them leaves a
 *    record that reconcile can find, whereas the reverse leaves `meta.json` claiming a
 *    DOI that nothing local can locate.
 *  - DOIs and record URLs are derived locally. Values in a response are assertions to
 *    check, never things to store.
 *
 * ## The containment rule
 *
 * A sandbox DOI (prefix 10.5072) resolves to nothing. In sandbox mode results go to the
 * sidecar ONLY; `--write-meta` is required, and says so out loud.
 */

import { readFile } from "node:fs/promises";
import { createHash } from "node:crypto";
import {
  assertBundleEmitLockHeld, isBundleEmitBusy, withBundleEmitLock,
} from "../presentation/emit_lock.js";
import {
  bundleId,
  bundleMarker,
  clearDepositRecord,
  notesCarryMarker,
  metaPath,
  paperPdfPath,
  readBundleMeta,
  readSidecar,
  updateBundleMeta,
  withBundleLock,
  withCommandLock,
  writeDepositRecordUnlocked,
  UNLOCKED_HANDLE,
  type CommandLockHandle,
  type DepositEnvRecord,
} from "./bundle.js";
import { ZenodoClient, ZenodoError, isSandboxDoi, toRecordId, type Deposition } from "./client.js";
import { buildZenodoMetadata, type BuildMetadataOptions, type ZenodoMetadata } from "./metadata.js";
import { pdfContainsDoi, pdfPage1ContainsDoi } from "./pdf_text.js";

export interface DepositContext {
  readonly bundleDir: string;
  readonly client: ZenodoClient;
  /** May NEW DOIs be written into `meta.json`? False by default in sandbox mode. */
  readonly writeMeta: boolean;
  /**
   * Set only by an explicit `--no-write-meta`: meta.json must not be touched at all.
   *
   * Distinct from `writeMeta: false`, which is merely the sandbox containment default.
   * The difference matters for REPAIR: rolling a dead draft DOI back to the published
   * one is fixing a value this tool itself wrote, not publishing new information, so it
   * proceeds under the default but is refused under an explicit prohibition.
   */
  readonly metaWritesForbidden?: boolean;
  /** Publish even when the PDF's stamp cannot be confirmed. */
  readonly allowUnstamped: boolean;
  readonly siteBaseUrl: string;
  readonly repoUrl?: string;
  readonly license?: string;
  readonly communities?: readonly string[];
  readonly titlePrefix?: string;
  readonly log: (line: string) => void;
  readonly warn: (line: string) => void;
  readonly now: () => Date;
  /**
   * Replaces the real lock acquisition. Injected by tests so a compromised lock can be
   * FORCED — the abort path is otherwise unreachable without provoking a filesystem
   * fault, which means it could be deleted by a refactor and no test would notice.
   * Production never sets this.
   */
  readonly lockRunner?: LockRunner;
}

export type LockRunner = <T>(
  bundleDir: string,
  action: (lock: CommandLockHandle) => Promise<T>,
) => Promise<T>;

function markerFor(ctx: DepositContext): string {
  return bundleMarker(ctx.bundleDir, ctx.client.env.name);
}

/** Exported for `release.ts`, which previews the exact metadata `publish` would send. Building
 *  that preview any other way would let the preview and the request drift apart. */
export function metadataOptions(ctx: DepositContext): BuildMetadataOptions {
  return {
    bundleId: bundleId(ctx.bundleDir),
    siteBaseUrl: ctx.siteBaseUrl,
    repoUrl: ctx.repoUrl,
    license: ctx.license,
    communities: ctx.communities,
    titlePrefix: ctx.titlePrefix,
    marker: markerFor(ctx),
  };
}

function stamped(ctx: DepositContext, patch: Omit<DepositEnvRecord, "updated_at">): DepositEnvRecord {
  return { ...patch, updated_at: ctx.now().toISOString() };
}

function emptyRecord(ctx: DepositContext): DepositEnvRecord {
  return stamped(ctx, {
    environment: ctx.client.env.name,
    api_base: ctx.client.env.apiBase,
    conceptrecid: null,
    concept_doi: null,
    marker: markerFor(ctx),
    published: null,
    draft: null,
    pending_reserve: null,
    publishing: null,
  });
}

/** Short, bounded wait for the pipeline's emit lock: long enough to ride out the gap
 *  between two stages, short enough that an operator is told promptly rather than
 *  appearing to hang behind a multi-hour P4 emit. */
const EMIT_WAIT = { retries: 6, factor: 1, minTimeout: 500, maxTimeout: 500 };

/**
 * Hold every lock a mutating subcommand needs, in the one order that cannot deadlock.
 *
 *     emit lock  ->  zenodo command lock  ->  meta lock
 *
 * The EMIT lock is the pipeline's (`presentation/emit_lock.ts`) and is the reason a
 * deposit can trust the bytes it reads: P4 rewrites `paper.tex`, recompiles the PDF and
 * updates `meta.json` under it, so without it `publish` can pair one version's metadata
 * with another version's PDF — permanently, on a frozen record. Taking it around the
 * whole read-upload-publish sequence makes that pairing atomic with respect to P4.
 *
 * Dry-run takes NO lock at all: it sends nothing and writes nothing, so serialising it
 * buys nothing, and creating a lock sentinel would leave the one filesystem artifact a
 * dry run is not entitled to leave.
 */
async function withBundleLocks<T>(
  ctx: DepositContext,
  action: (lock: CommandLockHandle) => Promise<T>,
): Promise<T> {
  if (ctx.client.dryRun) return action(UNLOCKED_HANDLE);
  if (ctx.lockRunner) return ctx.lockRunner(ctx.bundleDir, action);
  // Losing EITHER lock invalidates the command, so both feed the same abort flag: the
  // emit lock guarantees the files are not being rewritten, the command lock guarantees
  // no second deposit is running, and neither guarantee survives its lock going away.
  try {
    return await withBundleEmitLock(
      ctx.bundleDir,
      () => withCommandLock(ctx.bundleDir, (lock) => action({
        assertHeld: () => {
          // The emit lock RECORDS a compromise rather than throwing, so it has to be
          // asked. Losing either lock invalidates the command for a different reason —
          // the emit lock guarantees the files are not being rewritten, the command
          // lock that no second deposit is running — and neither guarantee outlives its
          // lock, so both are checked at every step that has a side effect.
          assertBundleEmitLockHeld(ctx.bundleDir);
          lock.assertHeld();
        },
      })),
      { wait: true, retries: EMIT_WAIT },
    );
  } catch (err) {
    if (isBundleEmitBusy(err)) {
      throw new Error(
        `An emit of this bundle is in progress (${ctx.bundleDir}), so its paper.pdf and ` +
          `meta.json may be mid-rewrite. Nothing was read or sent. Re-run once that emit ` +
          `finishes.`,
      );
    }
    throw err;
  }
}

/** sha256 of a file's bytes, for the publish journal. */
async function sha256File(file: string): Promise<string> {
  return createHash("sha256").update(await readFile(file)).digest("hex");
}

/**
 * The version a live record says it is, from its own `metadata.version` (`vN`).
 *
 * This and the publish journal are the only admissible answers to "which version did we
 * publish". `meta.version` is not: it is mutable shared state that P4 can advance at any
 * moment, including between a publish whose response was lost and the reconcile that
 * repairs it.
 */
function versionFromLiveRecord(dep: Deposition): number | null {
  const v = (dep.metadata as { version?: unknown } | undefined)?.version;
  if (typeof v !== "string") return null;
  const m = /^v(\d+)$/.exec(v.trim());
  return m ? Number(m[1]) : null;
}

/**
 * Roll `meta.version_doi` back to the published version when it currently names a DOI
 * that has just become dead.
 *
 * Unconditional with respect to `writeMeta`: this is not publishing new information,
 * it is withdrawing a value this tool itself wrote a moment ago. Leaving it would put
 * an identifier that resolves to nothing into the live site's citation metadata. An
 * explicit `--no-write-meta` turns it into a refusal instead, naming the flag, and the
 * caller must make that check BEFORE doing the thing that kills the DOI.
 */
async function repairDeadVersionDoi(
  ctx: DepositContext,
  record: DepositEnvRecord,
  deadVersionDoi: string,
): Promise<boolean> {
  if (record.published === null || record.concept_doi === null) return false;
  const meta = await readBundleMeta(ctx.bundleDir);
  if (meta.version_doi !== deadVersionDoi) return false;
  if (ctx.metaWritesForbidden) {
    throw new Error(
      `meta.json records version DOI ${deadVersionDoi}, which no longer exists, but ` +
        `--no-write-meta forbids repairing it. Re-run without --no-write-meta so the published ` +
        `version DOI ${record.published.version_doi} can be restored. Nothing has been changed.`,
    );
  }
  await updateBundleMeta(ctx.bundleDir, (m) => {
    m.doi = record.concept_doi;
    m.version_doi = record.published!.version_doi;
  });
  ctx.log(
    `meta.json version_doi rolled back from the dead ${deadVersionDoi} to the published ` +
      `${record.published.version_doi}.`,
  );
  return true;
}

/** Refuse to touch a deposition that is not tagged for this bundle.
 *
 *  The sidecar says which deposition belongs here; this asks the deposition. Both must
 *  agree before anything irreversible happens, because a `zenodo.json` copied into
 *  another bundle is perfectly well-formed and names someone else's paper. */
function assertBelongsToBundle(ctx: DepositContext, dep: Deposition, what: string): void {
  const marker = markerFor(ctx);
  if (notesCarryMarker(dep.metadata?.notes, marker)) return;
  throw new Error(
    `Refusing to ${what}: deposition ${dep.id} does not carry this bundle's marker ` +
      `(${marker}) in its notes, so it does not belong to ${bundleId(ctx.bundleDir)}. ` +
      `This usually means a zenodo.json was copied from another bundle, or the deposition ` +
      `was re-tagged on Zenodo. Nothing has been changed.`,
  );
}

/** Persist one environment's record under the bundle lock. */
async function saveRecord(ctx: DepositContext, record: DepositEnvRecord): Promise<DepositEnvRecord> {
  await withBundleLock(ctx.bundleDir, async () => {
    await writeDepositRecordUnlocked(ctx.bundleDir, record);
  });
  return record;
}

/** The concept DOI implied by a deposition, derived locally. */
function conceptOf(ctx: DepositContext, dep: Deposition): { recid: number; doi: string } {
  const recid = toRecordId(dep.conceptrecid);
  if (recid === null) {
    throw new Error(
      `Deposition ${dep.id} carries no usable conceptrecid (${JSON.stringify(dep.conceptrecid)}), ` +
        `so its concept DOI cannot be derived. Nothing has been recorded.`,
    );
  }
  return { recid, doi: ctx.client.conceptDoi(recid) };
}

/**
 * Check what the API says a DOI is against what we derived, and refuse on disagreement.
 *
 * Response fields are NOT the source of truth — the sandbox is known to report a
 * production-prefixed `prereserve_doi`, so "what Zenodo said" has already been observed
 * to be wrong. Persisting a response value would write a DOI the PDF does not print.
 */
function assertDoiAgrees(kind: string, derived: string, reported: unknown, depId: number): void {
  if (typeof reported !== "string" || reported.length === 0) return; // absent is normal pre-publish
  if (reported === derived) return;
  throw new Error(
    `${kind} MISMATCH on deposition ${depId}: this tool derived ${derived} from the record id ` +
      `and the configured instance prefix, but Zenodo reports ${reported}. Refusing to continue ` +
      `and writing nothing — the locally derived DOI is what any already-compiled PDF was ` +
      `stamped with, so a disagreement means either the wrong instance is configured or ` +
      `Zenodo's DOI scheme has changed. Investigate before retrying.`,
  );
}

/** Apply the containment rule and, when allowed, write the DOIs into `meta.json`. */
async function maybeWriteMeta(
  ctx: DepositContext,
  conceptDoi: string,
  versionDoi: string | null,
): Promise<boolean> {
  if (ctx.client.dryRun) {
    ctx.log(`[dry-run] would set meta.json doi=${conceptDoi} version_doi=${versionDoi ?? "null"}`);
    return false;
  }
  if (!ctx.writeMeta) {
    const why = isSandboxDoi(conceptDoi)
      ? `${conceptDoi} is a SANDBOX DOI and resolves to nothing`
      : "--write-meta was not passed";
    ctx.log(
      `meta.json left untouched (${why}). The deposit is recorded in zenodo.json only; ` +
        `pass --write-meta to write the DOI into meta.json.`,
    );
    return false;
  }
  if (isSandboxDoi(conceptDoi)) {
    // REFUSE, do not warn. A bundle whose meta.json already carries a production DOI is
    // a published paper; replacing its identifier with one that resolves to nothing is
    // not something an operator should be able to do by adding --write-meta to a
    // rehearsal command.
    const existing = await readBundleMeta(ctx.bundleDir);
    for (const [field, value] of [["doi", existing.doi], ["version_doi", existing.version_doi]] as const) {
      if (typeof value === "string" && value.trim() && !isSandboxDoi(value)) {
        throw new Error(
          `Refusing to overwrite meta.${field} = ${value} with the SANDBOX DOI ${conceptDoi}. ` +
            `That DOI does not resolve, and ${value} looks like a real one. If this bundle ` +
            `genuinely has no production deposit, clear meta.${field} by hand first.`,
        );
      }
    }
    ctx.warn(
      `WRITING A SANDBOX DOI (${conceptDoi}) INTO meta.json because --write-meta was passed. ` +
        `This DOI does not resolve; it must not reach the live site.`,
    );
  }
  await updateBundleMeta(ctx.bundleDir, (meta) => {
    meta.doi = conceptDoi;
    meta.version_doi = versionDoi;
  });
  ctx.log(`meta.json updated: doi=${conceptDoi} version_doi=${versionDoi ?? "null"}`);
  return true;
}

// ---------------------------------------------------------------------------
// reconcile
// ---------------------------------------------------------------------------

export interface ReconcileResult {
  readonly record: DepositEnvRecord | null;
  /** Human-readable repairs performed, empty when local state was already correct. */
  readonly repairs: readonly string[];
}

/**
 * Make local state agree with Zenodo before any command acts on it.
 *
 * Runs at the start of every mutating subcommand and of `status --repair`. It is
 * idempotent, performs no creation of any kind, and handles the four ways local and
 * remote state can disagree:
 *
 *  (i)   a recorded DRAFT that Zenodo has already published → record it as published
 *        (this is the "publish succeeded, the response was lost" case);
 *  (ii)  a PUBLISHED record whose `links.latest_draft` exists while we have no draft →
 *        adopt that draft (the "new-version succeeded, the response was lost" case);
 *  (iii) a PENDING journal entry with nothing recorded → marker search and adopt;
 *  (iv)  a recorded draft that 404s → refuse loudly if a concept DOI is already tied to
 *        it, otherwise clear it.
 *
 * (iv) is a refusal rather than a repair on purpose. A concept DOI whose draft has
 * vanished cannot be re-created — Zenodo would mint a different one — so any PDF
 * already stamped with it is unrecoverable by this tool. Deciding what to do is a
 * human's call, and the previous code made it by creating a replacement deposit and
 * only then discovering it was not allowed to, leaving a fresh orphan on every retry.
 */
export async function reconcile(
  ctx: DepositContext,
  opts: {
    /**
     * Do not throw when a FIRST reservation's draft has vanished.
     *
     * Set only by `abandon --discard-stamped-doi`, which is the remedy that refusal
     * tells the operator to use — so reconcile refusing first made the advice
     * impossible to follow. The caller still has to do the cleanup; all this does is
     * decline to block it.
     */
    readonly allowVanishedFirstReservation?: boolean;
  } = {},
): Promise<ReconcileResult> {
  const env = ctx.client.env.name;
  const repairs: string[] = [];
  if (ctx.client.dryRun) {
    const sidecar = await readSidecar(ctx.bundleDir);
    return { record: sidecar[env] ?? null, repairs };
  }

  let record = (await readSidecar(ctx.bundleDir))[env] ?? null;
  if (!record) return { record: null, repairs };

  // (i) + (iv): a recorded draft may have been published, or may be gone.
  if (record.draft) {
    const live = await ctx.client.getDepositionOrNull(record.draft.deposition_id);
    if (live === null) {
      if (record.published !== null) {
        // A REVISION draft that vanished is harmless: the published version still holds
        // the concept DOI, so nothing permanent is lost and there is nothing to refuse.
        // The earlier code refused here too, which bricked the bundle — every later
        // command failed, and the advice it printed (delete the sidecar entry) would
        // have erased the only record that v1 existed.
        const dead = record.draft.version_doi;
        const stillPublished = record.published.version_doi;
        // Decide the meta repair BEFORE clearing, while `record` still describes it.
        await repairDeadVersionDoi(ctx, record, dead);
        record = stamped(ctx, { ...record, draft: null, publishing: null });
        await saveRecord(ctx, record);
        repairs.push(
          `cleared revision draft ${dead} which no longer exists on Zenodo; ` +
            `version ${stillPublished} remains published`,
        );
      } else if (record.concept_doi && opts.allowVanishedFirstReservation) {
        ctx.warn(
          `The recorded ${env} draft ${record.draft.deposition_id} no longer exists on Zenodo; ` +
            `continuing because --discard-stamped-doi was passed.`,
        );
      } else if (record.concept_doi) {
        throw new Error(
          `The recorded ${env} draft ${record.draft.deposition_id} no longer exists on Zenodo, ` +
            `but this bundle already holds concept DOI ${record.concept_doi} and has nothing ` +
            `published. Refusing to continue and creating nothing.\n\n` +
            `A concept DOI cannot be re-created: a new draft would carry a DIFFERENT one, so ` +
            `any PDF already compiled with ${record.concept_doi} would print an identifier ` +
            `that resolves to nothing and would have to be recompiled and redistributed.\n\n` +
            `Resolve this by hand: look for the draft in the Zenodo UI at ` +
            `${ctx.client.env.webBase}/me/uploads?q=&f=is_published%3Afalse — it may have been ` +
            `deleted there. If it is genuinely gone AND you are certain no PDF stamped with ` +
            `${record.concept_doi} has been distributed, run 'abandon --discard-stamped-doi' ` +
            `to give up that DOI deliberately, then 'reserve' for a new one.`,
        );
      } else {
        record = stamped(ctx, { ...record, draft: null, publishing: null });
        await saveRecord(ctx, record);
        repairs.push(`cleared a recorded draft that no longer exists on Zenodo`);
      }
    } else if (live.submitted === true || live.state === "done") {
      assertBelongsToBundle(ctx, live, "record deposition as published");
      const { recid, doi } = conceptOf(ctx, live);
      if (record.concept_doi && doi !== record.concept_doi) {
        throw new Error(
          `Deposition ${live.id} is published under concept DOI ${doi}, but this bundle ` +
            `reserved ${record.concept_doi}. Refusing to record it; investigate before retrying.`,
        );
      }
      assertDoiAgrees("Concept DOI", doi, live.conceptdoi, live.id);
      const versionDoi = ctx.client.versionDoi(live.id);
      assertDoiAgrees("Version DOI", versionDoi, live.doi, live.id);
      // NOT `meta.version`: see versionFromLiveRecord. The journal written before the
      // publish POST is the first-choice evidence; the record's own metadata is the
      // second; there is no third, and guessing is worse than recording null.
      const publishedVersion = record.publishing?.version ?? versionFromLiveRecord(live);
      record = stamped(ctx, {
        ...record,
        conceptrecid: recid,
        concept_doi: doi,
        publishing: null,
        published: {
          deposition_id: live.id,
          version_doi: versionDoi,
          published_version: publishedVersion,
          // Locally derived: never the response's own link.
          record_url: ctx.client.recordUrl(live.id),
          published_at: ctx.now().toISOString(),
        },
        draft: null,
        pending_reserve: null,
      });
      await saveRecord(ctx, record);
      repairs.push(
        `deposition ${live.id} was already published on Zenodo (${versionDoi}); recorded it`,
      );
      await maybeWriteMeta(ctx, doi, versionDoi);
    }
  }

  // (ii) a published record may already have an edit draft we never recorded.
  if (record.published && !record.draft) {
    const live = await ctx.client.getDepositionOrNull(record.published.deposition_id);
    if (live === null) {
      // Distinct from "there is no latest draft". A published record that cannot be
      // fetched means the token lost access, the instance is wrong, or the record was
      // withdrawn — none of which may be silently continued from.
      throw new Error(
        `The published ${env} record ${record.published.deposition_id} ` +
          `(${record.published.version_doi}) could not be fetched from Zenodo (404). A ` +
          `published record does not simply disappear, so this means the token no longer has ` +
          `access, the configured instance is wrong, or the record was withdrawn. Refusing to ` +
          `continue from unverified local state; nothing has been changed.`,
      );
    }
    const latest = live.links?.latest_draft;
    if (latest) {
      // Probed: for a published record with NO open draft, Zenodo returns
      // links.latest_draft ANYWAY, pointing at the published record itself (200,
      // submitted:true). And after a revision draft is deleted the link still names it,
      // now 404. Both are normal, so the link is followed tolerantly and only an
      // unpublished, different deposition is adopted.
      const draft = await ctx.client.getByUrlOrNull(latest);
      if (draft && draft.submitted === false && draft.id !== record.published.deposition_id) {
        assertBelongsToBundle(ctx, draft, "adopt the open revision draft");
        const { recid, doi } = conceptOf(ctx, draft);
        if (record.concept_doi && doi !== record.concept_doi) {
          throw new Error(
            `The existing edit draft ${draft.id} derives concept DOI ${doi}, not ` +
              `${record.concept_doi}. Refusing to adopt it.`,
          );
        }
        record = stamped(ctx, {
          ...record,
          conceptrecid: recid,
          concept_doi: doi,
          draft: {
            deposition_id: draft.id,
            version_doi: ctx.client.versionDoi(draft.id),
            opened_at: ctx.now().toISOString(),
          },
          pending_reserve: null,
        });
        await saveRecord(ctx, record);
        repairs.push(`adopted the already-open revision draft ${draft.id}`);
      }
    }
  }

  // (iii) a pending reserve with nothing recorded: look for the orphan it may have made.
  if (record.pending_reserve && !record.draft && !record.published) {
    const marker = markerFor(ctx);
    const orphans = await findOrphans(ctx, marker);
    if (orphans.length === 1) {
      const draft = orphans[0];
      assertBelongsToBundle(ctx, draft, "adopt the orphaned draft");
      const { recid, doi } = conceptOf(ctx, draft);
      if (record.concept_doi && doi !== record.concept_doi) {
        throw new Error(
          `The orphaned draft ${draft.id} derives concept DOI ${doi}, but this bundle holds ` +
            `${record.concept_doi}. Refusing to adopt it; nothing has been changed.`,
        );
      }
      record = stamped(ctx, {
        ...record,
        conceptrecid: recid,
        concept_doi: doi,
        draft: {
          deposition_id: draft.id,
          version_doi: ctx.client.versionDoi(draft.id),
          opened_at: ctx.now().toISOString(),
        },
        pending_reserve: null,
      });
      await saveRecord(ctx, record);
      repairs.push(`adopted orphaned draft ${draft.id} left by an interrupted reserve`);
    }
  }

  for (const r of repairs) ctx.warn(`reconciled: ${r}`);
  return { record, repairs };
}

/** Marker search with the multiple-match refusal every caller needs. */
async function findOrphans(ctx: DepositContext, marker: string): Promise<Deposition[]> {
  const found = await ctx.client.findDraftsByMarker(marker);
  // The client already filters; re-check locally so the rule lives beside its reason.
  const exact = found.filter((d) => notesCarryMarker(d.metadata?.notes, marker));
  if (exact.length > 1) {
    throw new Error(
      `Found ${exact.length} unpublished Zenodo drafts marked ${marker} ` +
        `(ids ${exact.map((o) => o.id).join(", ")}). Refusing to guess which one owns this ` +
        `paper's concept DOI — delete the spurious ones in the Zenodo UI, then re-run.`,
    );
  }
  return exact;
}

// ---------------------------------------------------------------------------
// reserve
// ---------------------------------------------------------------------------

export interface ReserveResult {
  readonly record: DepositEnvRecord;
  readonly reused: boolean;
  readonly metaWritten: boolean;
}

/**
 * Open (or re-find) the draft that owns this paper's concept DOI.
 *
 * Creation is the last resort, reached only when reconcile found nothing, the sidecar
 * holds nothing, and a marker search of the account turns up nothing. The pending
 * journal is written and flushed BEFORE the create request leaves, so a process killed
 * mid-create still leaves a note that a draft for this marker may exist.
 */
export async function reserve(
  ctx: DepositContext,
  opts: { readonly confirmNoRemoteDraft?: boolean } = {},
): Promise<ReserveResult> {
  return withBundleLocks(ctx, (lock) => reserveLocked(ctx, opts, lock));
}

async function reserveLocked(
  ctx: DepositContext,
  opts: { readonly confirmNoRemoteDraft?: boolean },
  lock: CommandLockHandle,
): Promise<ReserveResult> {
  const env = ctx.client.env.name;
  const marker = markerFor(ctx);

  if (ctx.client.dryRun) {
    const existing = (await readSidecar(ctx.bundleDir))[env];
    if (existing?.published) {
      ctx.log(`[dry-run] ${existing.concept_doi} is already published; nothing to reserve.`);
      return { record: existing, reused: true, metaWritten: false };
    }
    if (existing?.draft) {
      ctx.log(`[dry-run] would reuse recorded draft ${existing.draft.deposition_id}.`);
      return { record: existing, reused: true, metaWritten: false };
    }
    ctx.log(`[dry-run] would look for an orphaned draft marked ${marker}, then create one.`);
    await ctx.client.findDraftsByMarker(marker);
    await ctx.client.createDraft();
    return { record: existing ?? emptyRecord(ctx), reused: false, metaWritten: false };
  }

  const { record: reconciled } = await reconcile(ctx);

  if (reconciled?.published) {
    ctx.log(
      `Already published on ${env}: ${reconciled.concept_doi} ` +
        `(version ${reconciled.published.version_doi}). Use 'new-version' to deposit a revision.`,
    );
    return { record: reconciled, reused: true, metaWritten: false };
  }

  if (reconciled?.draft) {
    const doi = reconciled.concept_doi!;
    ctx.log(`Reusing draft ${reconciled.draft.deposition_id}; concept DOI ${doi}.`);
    const metaWritten = await maybeWriteMeta(ctx, doi, reconciled.draft.version_doi);
    return { record: reconciled, reused: true, metaWritten };
  }

  // A concept DOI with neither a draft nor a published version means an earlier
  // reservation was lost without being deliberately given up. Creating now would mint a
  // second one, so refuse BEFORE the search rather than after it.
  if (reconciled?.concept_doi && !reconciled.draft && !reconciled.published) {
    throw new Error(
      `This bundle already holds concept DOI ${reconciled.concept_doi} on ${env}, but no draft ` +
        `and no published version remain for it. Creating a new draft would mint a SECOND ` +
        `permanent concept DOI, so nothing has been created.\n\n` +
        `If a PDF stamped with ${reconciled.concept_doi} may have been distributed, recover the ` +
        `draft in the Zenodo UI. If not, run 'abandon --discard-stamped-doi' to give that DOI ` +
        `up deliberately, then 'reserve'.`,
    );
  }

  // Nothing recorded. Search the account before creating anything.
  const orphans = await findOrphans(ctx, marker);
  let draft: Deposition;
  let adopted = false;
  if (orphans.length === 1) {
    draft = orphans[0];
    assertBelongsToBundle(ctx, draft, "adopt the orphaned draft");
    adopted = true;
    ctx.warn(
      `Adopted orphaned draft ${draft.id} marked ${marker} — a previous run created it but did ` +
        `not record it. No new draft was created, so the concept DOI is unchanged.`,
    );
  } else if (reconciled?.pending_reserve && !opts.confirmNoRemoteDraft) {
    // AN EMPTY SEARCH IS NOT PROOF. A journal entry says a create was attempted and its
    // outcome was never learned; a search that returns nothing says only that nothing
    // MATCHING IS INDEXED YET. Zenodo's deposit search is an index over a separate
    // store and it lags writes by an unknown amount, so "created successfully, then the
    // connection dropped, then we searched immediately" produces exactly this state —
    // and creating here mints a second permanent concept DOI for a paper that already
    // has one, with the first left unrecorded and unfindable.
    throw new Error(
      `A previous 'reserve' for ${bundleId(ctx.bundleDir)} was interrupted ` +
        `(started ${reconciled.pending_reserve.started_at}) and its outcome is unknown. The ` +
        `marker search found no matching draft, but that is NOT evidence that no draft was ` +
        `created: Zenodo's deposit search is an index and it lags writes, so a draft created ` +
        `moments ago may simply not be visible yet.\n\n` +
        `Refusing to create a second deposit, because that would mint a second permanent ` +
        `concept DOI for this paper.\n\n` +
        `What to do: check this account's unpublished drafts at ` +
        `${ctx.client.env.webBase}/me/uploads?q=&f=is_published%3Afalse for one marked ` +
        `${marker}, then re-run 'reserve' — it will adopt it. If a few minutes have passed ` +
        `and no such draft exists, re-run with --confirm-no-remote-draft to create one.`,
    );
  } else {
    if (reconciled?.pending_reserve && opts.confirmNoRemoteDraft) {
      ctx.warn(
        `--confirm-no-remote-draft: creating a new draft although an earlier reserve's outcome ` +
          `was never confirmed. If that earlier create did succeed, its draft is now an ` +
          `unreferenced orphan on the account and should be deleted by hand.`,
      );
    }
    // Journal FIRST, and make sure it is on disk, so a crash inside the create leaves a
    // breadcrumb that reconcile can act on.
    const base = (await readSidecar(ctx.bundleDir))[env] ?? emptyRecord(ctx);
    await saveRecord(ctx, stamped(ctx, {
      ...base,
      marker,
      pending_reserve: { marker, started_at: ctx.now().toISOString() },
    }));
    lock.assertHeld();
    draft = await ctx.client.createDraft(reservationMetadata(ctx));
  }

  const { recid, doi } = conceptOf(ctx, draft);
  assertDoiAgrees("Concept DOI", doi, draft.conceptdoi, draft.id);
  const versionDoi = ctx.client.versionDoi(draft.id);

  const base = (await readSidecar(ctx.bundleDir))[env] ?? emptyRecord(ctx);
  if (base.concept_doi && base.concept_doi !== doi) {
    throw new Error(
      `This bundle already has concept DOI ${base.concept_doi} on ${env}; refusing to replace ` +
        `it with ${doi}. A concept DOI is permanent once a PDF may have been stamped with it.`,
    );
  }
  const record = stamped(ctx, {
    ...base,
    conceptrecid: recid,
    concept_doi: doi,
    marker,
    draft: { deposition_id: draft.id, version_doi: versionDoi, opened_at: ctx.now().toISOString() },
    pending_reserve: null,
  });
  await saveRecord(ctx, record);

  ctx.log(
    `${adopted ? "Adopted" : "Reserved"} ${env} draft ${draft.id}: concept DOI ${doi}, ` +
      `version DOI ${versionDoi} (both unregistered until publish).`,
  );
  const metaWritten = await maybeWriteMeta(ctx, doi, versionDoi);
  return { record, reused: adopted, metaWritten };
}

/** Minimal metadata attached at creation time, carrying the marker that makes the draft
 *  findable. `buildZenodoMetadata` appends the same marker line, so it survives the
 *  wholesale metadata replacement at publish time. */
function reservationMetadata(ctx: DepositContext): Record<string, unknown> {
  return {
    upload_type: "publication",
    publication_type: "workingpaper",
    title: `${ctx.titlePrefix ?? ""}CausalSmith reservation — ${bundleId(ctx.bundleDir)}`,
    description: "<p>DOI reserved; descriptive metadata is set when the paper is published.</p>",
    creators: [{ name: "CausalSmith" }],
    notes: markerFor(ctx),
  };
}

// ---------------------------------------------------------------------------
// publish
// ---------------------------------------------------------------------------

export interface PublishResult {
  readonly record: DepositEnvRecord;
  readonly metadata: ZenodoMetadata;
  readonly alreadyPublished: boolean;
  readonly metaWritten: boolean;
}

/**
 * Refuse to publish a PDF whose printed DOI is not the one being registered.
 *
 * `absent` and `unavailable` BOTH refuse. They are different failures — "the stamp is
 * missing" versus "nobody could read the file" — and get different messages, because
 * the fixes differ. What they share is that neither is evidence the PDF is correctly
 * stamped, and publishing is irreversible.
 *
 * PAGE 1 ONLY. The stamp is drawn on page 1; a DOI found in the bibliography or an
 * acknowledgement on page 9 is somebody else's identifier and is no evidence at all.
 * `pdfPage1ContainsDoi` falls back to the whole document only when nobody can split the
 * file into pages, and labels the method when it does.
 */
async function assertStamped(ctx: DepositContext, pdf: string, conceptDoi: string): Promise<void> {
  const check = await pdfPage1ContainsDoi(pdf, conceptDoi);
  if (check.outcome === "present") {
    ctx.log(`Stamp check: ${conceptDoi} found in ${pdf} (via ${check.method}).`);
    return;
  }
  if (check.outcome === "unavailable") {
    if (ctx.allowUnstamped) {
      ctx.warn(
        `!! Publishing WITHOUT a stamp check: ${check.reason}. --allow-unstamped was passed. ` +
          `If the PDF prints the wrong DOI, the published paper is permanently wrong.`,
      );
      return;
    }
    throw new Error(
      `Refusing to publish: the stamp could not be verified because ${check.reason}. ` +
        `Install poppler (pdftotext) or ghostscript, or repair the PDF, so the check can run. ` +
        `Pass --allow-unstamped only if you are certain the PDF is correct.`,
    );
  }
  if (ctx.allowUnstamped) {
    ctx.warn(
      `!! Publishing an UNSTAMPED PDF: ${pdf} does not contain ${conceptDoi} ` +
        `(checked via ${check.method}) and --allow-unstamped was passed.`,
    );
    return;
  }
  throw new Error(
    `Refusing to publish: ${pdf} does not contain the DOI it would be published under ` +
      `(${conceptDoi}), checked via ${check.method}. Recompile the paper with the DOI ` +
      `stamped on page 1, or pass --allow-unstamped if the stamp is deliberately absent.` +
      (check.method.startsWith("PyMuPDF") ? "" :
        `\n\nNote: ${check.method} does not keep the rotated margin stamp on one line — it ` +
        `interleaves it with body text — so a correctly stamped paper can be refused when the ` +
        `text abutting the DOI begins with a digit. Installing PyMuPDF (pip install pymupdf) ` +
        `makes this check read the stamp as one string and is the preferred extractor.`),
  );
}

export async function publish(ctx: DepositContext): Promise<PublishResult> {
  return withBundleLocks(ctx, (lock) => publishLocked(ctx, lock));
}

async function publishLocked(ctx: DepositContext, lock: CommandLockHandle): Promise<PublishResult> {
  const env = ctx.client.env.name;
  // Read under the emit lock: from here to the publish POST, P4 cannot rewrite either
  // of these files, so the metadata and the PDF are guaranteed to be one emit's output.
  const meta = await readBundleMeta(ctx.bundleDir);
  const metadata = buildZenodoMetadata(meta, metadataOptions(ctx));

  const record = ctx.client.dryRun
    ? (await readSidecar(ctx.bundleDir))[env] ?? null
    : (await reconcile(ctx)).record;

  if (!record) {
    throw new Error(
      `No ${env} deposit recorded for ${ctx.bundleDir}. Run 'reserve' first — publishing ` +
        `without a reservation would mint a concept DOI that the PDF cannot already carry.`,
    );
  }

  if (!record.draft) {
    if (record.published) {
      // Idempotent repair rather than an early return: a previous run may have
      // published and then failed before writing meta.json.
      ctx.log(
        `Version ${record.published.version_doi} is already published and no revision draft is ` +
          `open. Nothing to publish; re-asserting local state.`,
      );
      const metaWritten = await maybeWriteMeta(
        ctx, record.concept_doi!, record.published.version_doi,
      );
      return { record, metadata, alreadyPublished: true, metaWritten };
    }
    throw new Error(`No open ${env} draft for ${ctx.bundleDir}. Run 'reserve' first.`);
  }
  if (!record.concept_doi) {
    throw new Error(`The ${env} record for ${ctx.bundleDir} has no concept DOI. Re-run 'reserve'.`);
  }

  const pdf = paperPdfPath(ctx.bundleDir);
  const bytes = await readFile(pdf).catch(() => {
    throw new Error(`No paper.pdf in ${ctx.bundleDir} — compile the paper before publishing.`);
  });
  await assertStamped(ctx, pdf, record.concept_doi);

  if (ctx.client.dryRun) {
    ctx.log(`[dry-run] would upload ${pdf} (${bytes.byteLength} bytes), set metadata, and publish.`);
    ctx.log(`[dry-run] metadata: ${JSON.stringify(metadata, null, 2)}`);
    return { record, metadata, alreadyPublished: false, metaWritten: false };
  }

  const depId = record.draft.deposition_id;
  const draft = await ctx.client.getDeposition(depId);
  assertBelongsToBundle(ctx, draft, "publish into this draft");
  const bucket = draft.links?.bucket;
  if (!bucket) throw new Error(`Deposition ${depId} has no links.bucket; cannot upload the PDF.`);

  const pre = conceptOf(ctx, draft);
  if (pre.doi !== record.concept_doi) {
    throw new Error(
      `Deposition ${depId} now derives concept DOI ${pre.doi}, but this bundle reserved ` +
        `${record.concept_doi}. Refusing to publish; nothing has been changed.`,
    );
  }

  // Journal the exact inputs BEFORE anything irreversible. If the publish succeeds and
  // the response is lost, this is what tells a later reconcile which version was
  // published — `meta.version` will by then answer a different question.
  const journal = {
    version: typeof meta.version === "number" && Number.isInteger(meta.version) ? meta.version : null,
    paper_sha256: createHash("sha256").update(bytes).digest("hex"),
    meta_sha256: await sha256File(metaPath(ctx.bundleDir)),
    started_at: ctx.now().toISOString(),
  };
  await saveRecord(ctx, stamped(ctx, { ...record, publishing: journal }));

  lock.assertHeld();
  const uploaded = await ctx.client.uploadFile(bucket, "paper.pdf", bytes);
  ctx.log(`Uploaded paper.pdf (${uploaded.size} bytes, ${uploaded.checksum}).`);

  lock.assertHeld();
  await ctx.client.updateMetadata(depId, metadata as unknown as Record<string, unknown>);
  ctx.log(`Metadata set on deposition ${depId}.`);

  lock.assertHeld();
  const published = await ctx.client.publish(depId);

  const post = conceptOf(ctx, published);
  assertDoiAgrees("Concept DOI", record.concept_doi, published.conceptdoi, published.id);
  if (post.doi !== record.concept_doi) {
    throw new Error(
      `Published deposition ${published.id} derives concept DOI ${post.doi}, not the reserved ` +
        `${record.concept_doi}. The record IS public; do not re-run blindly. Investigate — ` +
        `anything stamped with the reserved DOI is now wrong.`,
    );
  }
  const versionDoi = ctx.client.versionDoi(published.id);
  assertDoiAgrees("Version DOI", versionDoi, published.doi, published.id);

  // SIDECAR FIRST. See the module docstring: a crash between these two writes must
  // leave something reconcile can find, and meta.json is not that.
  const next = stamped(ctx, {
    ...record,
    conceptrecid: post.recid,
    concept_doi: record.concept_doi,
    published: {
      deposition_id: published.id,
      version_doi: versionDoi,
      published_version: journal.version,
      record_url: ctx.client.recordUrl(published.id),
      published_at: ctx.now().toISOString(),
    },
    draft: null,
    pending_reserve: null,
    publishing: null,
  });
  await saveRecord(ctx, next);
  ctx.log(
    `Published: ${next.published!.record_url} — concept ${next.concept_doi}, version ${versionDoi}.`,
  );

  const metaWritten = await maybeWriteMeta(ctx, next.concept_doi!, versionDoi);
  return { record: next, metadata, alreadyPublished: false, metaWritten };
}

// ---------------------------------------------------------------------------
// new-version
// ---------------------------------------------------------------------------

export interface NewVersionResult {
  readonly record: DepositEnvRecord;
  readonly metaWritten: boolean;
}

/**
 * Open a draft for the next version of an already-published paper.
 *
 * The concept DOI does NOT move, so the page-1 stamp from the previous version stays
 * correct and only the version DOI is new. The new draft inherits the previous
 * version's files; `publish` PUTs `paper.pdf` over the inherited one.
 *
 * Reconcile runs first, which is what makes this safe after a lost response: if the
 * previous attempt's POST actually opened a draft, reconcile adopts it via
 * `links.latest_draft` and this function finds the work already done.
 */
export async function newVersion(
  ctx: DepositContext,
  opts: { readonly force?: boolean } = {},
): Promise<NewVersionResult> {
  return withBundleLocks(ctx, (lock) => newVersionLocked(ctx, opts, lock));
}

async function newVersionLocked(
  ctx: DepositContext,
  opts: { readonly force?: boolean },
  lock: CommandLockHandle,
): Promise<NewVersionResult> {
  const env = ctx.client.env.name;
  const record = ctx.client.dryRun
    ? (await readSidecar(ctx.bundleDir))[env] ?? null
    : (await reconcile(ctx)).record;

  if (!record) throw new Error(`No ${env} deposit recorded for ${ctx.bundleDir}; nothing to version.`);
  if (!record.published) {
    throw new Error(
      `Nothing is published on ${env} for ${ctx.bundleDir}` +
        (record.draft
          ? `, only draft ${record.draft.deposition_id}. Publish it (or 'abandon' it) rather ` +
            `than opening a new version of it.`
          : `. Run 'reserve' and 'publish' first.`),
    );
  }
  if (record.draft) {
    // Reconcile may have just adopted a draft opened by a previous, ambiguous attempt.
    ctx.log(
      `A ${env} revision draft (${record.draft.deposition_id}) is already open; reserved ` +
        `version DOI ${record.draft.version_doi}. Run 'publish' once paper.pdf is rebuilt.`,
    );
    const metaWritten = await maybeWriteMeta(ctx, record.concept_doi!, record.draft.version_doi);
    return { record, metaWritten };
  }

  const meta = await readBundleMeta(ctx.bundleDir);
  const current = meta.version;
  const publishedAt = record.published.published_version;
  if (typeof current !== "number" || !Number.isInteger(current) || current < 1) {
    throw new Error(
      `meta.version must be an integer >= 1 to open a new version, but it is ` +
        `${JSON.stringify(current)}. A version DOI that does not correspond to a declared ` +
        `version is unciteable; set meta.version first.`,
    );
  }
  if (!opts.force) {
    if (typeof publishedAt !== "number" || !Number.isInteger(publishedAt)) {
      throw new Error(
        `The published ${env} record does not record which version it was ` +
          `(published_version=${JSON.stringify(publishedAt)}), so no advance can be demonstrated. ` +
          `Re-check the record and pass --force if you are certain a new version is warranted.`,
      );
    }
    if (current <= publishedAt) {
      throw new Error(
        `meta.version is ${current} and version ${publishedAt} is already published, so there is ` +
          `nothing new to deposit. Bump meta.version first, or pass --force.`,
      );
    }
  }

  if (ctx.client.dryRun) {
    ctx.log(`[dry-run] would open a new version of deposition ${record.published.deposition_id}.`);
    await ctx.client.newVersion(record.published.deposition_id);
    return { record, metaWritten: false };
  }

  // Check the PARENT's identity before the POST, not just the draft's afterwards: a
  // new-version POST against another paper's record is itself the damage.
  const parent = await ctx.client.getDeposition(record.published.deposition_id);
  assertBelongsToBundle(ctx, parent, "open a new version of this record");

  lock.assertHeld();
  const draft = await ctx.client.newVersion(record.published.deposition_id);
  assertBelongsToBundle(ctx, draft, "open a new version of this record");
  const { recid, doi } = conceptOf(ctx, draft);
  if (doi !== record.concept_doi) {
    throw new Error(
      `The new-version draft ${draft.id} derives concept DOI ${doi}, not ${record.concept_doi}. ` +
        `That should be impossible. Nothing has been recorded; inspect the record on Zenodo and ` +
        `delete the stray draft before retrying.`,
    );
  }
  assertDoiAgrees("Concept DOI", doi, draft.conceptdoi, draft.id);
  const versionDoi = ctx.client.versionDoi(draft.id);

  const next = stamped(ctx, {
    ...record,
    conceptrecid: recid,
    concept_doi: doi,
    // `published` is untouched: it keeps v1 citable while v2 is drafted.
    draft: { deposition_id: draft.id, version_doi: versionDoi, opened_at: ctx.now().toISOString() },
    pending_reserve: null,
  });
  await saveRecord(ctx, next);

  ctx.log(
    `New version draft ${draft.id} opened. Concept DOI unchanged (${doi}); reserved version DOI ` +
      `${versionDoi}. Version ${record.published.version_doi} stays published. Run 'publish' ` +
      `once paper.pdf is rebuilt.`,
  );
  const metaWritten = await maybeWriteMeta(ctx, doi, versionDoi);
  return { record: next, metaWritten };
}

// ---------------------------------------------------------------------------
// status
// ---------------------------------------------------------------------------

export interface StatusResult {
  readonly record: DepositEnvRecord | null;
  readonly live: Deposition | null;
  readonly meta: { doi: unknown; version_doi: unknown; version: unknown };
  readonly repairs: readonly string[];
}

/** Read-only by default; `--repair` runs {@link reconcile} first. */
export async function status(
  ctx: DepositContext,
  opts: { readonly repair?: boolean } = {},
): Promise<StatusResult> {
  const env = ctx.client.env.name;
  let repairs: readonly string[] = [];
  if (opts.repair && !ctx.client.dryRun) {
    repairs = (await withBundleLocks(ctx, () => reconcile(ctx))).repairs;
    if (repairs.length === 0) ctx.log("reconcile: local state already matches Zenodo.");
  }

  const record = (await readSidecar(ctx.bundleDir))[env] ?? null;
  const meta = await readBundleMeta(ctx.bundleDir);
  const summary = {
    doi: meta.doi ?? null,
    version_doi: meta.version_doi ?? null,
    version: meta.version ?? null,
  };

  if (!record) {
    ctx.log(`No ${env} deposit recorded for ${ctx.bundleDir}.`);
    ctx.log(`meta.json: ${JSON.stringify(summary)}`);
    return { record: null, live: null, meta: summary, repairs };
  }
  const watch = record.draft?.deposition_id ?? record.published?.deposition_id ?? null;
  let live: Deposition | null = null;
  if (!ctx.client.dryRun && watch !== null) {
    try {
      live = await ctx.client.getDepositionOrNull(watch);
    } catch (err) {
      ctx.warn(`Could not query Zenodo: ${err instanceof ZenodoError ? err.message : String(err)}`);
    }
  }
  ctx.log(`environment    ${record.environment} (${record.api_base})`);
  ctx.log(`concept DOI    ${record.concept_doi ?? "(none)"}   conceptrecid=${record.conceptrecid ?? "(none)"}`);
  ctx.log(`marker         ${record.marker}`);
  if (record.published) {
    ctx.log(
      `published      deposition ${record.published.deposition_id}  ${record.published.version_doi}  ` +
        `v${record.published.published_version ?? "?"}  ${record.published.record_url}`,
    );
  } else {
    ctx.log(`published      (nothing published yet)`);
  }
  if (record.draft) {
    ctx.log(
      `open draft     deposition ${record.draft.deposition_id}  reserved ${record.draft.version_doi}  ` +
        `opened ${record.draft.opened_at}`,
    );
  } else {
    ctx.log(`open draft     (none)`);
  }
  if (record.pending_reserve) {
    ctx.warn(
      `pending        a reserve started ${record.pending_reserve.started_at} did not complete; ` +
        `run 'status --repair' or re-run 'reserve' to adopt any orphaned draft.`,
    );
  }
  ctx.log(`meta.version   ${summary.version ?? "(none)"}`);
  ctx.log(`live state     ${live ? `${live.state} (submitted=${live.submitted})` : "(not queried / not found)"}`);
  ctx.log(`meta.json      doi=${JSON.stringify(summary.doi)} version_doi=${JSON.stringify(summary.version_doi)}`);
  ctx.log(`updated        ${record.updated_at}`);
  return { record, live, meta: summary, repairs };
}

// ---------------------------------------------------------------------------
// abandon
// ---------------------------------------------------------------------------

/**
 * Delete the open UNPUBLISHED draft.
 *
 * Never touches the published version, and never clears the concept DOI while one
 * exists. Abandoning the v2 draft of a published paper leaves v1 exactly as citable as
 * it was a moment earlier.
 *
 * ## The stamped-PDF check
 *
 * Abandoning a FIRST reservation throws away a concept DOI. If the PDF on disk already
 * prints that DOI, every copy of it — including any already distributed — becomes a
 * pointer to nothing, and the next `reserve` mints a different identity for the same
 * paper. So the PDF is inspected first, and an unreadable PDF counts as a refusal too:
 * the check is for the ABSENCE of the DOI, and absence cannot be established from a
 * file nobody can read. `--discard-stamped-doi` is the deliberate override.
 *
 * A REVISION draft is exempt: the published version keeps the concept DOI, so a PDF
 * carrying it stays correct.
 */
export async function abandon(
  ctx: DepositContext,
  opts: { readonly discardStampedDoi?: boolean } = {},
): Promise<{ deleted: boolean }> {
  return withBundleLocks(ctx, (lock) => abandonLocked(ctx, opts, lock));
}

async function abandonLocked(
  ctx: DepositContext,
  opts: { readonly discardStampedDoi?: boolean },
  lock: CommandLockHandle,
): Promise<{ deleted: boolean }> {
  const env = ctx.client.env.name;
  const record = ctx.client.dryRun
    ? (await readSidecar(ctx.bundleDir))[env] ?? null
    : (await reconcile(ctx, {
        allowVanishedFirstReservation: opts.discardStampedDoi === true,
      })).record;

  if (!record) {
    ctx.log(`No ${env} deposit recorded for ${ctx.bundleDir}; nothing to abandon.`);
    return { deleted: false };
  }
  if (!record.draft) {
    if (record.published) {
      throw new Error(
        `There is no open ${env} draft to abandon. Version ${record.published.version_doi} is ` +
          `PUBLISHED: a published Zenodo record cannot be deleted by the API and its DOI is ` +
          `permanent. Ask the Zenodo curators if it genuinely has to go.`,
      );
    }
    // A concept DOI with no draft and nothing published: an earlier reservation was lost.
    // `reserve` refuses in this state and points here, so this has to be the way out.
    if (record.concept_doi) {
      if (!opts.discardStampedDoi) {
        throw new Error(
          `There is no open ${env} draft, but this bundle still holds concept DOI ` +
            `${record.concept_doi} from a reservation that was lost. Giving that DOI up is ` +
            `deliberate — any PDF already stamped with it would print an identifier that ` +
            `resolves to nothing — so re-run with --discard-stamped-doi to clear it.`,
        );
      }
      await clearLostReservation(ctx, record);
      return { deleted: true };
    }
    ctx.log(`No open ${env} draft for ${ctx.bundleDir}; nothing to abandon.`);
    return { deleted: false };
  }

  const isFirstReservation = record.published === null;
  if (isFirstReservation && record.concept_doi && !opts.discardStampedDoi) {
    await assertNotStamped(ctx, record.concept_doi);
  }

  const draftId = record.draft.deposition_id;

  // Deleting someone else's draft is as irreversible as publishing into it. The draft
  // may also have gone between reconcile and here — its own DELETE retried, or someone
  // removing it in the UI — which is not a failure: it is the state abandon was asked
  // to produce, so the local cleanup below still has to run.
  let alreadyGoneBeforeDelete = false;
  if (!ctx.client.dryRun) {
    const live = await ctx.client.getDepositionOrNull(draftId);
    if (live === null) {
      alreadyGoneBeforeDelete = true;
      ctx.log(`Draft ${draftId} is already gone on Zenodo; clearing the local record only.`);
    } else {
      assertBelongsToBundle(ctx, live, "delete this draft");
    }
  }

  // A revision draft's DOI may already be in meta.json, put there by `new-version`.
  // Deleting the draft makes that DOI dead, so the rollback is part of the same
  // operation, not an optional extra — decide whether it is possible BEFORE deleting.
  const metaBefore = await readBundleMeta(ctx.bundleDir);
  const mustRepairVersionDoi =
    record.published !== null && metaBefore.version_doi === record.draft.version_doi;
  // The FIRST-reservation case needs the same guard: abandoning it clears meta.doi and
  // meta.version_doi outright, which is just as much a write.
  const mustClearFirstReservation =
    record.published === null && record.concept_doi !== null &&
    metaBefore.doi === record.concept_doi;
  if ((mustRepairVersionDoi || mustClearFirstReservation) && ctx.metaWritesForbidden) {
    throw new Error(
      `Refusing to abandon draft ${draftId}: meta.json records ` +
        (mustRepairVersionDoi
          ? `its version DOI (${record.draft.version_doi}), which this command would make dead, `
          : `its concept DOI (${record.concept_doi}), which this command would give up, `) +
        `but --no-write-meta forbids the corresponding meta.json write. Re-run without ` +
        `--no-write-meta` +
        (mustRepairVersionDoi
          ? ` so the published version DOI ${record.published!.version_doi} can be restored.`
          : ` so those fields can be cleared.`),
    );
  }

  if (ctx.client.dryRun) {
    ctx.log(`[dry-run] would delete draft ${draftId} and clear the ${env} draft entry.`);
    await ctx.client.deleteDraft(draftId);
    return { deleted: false };
  }

  if (isFirstReservation && opts.discardStampedDoi) {
    ctx.warn(
      `!! DISCARDING concept DOI ${record.concept_doi} with --discard-stamped-doi. Every ` +
        `compiled PDF carrying it is now wrong and must be recompiled against the DOI the next ` +
        `'reserve' produces. If any such PDF has been distributed, it cannot be corrected.`,
    );
  }

  if (!alreadyGoneBeforeDelete) {
    lock.assertHeld();
    const { alreadyGone } = await ctx.client.deleteDraft(draftId);
    ctx.log(alreadyGone
      ? `Draft ${draftId} was already gone on Zenodo; recording that locally.`
      : `Deleted draft ${draftId}.`);
  }

  if (record.published) {
    await saveRecord(ctx, stamped(ctx, {
      ...record, draft: null, pending_reserve: null, publishing: null,
    }));
    ctx.log(
      `The ${env} draft entry is cleared. Version ${record.published.version_doi} stays ` +
        `published and concept DOI ${record.concept_doi} is unchanged.`,
    );
    if (mustRepairVersionDoi) {
      await repairDeadVersionDoi(ctx, record, record.draft.version_doi);
    } else if (ctx.writeMeta) {
      await maybeWriteMeta(ctx, record.concept_doi!, record.published.version_doi);
    }
    return { deleted: true };
  }

  // Nothing published: the reservation is genuinely gone, so the record goes too — in
  // ONE write, not a clear-the-draft write followed by a remove-the-record write. Two
  // writes mean a crash between them leaves a record with no draft and a live concept
  // DOI, which the next reserve refuses outright.
  await clearDepositRecord(ctx.bundleDir, env);
  ctx.log(`Nothing was published for this bundle, so the ${env} entry was removed from zenodo.json.`);

  if (mustClearFirstReservation) {
    await updateBundleMeta(ctx.bundleDir, (m) => {
      m.doi = null;
      m.version_doi = null;
    });
    ctx.log(`Cleared doi/version_doi from meta.json (they held the abandoned reservation).`);
  }
  return { deleted: true };
}

/**
 * Give up a concept DOI whose draft is gone: clear the environment record and the
 * `meta.json` fields it put there, in that order, with the permission check FIRST so a
 * forbidden meta write cannot leave the record half-cleared.
 */
async function clearLostReservation(
  ctx: DepositContext,
  record: DepositEnvRecord,
): Promise<void> {
  const env = ctx.client.env.name;
  const meta = await readBundleMeta(ctx.bundleDir);
  const mustClearMeta = record.concept_doi !== null && meta.doi === record.concept_doi;
  if (mustClearMeta && ctx.metaWritesForbidden) {
    throw new Error(
      `Refusing to discard concept DOI ${record.concept_doi}: meta.json records it, but ` +
        `--no-write-meta forbids clearing it. Re-run without --no-write-meta. Nothing has ` +
        `been changed.`,
    );
  }
  ctx.warn(
    `!! DISCARDING concept DOI ${record.concept_doi}. Every compiled PDF carrying it is now ` +
      `wrong and must be recompiled against the DOI the next 'reserve' produces. If any such ` +
      `PDF has been distributed, it cannot be corrected.`,
  );
  await clearDepositRecord(ctx.bundleDir, env);
  ctx.log(`Removed the ${env} entry from zenodo.json.`);
  if (mustClearMeta) {
    await updateBundleMeta(ctx.bundleDir, (m) => {
      m.doi = null;
      m.version_doi = null;
    });
    ctx.log(`Cleared doi/version_doi from meta.json (they held the discarded reservation).`);
  }
}

/** Refuse when the local PDF carries — or might carry — the DOI about to be discarded. */
async function assertNotStamped(ctx: DepositContext, conceptDoi: string): Promise<void> {
  const pdf = paperPdfPath(ctx.bundleDir);
  const check = await pdfContainsDoi(pdf, conceptDoi);
  if (check.outcome === "unavailable" && check.code === "ENOENT") {
    // ENOENT, and ONLY ENOENT: there is no file, so no file can be carrying the DOI.
    // Every other failure (EACCES, EIO, EISDIR, an extractor that could not parse it)
    // means the PDF IS there and we could not look inside it — which is not evidence of
    // absence, and the previous version treated it as though it were.
    ctx.log(`No paper.pdf to check for the stamp (${check.reason}); proceeding.`);
    return;
  }
  if (check.outcome === "absent") return;
  const why = check.outcome === "present"
    ? `${pdf} already prints ${conceptDoi} (found via ${check.method})`
    : `the stamp check could not run: ${check.reason}`;
  throw new Error(
    `Refusing to abandon this reservation: ${why}.\n\n` +
      `Abandoning it throws the concept DOI away — the next 'reserve' mints a different one — ` +
      `so every copy of that PDF would print an identifier that resolves to nothing. ` +
      `Recompile the paper without the stamp, or pass --discard-stamped-doi if you are certain ` +
      `no stamped PDF has been distributed.`,
  );
}
