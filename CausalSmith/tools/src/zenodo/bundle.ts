/** The two files a deposit touches inside a presentation bundle: the shared
 *  `meta.json` and the deposit-bookkeeping sidecar `zenodo.json`.
 *
 * ## meta.json is shared state, and this is not its only writer
 *
 * P4 rewrites it on every re-emit, P5 writes the referee score, and this tool writes
 * the DOIs. Atomic replacement is not enough: two processes that each read, think, and
 * write back will silently revert one another (a DOI reset to null by a re-emit that
 * started before the deposit). So every write goes through the pipeline package's
 * `updateBundleMeta`, which takes a per-bundle lock on the SHARED filesystem, re-reads
 * inside the lock, and preserves unknown keys and key order.
 *
 * ## The sidecar exists because meta.json cannot hold what idempotence needs
 *
 * `doi`/`version_doi` are outputs. The durable HANDLE on a reservation is the
 * deposition id, which has no place in the site's data contract. The sidecar holds it,
 * keyed BY ENVIRONMENT so a sandbox rehearsal can never overwrite production.
 *
 * ## Published state and draft state are separate, and that separation is load bearing
 *
 * The first version stored one flat record with a `state` field. Opening a revision
 * overwrote the published record's id with the draft's, so `abandon` on that revision
 * deleted the only memory that v1 existed — and cleared the concept DOI with it. The
 * next `reserve` then minted a SECOND concept DOI for a paper whose published PDF was
 * already stamped with the first. A concept DOI, once a PDF may have been compiled
 * against it, is immutable; {@link DepositEnvRecord} is shaped so that losing it is not
 * expressible.
 *
 * ## Reads fail loudly
 *
 * `{}` is returned for ENOENT and nothing else. A permission error or a corrupt file
 * used to look identical to "no deposit yet", which turns a transient glitch into a
 * duplicate concept DOI.
 */

import { mkdir, readFile, stat, writeFile } from "node:fs/promises";
import path from "node:path";
import { createHash } from "node:crypto";
import lockfile from "proper-lockfile";
import {
  readBundleMeta as readMetaLocked,
  updateBundleMeta as updateMetaLocked,
  withBundleMetaLock,
} from "../presentation/meta_store.js";
import { writeJsonAtomic } from "../presentation/json_io.js";
import type { BundleMeta } from "./metadata.js";
import { PRODUCTION, SANDBOX, type ZenodoEnvironment, type ZenodoEnvironmentName } from "./client.js";

export const META_FILENAME = "meta.json";
export const SIDECAR_FILENAME = "zenodo.json";
export const PAPER_PDF_FILENAME = "paper.pdf";
/** Bumped whenever the sidecar shape changes incompatibly. */
export const SIDECAR_SCHEMA = 2;
/** Sentinel the whole-command lock is taken on; `proper-lockfile` creates `<it>.lock`
 *  beside it. Both need a `.gitignore` entry — see the WP-C report. */
export const COMMAND_LOCK_FILE = ".zenodo.lock";

/** A version of this paper that IS published. Permanent; never cleared. */
export interface PublishedDeposit {
  readonly deposition_id: number;
  /** Locally derived, never copied from a response. */
  readonly version_doi: string;
  /** `meta.version` as it stood when this was published. */
  readonly published_version: number | null;
  readonly record_url: string;
  readonly published_at: string;
}

/** An open, unpublished draft — the only part of the record `abandon` may remove. */
export interface DraftDeposit {
  readonly deposition_id: number;
  /** Reserved, not yet registered. */
  readonly version_doi: string;
  readonly opened_at: string;
}

/** Written BEFORE a draft is created, so a crash in the gap leaves a breadcrumb. */
export interface PendingReserve {
  readonly marker: string;
  readonly started_at: string;
}

/**
 * Written BEFORE the publish POST, and cleared once the publish is recorded.
 *
 * It exists because `meta.version` is MUTABLE and shared: P4 can bump it at any moment,
 * including between a publish whose response was lost and the reconcile that repairs
 * it. Reading the current `meta.version` at repair time therefore answers "what version
 * is the bundle at now", not "what version did we publish" — and recording the first as
 * the second makes `new-version` believe v2 is already out when only v1 is.
 *
 * The hashes pin the exact bytes the deposit was made from, so a later reader can tell
 * whether the published PDF and the published metadata came from the same emit.
 */
export interface PendingPublish {
  readonly version: number | null;
  /** sha256 of the paper.pdf bytes actually uploaded. */
  readonly paper_sha256: string;
  /** sha256 of the meta.json bytes the Zenodo metadata was built from. */
  readonly meta_sha256: string;
  readonly started_at: string;
}

export interface DepositEnvRecord {
  readonly environment: ZenodoEnvironmentName;
  readonly api_base: string;
  /** Null only before the very first draft exists. */
  readonly conceptrecid: number | null;
  /** The paper's permanent identity on this instance. Immutable once set. */
  readonly concept_doi: string | null;
  /** Deterministic, bundle-derived; stamped into the draft's notes so an orphan is
   *  findable after a crash. */
  readonly marker: string;
  readonly published: PublishedDeposit | null;
  readonly draft: DraftDeposit | null;
  readonly pending_reserve: PendingReserve | null;
  /** In-flight publish; see {@link PendingPublish}. */
  readonly publishing: PendingPublish | null;
  readonly updated_at: string;
}

export interface ZenodoSidecar {
  schema?: number;
  sandbox?: DepositEnvRecord;
  production?: DepositEnvRecord;
}

export function metaPath(bundleDir: string): string {
  return path.join(bundleDir, META_FILENAME);
}
export function sidecarPath(bundleDir: string): string {
  return path.join(bundleDir, SIDECAR_FILENAME);
}
export function paperPdfPath(bundleDir: string): string {
  return path.join(bundleDir, PAPER_PDF_FILENAME);
}

/** The site's paper id for this bundle: the directory basename. */
export function bundleId(bundleDir: string): string {
  return path.basename(path.resolve(bundleDir));
}

/**
 * The token stamped into a draft's `notes` so a crashed run can find its orphan.
 *
 * A HASH of the bundle id and the environment name, not the readable id. Two reasons,
 * both from audit:
 *
 *  - The bare id was compared by SUBSTRING, so bundle `foo` would adopt a draft marked
 *    for `foobar` — the wrong paper's permanent identity. Hashing makes every marker
 *    the same length, so no marker can be a prefix of another, and the comparison is
 *    exact line equality regardless.
 *  - Scoping by environment means a sandbox rehearsal and a production deposit for the
 *    same paper can never adopt one another's drafts.
 *
 * Deterministic in (bundle id, environment) and nothing else: two runs of the same
 * bundle must agree, or the orphan is unfindable. The bundle id is the directory
 * basename, which the project treats as the paper's frozen identity.
 */
export function bundleMarker(bundleDir: string, environment: ZenodoEnvironmentName): string {
  const digest = createHash("sha256")
    .update(`${bundleId(bundleDir)}\n${environment}`)
    .digest("hex")
    .slice(0, 32);
  return `causalsmith-bundle-id:${digest}`;
}

/** True when `notes` carries `marker` as a whole line of its own. */
export function notesCarryMarker(notes: unknown, marker: string): boolean {
  return typeof notes === "string" && notes.split(/\r?\n/).some((line) => line.trim() === marker);
}

// ---------------------------------------------------------------------------
// The whole-command lock
// ---------------------------------------------------------------------------

/** Long enough that a slow upload or a retrying network call is never mistaken for a
 *  dead process; the heartbeat below keeps a live holder's lock fresh regardless. */
const COMMAND_LOCK_STALE_MS = 300_000;
const COMMAND_LOCK_UPDATE_MS = 10_000;
const COMMAND_LOCK_RETRIES = { retries: 60, factor: 1.4, minTimeout: 200, maxTimeout: 5_000 };

async function ensureLockTarget(target: string): Promise<void> {
  try {
    await stat(target);
  } catch {
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, "CausalSmith Zenodo command lock sentinel\n", "utf8");
  }
}

/**
 * Hold an exclusive per-bundle lock for the ENTIRE duration of a mutating subcommand,
 * network calls included.
 *
 * ## Why a second lock
 *
 * `meta.json`'s lock (`.meta.lock`) must be held only across a read-modify-write of
 * milliseconds; holding it across a slow upload would block P4 and P5 for the length of
 * a deposit. This lock is the opposite: it exists precisely to cover the slow work, so
 * that "did another process already create a draft for this paper?" is not a question
 * the deposit logic has to answer by racing. It is therefore a different file with a
 * different stale threshold and a heartbeat (`update`), which refreshes the lock while
 * a long request is in flight so a live holder is never judged stale.
 *
 * ## Lock order
 *
 * **zenodo-lock → meta-lock, never the reverse.** A command takes this lock first and
 * may then take the meta lock briefly, many times, inside it. Nothing takes the meta
 * lock and then reaches for this one; that ordering is what makes deadlock impossible,
 * and it is why the meta writer is never called with this lock unheld.
 */
export class CommandLockCompromisedError extends Error {
  constructor(bundleDir: string, detail: string) {
    super(
      `The exclusive command lock on ${bundleDir} was lost mid-command (${detail}). The ` +
        `operation has been stopped before any further request, but anything already sent may ` +
        `or may not have been applied, and another process could have been running ` +
        `concurrently. Re-run the command: it reconciles against Zenodo before acting.`,
    );
    this.name = "CommandLockCompromisedError";
  }
}

/** Handed to the locked action so it can refuse to take the next irreversible step once
 *  the lock is no longer ours. */
export interface CommandLockHandle {
  /** Throws {@link CommandLockCompromisedError} if the lock has been compromised. */
  assertHeld(): void;
}

/** A handle for paths that legitimately run without a lock (dry-run). */
export const UNLOCKED_HANDLE: CommandLockHandle = { assertHeld: () => {} };

/** The one `proper-lockfile` call this module makes, injectable so a test can drive the
 *  compromise callback. Production never passes it; a test that replaces it still goes
 *  through the real handle, so a no-op `assertHeld` fails. */
export type LockAcquirer = (
  target: string,
  opts: Parameters<typeof lockfile.lock>[1],
) => Promise<() => Promise<void>>;

export async function withCommandLock<T>(
  bundleDir: string,
  action: (lock: CommandLockHandle) => Promise<T>,
  acquire: LockAcquirer = (t, o) => lockfile.lock(t, o),
): Promise<T> {
  const target = path.join(bundleDir, COMMAND_LOCK_FILE);
  await ensureLockTarget(target);
  let compromised: string | null = null;
  const release = await acquire(target, {
    stale: COMMAND_LOCK_STALE_MS,
    update: COMMAND_LOCK_UPDATE_MS,
    retries: COMMAND_LOCK_RETRIES,
    realpath: false,
    // proper-lockfile's DEFAULT onCompromised rethrows asynchronously, outside the
    // command's promise chain — on a shared filesystem that turns an NFS hiccup during
    // an upload into an uncaught exception and a hard process exit, at the exact moment
    // the remote outcome is least certain. Recording it instead lets the command stop
    // between steps and report an ambiguous operation the operator can reconcile.
    onCompromised: (err: Error) => { compromised = err.message; },
  });
  const handle: CommandLockHandle = {
    assertHeld: () => {
      if (compromised !== null) throw new CommandLockCompromisedError(bundleDir, compromised);
    },
  };
  try {
    return await action(handle);
  } finally {
    // The lock may already be gone; releasing a compromised lock throws, and that must
    // not mask the action's own outcome.
    await release().catch(() => {});
  }
}

// ---------------------------------------------------------------------------
// meta.json
// ---------------------------------------------------------------------------

export async function readBundleMeta(bundleDir: string): Promise<BundleMeta> {
  const meta = (await readMetaLocked(bundleDir)) as BundleMeta;
  if (Object.keys(meta).length === 0) {
    throw new Error(`No ${META_FILENAME} in ${bundleDir} — is this a presentation bundle?`);
  }
  return meta;
}

/**
 * Apply `mutate` to the bundle's CURRENT `meta.json` under the per-bundle lock.
 *
 * The mutator is handed an object re-read INSIDE the lock, never a snapshot taken
 * earlier, so a long-running deposit cannot write back a view of the file from before
 * P4's re-emit. Unknown keys, key order, 2-space indent and the trailing newline are
 * all preserved by the shared writer.
 */
export async function updateBundleMeta(
  bundleDir: string,
  mutate: (meta: BundleMeta) => void,
): Promise<BundleMeta> {
  return (await updateMetaLocked(bundleDir, (current) => {
    mutate(current as BundleMeta);
  })) as BundleMeta;
}

// ---------------------------------------------------------------------------
// zenodo.json
// ---------------------------------------------------------------------------

function isObject(v: unknown): v is Record<string, unknown> {
  return v !== null && typeof v === "object" && !Array.isArray(v);
}

function badSidecar(file: string, detail: string): Error {
  return new Error(
    `${file} is not a valid deposit sidecar (${detail}).\n` +
      `This file is the ONLY record of any draft already opened for this paper. Treating it ` +
      `as absent would open a second deposit and mint a second, permanent concept DOI. ` +
      `Inspect and fix it by hand — do not delete it without first checking Zenodo for an ` +
      `existing draft or published record for this bundle.`,
  );
}

function isIsoTimestamp(v: unknown): boolean {
  return typeof v === "string" && !Number.isNaN(Date.parse(v));
}

function positiveInt(v: unknown): boolean {
  return typeof v === "number" && Number.isInteger(v) && v > 0;
}

/** `<prefix>/zenodo.<id>` for the given environment, or null when it is not that. */
function doiRecid(env: ZenodoEnvironment, doi: unknown): number | null {
  if (typeof doi !== "string") return null;
  const m = new RegExp(`^${env.doiPrefix.replace(".", "\\.")}/zenodo\\.(\\d+)$`).exec(doi.trim());
  return m ? Number(m[1]) : null;
}

function checkFields(
  file: string, where: string, value: Record<string, unknown>,
  spec: [string, (v: unknown) => boolean, string][],
  /** Keys a record written by an older build may legitimately lack. */
  optional: ReadonlySet<string> = new Set(),
): void {
  for (const [key, ok, expected] of spec) {
    if (!(key in value)) {
      if (optional.has(key)) continue;
      throw badSidecar(file, `"${where}.${key}" is missing (expected ${expected})`);
    }
    if (!ok(value[key])) {
      throw badSidecar(file, `"${where}.${key}" should be ${expected} but is ${JSON.stringify(value[key])}`);
    }
  }
  for (const key of Object.keys(value)) {
    if (!spec.some(([k]) => k === key)) {
      throw badSidecar(file, `unexpected key "${where}.${key}"`);
    }
  }
}

/**
 * Validate one environment's record, recursively and against that environment's own
 * constants.
 *
 * The previous version checked shapes but not CONSISTENCY, so a record filed under the
 * `sandbox` key could declare `environment: "production"` and carry a production
 * api_base — after which a sandbox command would write through the production key and
 * overwrite genuine production bookkeeping. Nested `published`/`draft` objects were not
 * inspected at all, so `draft: {}` passed and then produced `undefined` deposition ids.
 *
 * Everything that can be cross-checked is: the key must equal the record's own
 * environment, the api_base and every DOI prefix must be that environment's, and a
 * concept DOI must name the conceptrecid it is filed beside.
 */
function validateEnvRecord(
  file: string, envKey: ZenodoEnvironmentName, value: unknown, bundleDir: string,
): DepositEnvRecord {
  if (!isObject(value)) throw badSidecar(file, `"${envKey}" is not an object`);
  const env: ZenodoEnvironment = envKey === "production" ? PRODUCTION : SANDBOX;
  const expectedMarker = bundleMarker(bundleDir, envKey);

  checkFields(file, envKey, value, [
    ["environment", (v) => v === envKey,
      `"${envKey}" — a record filed under the "${envKey}" key must not claim another environment`],
    ["api_base", (v) => v === env.apiBase, `exactly "${env.apiBase}" for the ${envKey} instance`],
    // NOT merely "a well-formed marker": THIS bundle's marker. A zenodo.json copied or
    // inherited from another bundle is syntactically perfect and names another paper's
    // deposit; acting on it would publish this bundle's PDF under that paper's DOI.
    ["marker", (v) => v === expectedMarker,
      `exactly ${expectedMarker} — the marker derived from this bundle directory and the ` +
      `"${envKey}" environment. A different marker means this zenodo.json belongs to another ` +
      `bundle (copied or renamed?) and must not be acted on`],
    ["conceptrecid", (v) => v === null || positiveInt(v), "null or a positive integer"],
    ["concept_doi", (v) => v === null || doiRecid(env, v) !== null,
      `null or a DOI with the ${envKey} prefix ${env.doiPrefix}`],
    ["published", (v) => v === null || isObject(v), "null or an object"],
    ["draft", (v) => v === null || isObject(v), "null or an object"],
    ["pending_reserve", (v) => v === null || isObject(v), "null or an object"],
    ["publishing", (v) => v === null || isObject(v), "null or an object"],
    ["updated_at", isIsoTimestamp, "an ISO timestamp"],
  ], new Set(["publishing"]));

  const conceptrecid = value.conceptrecid as number | null;
  const conceptDoi = value.concept_doi as string | null;
  if ((conceptrecid === null) !== (conceptDoi === null)) {
    throw badSidecar(file, `"${envKey}.conceptrecid" and "${envKey}.concept_doi" must be set together`);
  }
  if (conceptDoi !== null && doiRecid(env, conceptDoi) !== conceptrecid) {
    throw badSidecar(
      file,
      `"${envKey}.concept_doi" is ${JSON.stringify(conceptDoi)} but "${envKey}.conceptrecid" is ` +
        `${conceptrecid}; a concept DOI must name its own conceptrecid`,
    );
  }

  if (isObject(value.published)) {
    checkFields(file, `${envKey}.published`, value.published, [
      ["deposition_id", positiveInt, "a positive integer"],
      ["version_doi", (v) => doiRecid(env, v) !== null, `a DOI with the ${envKey} prefix ${env.doiPrefix}`],
      ["published_version", (v) => v === null || positiveInt(v), "null or a positive integer"],
      ["record_url", (v) => typeof v === "string" && v.startsWith(`${env.webBase}/`),
        `a URL under ${env.webBase}`],
      ["published_at", isIsoTimestamp, "an ISO timestamp"],
    ]);
    const pub = value.published as unknown as PublishedDeposit;
    if (doiRecid(env, pub.version_doi) !== pub.deposition_id) {
      throw badSidecar(file, `"${envKey}.published.version_doi" does not name deposition ${pub.deposition_id}`);
    }
  }

  if (isObject(value.draft)) {
    checkFields(file, `${envKey}.draft`, value.draft, [
      ["deposition_id", positiveInt, "a positive integer"],
      ["version_doi", (v) => doiRecid(env, v) !== null, `a DOI with the ${envKey} prefix ${env.doiPrefix}`],
      ["opened_at", isIsoTimestamp, "an ISO timestamp"],
    ]);
    const draft = value.draft as unknown as DraftDeposit;
    if (doiRecid(env, draft.version_doi) !== draft.deposition_id) {
      throw badSidecar(file, `"${envKey}.draft.version_doi" does not name deposition ${draft.deposition_id}`);
    }
    if (isObject(value.published) &&
        (value.published as unknown as PublishedDeposit).deposition_id === draft.deposition_id) {
      throw badSidecar(file, `"${envKey}" lists the same deposition as both published and draft`);
    }
  }

  if (isObject(value.publishing)) {
    checkFields(file, `${envKey}.publishing`, value.publishing, [
      ["version", (v) => v === null || positiveInt(v), "null or a positive integer"],
      ["paper_sha256", (v) => typeof v === "string" && /^[0-9a-f]{64}$/.test(v), "a sha256 hex digest"],
      ["meta_sha256", (v) => typeof v === "string" && /^[0-9a-f]{64}$/.test(v), "a sha256 hex digest"],
      ["started_at", isIsoTimestamp, "an ISO timestamp"],
    ]);
  }

  if (isObject(value.pending_reserve)) {
    checkFields(file, `${envKey}.pending_reserve`, value.pending_reserve, [
      ["marker", (v) => v === value.marker, "the same marker as the record"],
      ["started_at", isIsoTimestamp, "an ISO timestamp"],
    ]);
  }

  if (value.publishing === undefined) value.publishing = null;
  return value as unknown as DepositEnvRecord;
}

/**
 * Read the sidecar.
 *
 * Returns `{}` for ENOENT ONLY. Every other outcome — EACCES, EIO, malformed JSON, a
 * JSON array, a record missing its fields — throws, because each of them is
 * indistinguishable from "no deposit yet" to a caller that swallows it, and the cost of
 * being wrong is a duplicate permanent DOI.
 */
export async function readSidecar(bundleDir: string): Promise<ZenodoSidecar> {
  const file = sidecarPath(bundleDir);
  let raw: string;
  try {
    raw = await readFile(file, "utf8");
  } catch (err) {
    const code = (err as NodeJS.ErrnoException).code;
    if (code === "ENOENT") return {};
    throw new Error(
      `${file} exists but could not be read (${code ?? "unknown error"}). Refusing to continue: ` +
        `treating an unreadable sidecar as absent would open a duplicate deposit.`,
    );
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw);
  } catch (err) {
    throw badSidecar(file, `invalid JSON: ${(err as Error).message}`);
  }
  if (!isObject(parsed)) throw badSidecar(file, "the top level is not a JSON object");

  const out: ZenodoSidecar = {};
  if ("schema" in parsed) {
    if (typeof parsed.schema !== "number") throw badSidecar(file, '"schema" is not a number');
    if (parsed.schema > SIDECAR_SCHEMA) {
      throw badSidecar(
        file,
        `it was written by a newer tool (schema ${parsed.schema} > ${SIDECAR_SCHEMA})`,
      );
    }
    out.schema = parsed.schema;
  }
  for (const env of ["sandbox", "production"] as const) {
    if (parsed[env] === undefined) continue;
    out[env] = validateEnvRecord(file, env, parsed[env], bundleDir);
  }
  for (const key of Object.keys(parsed)) {
    if (key !== "schema" && key !== "sandbox" && key !== "production") {
      throw badSidecar(file, `unexpected top-level key ${JSON.stringify(key)}`);
    }
  }
  return out;
}

/**
 * Replace one environment's record, under the SAME per-bundle lock `meta.json` uses.
 *
 * Sharing the lock is deliberate: `reserve` and `publish` update both files as one
 * logical step, and a reader that sees a DOI in `meta.json` with no matching sidecar
 * entry (or the reverse) cannot tell which write to trust. Holding one lock across both
 * makes the pair consistent to anyone who takes it.
 */
export async function writeDepositRecord(
  bundleDir: string,
  record: DepositEnvRecord,
): Promise<ZenodoSidecar> {
  return withBundleMetaLock(bundleDir, async () => {
    const sidecar = await readSidecar(bundleDir);
    const next: ZenodoSidecar = { ...sidecar, schema: SIDECAR_SCHEMA, [record.environment]: record };
    await writeJsonAtomic(sidecarPath(bundleDir), next);
    return next;
  });
}

/** Run `action` holding the bundle lock, so a read-decide-write over the sidecar and
 *  `meta.json` is one indivisible step. The action must use the `*Unlocked` helpers. */
export async function withBundleLock<T>(bundleDir: string, action: () => Promise<T>): Promise<T> {
  return withBundleMetaLock(bundleDir, action);
}

/** Sidecar write WITHOUT taking the lock — for use inside {@link withBundleLock}. */
export async function writeDepositRecordUnlocked(
  bundleDir: string,
  record: DepositEnvRecord,
): Promise<ZenodoSidecar> {
  const sidecar = await readSidecar(bundleDir);
  const next: ZenodoSidecar = { ...sidecar, schema: SIDECAR_SCHEMA, [record.environment]: record };
  await writeJsonAtomic(sidecarPath(bundleDir), next);
  return next;
}

/** Drop one environment's record entirely.
 *
 *  Only correct when that environment has NOTHING published — `abandon` checks first,
 *  and removing a record that names a published version would lose the concept DOI. */
export async function clearDepositRecord(
  bundleDir: string,
  environment: ZenodoEnvironmentName,
): Promise<ZenodoSidecar> {
  return withBundleMetaLock(bundleDir, async () => {
    const sidecar = await readSidecar(bundleDir);
    const existing = sidecar[environment];
    if (existing?.published) {
      throw new Error(
        `Refusing to remove the ${environment} deposit record for ${bundleDir}: it names ` +
          `published version ${existing.published.version_doi}, and dropping it would lose the ` +
          `permanent concept DOI ${existing.concept_doi}.`,
      );
    }
    const next: ZenodoSidecar = { ...sidecar, schema: SIDECAR_SCHEMA };
    delete next[environment];
    await writeJsonAtomic(sidecarPath(bundleDir), next);
    return next;
  });
}
