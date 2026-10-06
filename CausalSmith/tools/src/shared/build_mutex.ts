/**
 * Cross-process mutex around `lake build` for the CausalSmith package.
 *
 * Once per-qid parallel runs are allowed (see `shared/run_heartbeat.ts`), two
 * concurrent pipelines can independently call `LeanLspClient.build()`. Both
 * invocations target the same `.lake/build` directory, which is not safe under
 * parallel lake invocations — `.olean` writes race and the cache can end up
 * inconsistent. Wrap `lake build` in an exclusive file lock so the LLM stages
 * remain parallel but compilation is serialized.
 *
 * Lock file: `<repoRoot>/.lake-build.lock` (gitignore this).
 *
 * Uses `proper-lockfile`, same as `shared/ledger_update.ts`. A 60-min stale window
 * accommodates Mathlib-scale rebuilds; in practice each acquisition completes
 * in seconds-to-minutes and the lock is released promptly.
 */
import lockfile from "proper-lockfile";
import { stat, writeFile } from "node:fs/promises";
import path from "node:path";

const STALE_MS = 60 * 60_000;
const RETRIES = { retries: 30, factor: 1.5, minTimeout: 200, maxTimeout: 10_000 };

async function ensureLockfileTarget(target: string): Promise<void> {
  try {
    await stat(target);
  } catch {
    await writeFile(target, "{}\n", "utf8");
  }
}

/**
 * The lock could not be ACQUIRED within its retry budget: another process still
 * holds it. The guarded action never started, so nothing it would have done
 * happened. Callers tell a lock wait from a failure of the action by this type.
 * Only contention has this type; any other failure to take the lock (disk full,
 * permissions, a missing directory) propagates as the error it is.
 */
export class LockAcquireError extends Error {
  constructor(readonly lockPath: string, cause: unknown) {
    super(
      `could not acquire ${path.basename(lockPath)}: ${cause instanceof Error ? cause.message : String(cause)}`,
      { cause },
    );
    this.name = "LockAcquireError";
  }
}

type Retries = typeof RETRIES;

/** Run `action` holding the exclusive lock on `lockPath`, waiting within `retries`. */
export async function withFileLock<T>(
  lockPath: string,
  retries: Retries,
  action: () => Promise<T>,
): Promise<T> {
  await ensureLockfileTarget(lockPath);
  let release: () => Promise<void>;
  try {
    release = await lockfile.lock(lockPath, { stale: STALE_MS, retries, realpath: false });
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ELOCKED") throw new LockAcquireError(lockPath, err);
    throw err;
  }
  try {
    return await action();
  } finally {
    await release();
  }
}

export async function withLakeBuildLock<T>(
  repoRoot: string,
  action: () => Promise<T>,
): Promise<T> {
  return withFileLock(path.join(repoRoot, ".lake-build.lock"), RETRIES, action);
}

// Promotion holds the lock across a full build + library_index + embed + doc:gen
// chain, so a run waiting to promote behind another may wait many minutes. Use a
// far more patient retry budget than the per-command lake lock (worst case ≈ 1h of
// waiting, comfortably longer than any single promotion) so a queued promotion
// waits its turn instead of erroring out.
const PROMOTE_RETRIES = { retries: 300, factor: 1.3, minTimeout: 1_000, maxTimeout: 30_000 };

/**
 * Cross-process mutex serializing the WHOLE substrate-promotion step across
 * concurrent `--study` runs. Unlike `withLakeBuildLock` (per-cwd, per-command),
 * this wraps the entire promotion — root-graph edit + `lake build` +
 * `library_index` + `embed:library` + `doc:gen` — so two runs can never
 * interleave their Causalean root edits or race on the shared `.lake` build dir.
 *
 * Keyed on the CAUSALEAN root (the shared resource every promotion mutates), so
 * all runs — regardless of their own package cwd — contend on the same lock:
 * `<causaleanRoot>/.substrate-promote.lock` (gitignore this).
 */
export async function withPromotionLock<T>(
  causaleanRoot: string,
  action: () => Promise<T>,
): Promise<T> {
  return withFileLock(path.join(causaleanRoot, ".substrate-promote.lock"), PROMOTE_RETRIES, action);
}
