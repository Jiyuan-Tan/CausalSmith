/**
 * The per-bundle EMIT lock: one writer at a time for a bundle's paper files.
 *
 * ## What it is for
 *
 * `meta_store.ts` serialises writes to `meta.json`. That is not enough, because the thing those
 * writes DESCRIBE — `paper.tex` — is rewritten outside any shared lock. P4 pins the date, repairs
 * cleveref ids and stamps commit ids into the manuscript; the backfill records the manuscript's
 * hash. Hashing inside the metadata lock closed the window where the file changed while the
 * backfill waited for that lock, but not the one where it changes while the backfill is writing:
 * a concurrent P4 can rewrite the manuscript and then fail before its own metadata write, leaving
 * a recorded hash that matches no version of the file. Nothing detects that afterwards — the next
 * otherwise-identical emit simply sees a hash mismatch and bumps the version over a paper nobody
 * revised, and a version number that reached a reader cannot be taken back.
 *
 * So the manuscript gets a lock of its own, and everything that rewrites a bundle's paper files
 * or reads them to make a durable record holds it for the whole operation.
 *
 * ## Why not the existing run heartbeat
 *
 * `shared/run_heartbeat.ts` does lock a presentation run per bundle, and it is on the shared
 * filesystem. It is deliberately NOT reused here for two reasons. It decides liveness with
 * `process.kill(pid, 0)`, which only answers for processes on the local host: on another cluster
 * node a live owner's PID reads as dead (or collides with an unrelated local process), so it is
 * node-local where it matters most. And it is taken by the presentation CLI around a whole run,
 * not by `stageP4`, so anything calling the stage directly — the future restamp tool, the Zenodo
 * release command, tests — is not covered at all. It remains the right thing for what it does:
 * refusing a second interactive run of the same paper.
 *
 * ## Lock ordering
 *
 * Three locks now exist. Taken in this order, always:
 *
 *     emit lock  →  working-paper registry lock  →  bundle meta lock
 *
 * Coarsest first. A process holding a finer lock must never reach back for a coarser one, or two
 * processes taking them in opposite orders deadlock on a shared filesystem, where the only symptom
 * is a run that never returns. The rule is enforced, not merely documented: each lock marks its
 * async context with a token that is cleared when the physical lock is released, and acquiring a
 * coarser lock while a finer one is held throws.
 *
 * Only the emit lock is held across slow work — that is its entire job. The other two are held for
 * a read and a write.
 *
 * Plain API (paths and functions, no pipeline types) so the restamp tool and the Zenodo release
 * command can take it without importing the pipeline.
 */
import { AsyncLocalStorage } from "node:async_hooks";
import { realpathSync } from "node:fs";
import { mkdir, stat, writeFile } from "node:fs/promises";
import { join, resolve } from "node:path";
import lockfile from "proper-lockfile";
import { isHoldingBundleMetaLock } from "./meta_store.js";
import { isHoldingWpRegistryLock } from "./wp_registry.js";

/** Sentinel the lock is taken on; `proper-lockfile` creates `<it>.lock` beside it. Both are
 *  gitignored — see the presentation byproducts block in the repo `.gitignore`. */
export const EMIT_LOCK_FILE = ".emit.lock";

/**
 * A P4 emit runs a LaTeX compile, a Lean build and several model calls; hours is normal. The
 * stale threshold is therefore generous, and `proper-lockfile` refreshes the lock's mtime every
 * `update` ms while the holder lives, so a long emit never starts to look abandoned. Without that
 * refresh a contender would "recover" a lock that is being actively used, which is worse than no
 * lock at all.
 */
const STALE_MS = 30 * 60_000;
const UPDATE_MS = 60_000;
/** Bounded wait for `wait: true`: about ten minutes, then a message naming the bundle. */
const WAIT_RETRIES = { retries: 60, factor: 1, minTimeout: 10_000, maxTimeout: 10_000 };

function staleWindowText(staleMs: number): string {
  const minutes = Math.round(staleMs / 60_000);
  return minutes >= 1 ? `${minutes} minute${minutes === 1 ? "" : "s"}` : `${Math.round(staleMs / 1000)} seconds`;
}

export type EmitLockOptions = {
  /** true: wait for the holder (bounded). false: fail immediately if the lock is held. */
  wait: boolean;
  /** test seams; production uses the constants above */
  staleMs?: number;
  updateMs?: number;
  retries?: { retries: number; factor: number; minTimeout: number; maxTimeout: number };
};

/** Thrown when the lock is held and the caller asked not to wait. Carries `code` so a caller can
 *  tell "someone else is emitting" apart from a genuine failure. */
export class BundleEmitBusyError extends Error {
  readonly code = "bundle_emit_busy";
  constructor(bundleDir: string, staleMs: number) {
    const path = join(bundleDir, EMIT_LOCK_FILE);
    super(
      `another emit of this bundle is running (${path} is held). Its paper files may be mid-rewrite, ` +
        "so nothing was read or written for it. Re-run once that emit finishes. If the previous emit " +
        `crashed, the lock frees itself after ${staleWindowText(staleMs)} without a heartbeat, or remove ` +
        `${path}.lock once you have confirmed no emit is running.`,
    );
    this.name = "BundleEmitBusyError";
  }
}

/**
 * Thrown when the lock we were holding stopped being ours — the mutex directory was deleted or
 * recovered by another process while this emit was running.
 *
 * `proper-lockfile` reports this from a TIMER, and its default handler rethrows there, which in
 * Node means an uncaught exception that takes the process down from outside any `try`. So the
 * compromise is recorded instead, and the operation fails at its next checkpoint with a message
 * that says which bundle is affected. An emit that has lost its lock must not go on to write:
 * another process may already be rewriting the same files.
 */
export class BundleEmitLockLostError extends Error {
  readonly code = "bundle_emit_lock_lost";
  constructor(bundleDir: string, cause: unknown) {
    super(
      `the emit lock for ${bundleDir} was lost while the emit was running ` +
        `(${cause instanceof Error ? cause.message : String(cause)}). Another process may have recovered ` +
        "or removed it and could now be writing the same bundle, so this emit stopped rather than " +
        "write on top of it. Re-run once nothing else is emitting this paper.",
    );
    this.name = "BundleEmitLockLostError";
  }
}

export function isBundleEmitBusy(err: unknown): err is BundleEmitBusyError {
  return (err as { code?: string } | null)?.code === "bundle_emit_busy";
}

/**
 * The token carries WHICH bundle is locked, not merely that something is.
 *
 * Without it, holding bundle A's lock answered "yes, held" for bundle B — so a nested call that
 * checked before taking its own lock skipped the acquisition entirely and a durable write went
 * out with no exclusivity at all, while the checkpoint before it reported everything fine. The
 * comparison is on the REALPATH, so `/tmp` vs `/private/tmp`, a trailing slash and a symlinked
 * bundle directory are all the same bundle — which is what `proper-lockfile` locks.
 */
type EmitToken = { bundleDir: string; active: boolean; compromised: unknown };

const holdingEmitLock = new AsyncLocalStorage<EmitToken>();

/** A bundle directory's identity for lock comparison: its realpath, or the resolved path when
 *  it does not exist yet (in which case no lock can be held on it either). */
function lockIdentity(bundleDir: string): string {
  try {
    return realpathSync(bundleDir);
  } catch {
    return resolve(bundleDir);
  }
}

/** Whether the caller is inside an emit lock ON THIS BUNDLE that is STILL HELD. */
export function isHoldingBundleEmitLock(bundleDir: string): boolean {
  const token = holdingEmitLock.getStore();
  return token?.active === true && token.bundleDir === lockIdentity(bundleDir);
}

/** The error that compromised the caller's emit lock, or null while it is healthy. */
export function bundleEmitLockCompromise(): unknown {
  return holdingEmitLock.getStore()?.compromised ?? null;
}

/**
 * Throw unless the caller holds a healthy emit lock ON `bundleDir`. Call it at the checkpoints
 * that matter — before a durable write, and before starting expensive work — so a lost lock
 * surfaces as a controlled failure of that emit rather than a process-level crash from a timer.
 *
 * NO LOCK AT ALL FAILS TOO. The earlier version only looked at the compromise field, so an
 * unlocked caller passed the checkpoint silently — the one situation the checkpoint exists to
 * catch, since a caller that never took the lock has exactly the same exposure as one that lost it.
 */
export function assertBundleEmitLockHeld(bundleDir: string): void {
  const token = holdingEmitLock.getStore();
  const mine = token !== undefined && token.bundleDir === lockIdentity(bundleDir);
  // A LOST lock is diagnosed before a missing one: `active` is cleared on release, and the
  // holder whose lock was recovered underneath it needs the specific message, not the generic one.
  if (mine && token.compromised != null) throw new BundleEmitLockLostError(bundleDir, token.compromised);
  if (mine && token.active) return;
  throw new Error(
    `no emit lock is held for ${bundleDir}, and this step is about to write its paper files. ` +
      (token?.active === true
        ? `The lock this caller holds is for ${token.bundleDir}, which is a DIFFERENT bundle — ` +
          "holding one bundle's lock says nothing about another's. "
        : "") +
      `Wrap the operation in withBundleEmitLock(${JSON.stringify(bundleDir)}, …): a write with no ` +
      "exclusivity can land on top of a concurrent emit of the same paper.",
  );
}

/** Retry an ELOCKED acquisition on the caller's schedule; any other failure is immediate. */
async function waitForLock(
  target: string,
  bundleDir: string,
  staleMs: number,
  opts: EmitLockOptions,
  token: EmitToken,
): Promise<() => Promise<void>> {
  const { retries, minTimeout } = opts.retries ?? WAIT_RETRIES;
  for (let attempt = 0; attempt < retries; attempt++) {
    await new Promise((r) => setTimeout(r, minTimeout));
    try {
      return await lockfile.lock(target, {
        stale: staleMs,
        update: opts.updateMs ?? UPDATE_MS,
        retries: 0,
        realpath: false,
        onCompromised: (err) => { token.compromised = err; },
      });
    } catch (err) {
      if ((err as { code?: string }).code !== "ELOCKED") throw err;
    }
  }
  throw new BundleEmitBusyError(bundleDir, staleMs);
}

async function ensureLockTarget(target: string): Promise<void> {
  try {
    await stat(target);
  } catch {
    await mkdir(join(target, ".."), { recursive: true });
    await writeFile(target, "bundle emit lock sentinel\n", "utf8");
  }
}

/**
 * Run `action` as the only emitter of `bundleDir`.
 *
 * Held for the WHOLE operation — compile, Lean build, model calls and all — because the point is
 * that nobody else rewrites `paper.tex` underneath it. Released in `finally`, so a thrown action
 * frees the bundle rather than blocking every later run.
 */
export async function withBundleEmitLock<T>(
  bundleDir: string,
  action: () => Promise<T>,
  opts: EmitLockOptions,
): Promise<T> {
  // See "Lock ordering" above. This is the COARSEST lock, so holding either finer one while
  // reaching for it is the deadlock case.
  if (isHoldingWpRegistryLock() || isHoldingBundleMetaLock()) {
    throw new Error(
      "lock order violation: the bundle emit lock must be taken BEFORE the working-paper registry " +
        "lock and the bundle meta lock, never while one of them is held.",
    );
  }
  const staleMs = opts.staleMs ?? STALE_MS;
  const target = join(bundleDir, EMIT_LOCK_FILE);
  await ensureLockTarget(target);
  const token: EmitToken = { bundleDir: lockIdentity(bundleDir), active: true, compromised: null };
  let release: () => Promise<void>;
  try {
    release = await lockfile.lock(target, {
      stale: staleMs,
      update: opts.updateMs ?? UPDATE_MS,
      // Retries are for CONTENTION only. `proper-lockfile` would also retry a permission or path
      // error, turning an immediate, unfixable failure into a ten-minute wait that ends the same
      // way; the loop below retries ELOCKED and nothing else.
      retries: 0,
      realpath: false,
      onCompromised: (err) => { token.compromised = err; },
    });
  } catch (err) {
    if ((err as { code?: string }).code !== "ELOCKED") throw err;
    if (!opts.wait) throw new BundleEmitBusyError(bundleDir, staleMs);
    release = await waitForLock(target, bundleDir, staleMs, opts, token);
  }
  try {
    const result = await holdingEmitLock.run(token, action);
    // Last checkpoint: if the lock was lost at any point, this emit's writes were made without
    // exclusivity and must not be reported as a success.
    if (token.compromised != null) throw new BundleEmitLockLostError(bundleDir, token.compromised);
    return result;
  } finally {
    // Cleared only once the release has completed — until then the lock really is still held —
    // and by a nested finally so a failing release cannot leave the marker set.
    try {
      await release();
    } catch (err) {
      // A compromised lock is already gone, so `proper-lockfile` reports "already released" here.
      // Rethrowing that from a `finally` would replace the real diagnosis (the lock was LOST)
      // with a confusing one. Any other release failure is still surfaced.
      if (token.compromised == null) throw err;
    } finally {
      token.active = false;
    }
  }
}
