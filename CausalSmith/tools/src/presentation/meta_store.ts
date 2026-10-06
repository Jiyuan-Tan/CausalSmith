/**
 * The one writer of a bundle's `meta.json`.
 *
 * ## The problem this exists to stop
 *
 * Three independent processes write this file: P4 (identity + the emitted content fields), P5
 * (the referee score), and the Zenodo tool (the DOIs). Each of them used to read the whole file,
 * hold the object in memory across minutes of slow work, and then write the whole file back. Any
 * two of them overlapping means the later writer silently reverts the earlier one — a published
 * DOI reset to null by a re-emit that started before the deposit, a score erased by a Zenodo
 * update. Nothing detects it afterwards: the file is well-formed, it is just missing a field
 * somebody else had already earned.
 *
 * So every writer must go through `updateBundleMeta` — P4 and P5 do. The Zenodo tool is switched
 * to it at integration time by the orchestrator, and the end-to-end test proving that writer
 * contends correctly belongs to that step; until then it is the one writer that can still lose an
 * update. What is covered here is the CONTRACT it will adopt: the tests exercise two locked
 * writers overlapping, including one overlapping P4's own critical section. `updateBundleMeta`
 * takes a per-bundle lock, RE-READS the
 * file inside the lock, hands the mutator the *fresh* object, and writes atomically. A writer
 * therefore cannot base its write on a stale snapshot, and it cannot clobber a key it does not
 * itself set: the mutator touches only the keys its stage owns, and every other key — including
 * keys this code has never heard of — survives by construction.
 *
 * The lock lives on the SHARED filesystem beside the file it guards, not in the host's `/tmp`.
 * Runs happen on several cluster nodes against one checkout; a host-local lock synchronizes
 * nothing between them, which is exactly how two nodes end up handing out the same number.
 *
 * Deliberately free of presentation-stage types (no `StageIO`, no ctx, plain objects only) so the
 * Zenodo tool can call it without importing the pipeline.
 *
 * ## Lock ordering
 *
 * There are three locks in this package: the per-bundle EMIT lock (`emit_lock.ts`, coarsest —
 * one writer at a time for a bundle's paper files), the working-paper REGISTRY lock
 * (`wp_registry.ts`), and this per-bundle META lock (finest). A process that needs more than one
 * takes them in that order — **emit → registry → meta** — or two processes taking them in
 * opposite orders deadlock, each holding what the other waits for.
 *
 * P4 holds the emit lock for its whole run and takes the other two inside it, in order; the
 * backfill takes the emit lock per bundle around its metadata transaction. The order is enforced,
 * not merely documented, because a deadlock on a shared filesystem lock is invisible until
 * someone notices a run that never finishes: each lock marks its async context with a token
 * cleared when the physical lock releases, and a coarser lock refuses to be taken inside a finer
 * one.
 *
 * Neither lock may be held across slow work. The mutator signature here is synchronous by design
 * so a caller cannot await a compile or a model call inside the critical section.
 */
import { AsyncLocalStorage } from "node:async_hooks";
import { mkdir, readFile, stat, writeFile } from "node:fs/promises";
import { join } from "node:path";
import lockfile from "proper-lockfile";
import { writeJsonAtomic } from "./json_io.js";

export const META_FILE = "meta.json";
/** Sentinel the lock is taken on; `proper-lockfile` then creates `<it>.lock` beside it.
 *  Both are gitignored — see the presentation byproducts block in the repo `.gitignore`. */
export const META_LOCK_FILE = ".meta.lock";

/** A minute is far longer than any read-modify-write here (milliseconds), so a lock older than
 *  this belongs to a process that died rather than one still working. */
const STALE_MS = 60_000;
const RETRIES = { retries: 30, factor: 1.4, minTimeout: 100, maxTimeout: 3_000 };

export type BundleMeta = Record<string, unknown>;

/** Ensure the lock sentinel exists; `proper-lockfile` refuses to lock a missing path. */
async function ensureLockTarget(target: string): Promise<void> {
  try {
    await stat(target);
  } catch {
    await mkdir(join(target, ".."), { recursive: true });
    await writeFile(target, "bundle meta.json lock sentinel\n", "utf8");
  }
}

/**
 * Marks the async context of code running inside a bundle meta lock.
 *
 * Per-context rather than a module-level flag: several `updateBundleMeta` calls are legitimately
 * in flight at once in one process, and a shared counter would report a violation for a caller
 * that holds nothing.
 *
 * The store is a TOKEN whose `active` flag tracks the PHYSICAL lock, not the async context.
 * Context propagates into anything scheduled inside the critical section — a timer, a detached
 * promise — and that work can legitimately outlive the lock; keeping a bare `true` there meant it
 * was refused the registry lock long after this one was released. Clearing the flag in the same
 * `finally` that releases makes the marker mean what it says.
 */
const holdingMetaLock = new AsyncLocalStorage<{ active: boolean; compromised: unknown }>();

/** Whether the caller is inside a bundle meta lock that is STILL HELD. Read by the coarser locks
 *  to enforce the emit→registry→meta ordering. */
export function isHoldingBundleMetaLock(): boolean {
  return holdingMetaLock.getStore()?.active === true;
}

/** Throw if the caller's metadata lock was compromised while it worked. */
export function assertBundleMetaLockHeld(bundleDir: string): void {
  const compromise = holdingMetaLock.getStore()?.compromised;
  if (compromise != null) {
    throw new Error(
      `the metadata lock for ${bundleDir} was lost before this write ` +
        `(${compromise instanceof Error ? compromise.message : String(compromise)}). Another writer may ` +
        "have replaced meta.json meanwhile, so nothing was written. Re-run.",
    );
  }
}

/** Run `action` holding the bundle's metadata lock. Exported for a writer that must make a
 *  decision and a write one indivisible step (the registry adoption path does this). */
export async function withBundleMetaLock<T>(bundleDir: string, action: () => Promise<T>): Promise<T> {
  const target = join(bundleDir, META_LOCK_FILE);
  await ensureLockTarget(target);
  // `proper-lockfile` reports a compromised lock from a TIMER, and its default handler rethrows
  // there — an uncaught exception outside any `try`. Record it instead and fail the transaction
  // below, so a lost lock cannot both crash the process and let the write through.
  const token = { active: true, compromised: null as unknown };
  const release = await lockfile.lock(target, {
    stale: STALE_MS, retries: RETRIES, realpath: false,
    onCompromised: (err) => { token.compromised = err; },
  });
  try {
    // See "Lock ordering" above: anything taking the registry lock from in here is a deadlock
    // waiting for a process that takes them the other way round.
    return await holdingMetaLock.run(token, action);
  } finally {
    // Cleared AFTER the release returns: until then the filesystem lock still exists, and a
    // detached acquisition of the registry lock in that gap would be the forbidden order for
    // real. The nested finally keeps the marker honest even if the release itself throws.
    try {
      await release();
    } catch (err) {
      if (token.compromised == null) throw err; // a compromised lock is already gone
    } finally {
      token.active = false;
    }
  }
}

/** The bundle's `meta.json`, or `{}` when it does not exist yet. Unlocked: for readers that only
 *  need a snapshot (a torn read is impossible — writes land by atomic rename). */
export async function readBundleMeta(bundleDir: string): Promise<BundleMeta> {
  const path = join(bundleDir, META_FILE);
  const raw = await readFile(path, "utf8").catch((err: NodeJS.ErrnoException) => {
    if (err.code === "ENOENT") return null;
    throw err;
  });
  if (raw === null) return {};
  let value: unknown;
  try {
    value = JSON.parse(raw);
  } catch (err) {
    throw new Error(`${path}: not valid JSON (${(err as Error).message})`);
  }
  if (value === null || typeof value !== "object" || Array.isArray(value)) {
    throw new Error(`${path}: expected a JSON object`);
  }
  return value as BundleMeta;
}

/**
 * Re-key `next` so that keys already present in `prior` keep their position and genuinely new
 * keys are appended.
 *
 * Key order is not cosmetic here: these files are reviewed as diffs, and a writer that reshuffles
 * them turns a one-field change into an unreadable rewrite. Keys the mutator deleted are dropped.
 */
export function inPriorKeyOrder(prior: BundleMeta, next: BundleMeta): BundleMeta {
  const out: BundleMeta = {};
  for (const key of Object.keys(prior)) if (key in next) out[key] = next[key];
  for (const key of Object.keys(next)) if (!(key in out)) out[key] = next[key];
  return out;
}

/**
 * Apply `mutate` to the bundle's CURRENT `meta.json` under the per-bundle lock and persist the
 * result; returns what was written.
 *
 * The mutator receives a fresh deep-ish copy read inside the lock — never a snapshot the caller
 * took earlier — and may either mutate it in place or return a replacement object. Whatever it
 * does not touch is preserved, key order included.
 */
export async function updateBundleMeta(
  bundleDir: string,
  mutate: (current: BundleMeta) => BundleMeta | void,
): Promise<BundleMeta> {
  return withBundleMetaLock(bundleDir, async () => {
    const current = await readBundleMeta(bundleDir);
    // The mutator gets its own object, so a mutator that both mutates and returns cannot
    // accidentally alias `current` and defeat the key-order comparison below.
    const draft: BundleMeta = { ...current };
    const returned = mutate(draft);
    const next = inPriorKeyOrder(current, returned ?? draft);
    // Last checkpoint before the durable write: without exclusivity this merge may be based on a
    // document another writer has already replaced.
    assertBundleMetaLockHeld(bundleDir);
    await writeJsonAtomic(join(bundleDir, META_FILE), next);
    return next;
  });
}
