import { writeFile, rename, rm, mkdir } from "node:fs/promises";
import path from "node:path";
import process from "node:process";

/**
 * Write `value` as pretty-printed JSON to `target`, atomically.
 *
 * Every canonical D-stage store is written through this: a torn graph-store object or
 * `core.json` costs the run every proof it holds, and a crash mid-write is not
 * a hypothetical on a shared cluster filesystem. Writing to a sibling temp file and
 * renaming makes the replacement atomic, so a reader sees either the old file or the
 * new one and never a truncated prefix.
 *
 * The temp name carries pid and timestamp so two concurrent writers to the same
 * target cannot collide on the scratch file; `rm` in `finally` leaves no debris
 * behind when the write itself throws.
 *
 * The destination directory is created if absent. `artifactPath` puts that obligation
 * on writers ("Writers must mkdir the dirname"), but nearly every call site here
 * instead relies on an earlier stage having made the subfolder — an invisible ordering
 * dependency that fails with ENOENT exactly when one of these stores is written FIRST
 * into a fresh run tree. Ensuring it here makes the contract hold by construction, and
 * matches every other store writer in the tree (state.ts, log.ts, graph/store.ts).
 */
export async function writeJsonAtomic(target: string, value: unknown): Promise<void> {
  await mkdir(path.dirname(target), { recursive: true });
  await writeTextAtomic(target, JSON.stringify(value, null, 2));
}

/**
 * `rename`, retried through the transient failures Windows adds to it.
 *
 * The retry is win32-only, so this is a strict no-op elsewhere: on POSIX
 * `rename(2)` replaces the destination unconditionally, and EPERM/EACCES/EBUSY there
 * are permanent conditions (permissions, a sticky bit, a busy mountpoint) that a
 * backoff would only report more slowly. Windows' MoveFileEx also replaces — EXCEPT
 * while any process holds the destination open, which on a developer machine is
 * routine: an editor, the search indexer, a virus scanner, a synced folder, or simply
 * the sibling `mapLimit` worker reading the cache we are replacing. Those clear
 * within milliseconds, so a short backoff turns a spurious stage failure back into
 * the atomic swap the caller asked for.
 */
export async function renameWithRetry(from: string, to: string): Promise<void> {
  for (let attempt = 0; ; attempt++) {
    try {
      await rename(from, to);
      return;
    } catch (err) {
      const code = (err as NodeJS.ErrnoException).code;
      const transient = process.platform === "win32" &&
        (code === "EPERM" || code === "EACCES" || code === "EBUSY");
      if (!transient || attempt >= 10) throw err;
      await new Promise((resolve) => setTimeout(resolve, 10 * (attempt + 1)));
    }
  }
}

/** Atomic raw-text variant of `writeJsonAtomic`, for writers that must preserve
 * exact prior bytes (e.g. transaction rollbacks) rather than re-serialize. */
export async function writeTextAtomic(target: string, text: string): Promise<void> {
  const temp = `${target}.tmp-${process.pid}-${Date.now()}`;
  await mkdir(path.dirname(target), { recursive: true });
  try {
    await writeFile(temp, text, "utf8");
    await renameWithRetry(temp, target);
  } finally {
    await rm(temp, { force: true });
  }
}
