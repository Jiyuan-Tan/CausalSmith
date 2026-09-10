import { writeFile, rename } from "node:fs/promises";

let seq = 0;

/**
 * Crash-safe JSON persistence for the presentation caches (gate/equivalence/proof
 * verdicts, section/proof cache keys). A plain `writeFile` truncates in place, so a
 * crash — or two concurrent `mapLimit` workers saving the same cache — can leave a
 * half-written file; the next run's `JSON.parse` then throws until the operator
 * deletes the cache and re-pays every audit in it. Unique temp + atomic rename means
 * every landing is a complete document (concurrent writers last-write-win on whole
 * files instead of interleaving bytes). Mirrors `savePaperState`'s temp+rename, with
 * a unique temp name because caches ARE written concurrently.
 */
export async function writeJsonAtomic(path: string, value: unknown): Promise<void> {
  await writeTextAtomic(path, JSON.stringify(value, null, 2) + "\n");
}

/** Replace a complete authored artifact without exposing a truncated file on interruption. */
export async function writeTextAtomic(path: string, text: string): Promise<void> {
  const tmp = `${path}.${process.pid}.${++seq}.tmp`;
  await writeFile(tmp, text, "utf8");
  await rename(tmp, path);
}
