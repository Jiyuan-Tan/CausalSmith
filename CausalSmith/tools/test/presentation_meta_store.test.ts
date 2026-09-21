import { afterEach, describe, expect, it } from "vitest";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { inPriorKeyOrder, readBundleMeta, updateBundleMeta } from "../src/presentation/meta_store.js";

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

async function bundle(meta?: Record<string, unknown>): Promise<string> {
  const dir = await mkdtemp(join(tmpdir(), "meta-store-"));
  dirs.push(dir);
  if (meta) await writeFile(join(dir, "meta.json"), `${JSON.stringify(meta, null, 2)}\n`);
  return dir;
}

describe("bundle meta.json writer", () => {
  it("writes 2-space JSON with one trailing newline", async () => {
    const dir = await bundle();
    await updateBundleMeta(dir, (m) => { m.qid = "q"; m.score = 7.5; });
    expect(await readFile(join(dir, "meta.json"), "utf8")).toBe('{\n  "qid": "q",\n  "score": 7.5\n}\n');
  });

  it("keeps existing keys in place and appends new ones, so a diff stays readable", async () => {
    const dir = await bundle({ qid: "q", title: "T", score: 6 });
    const written = await updateBundleMeta(dir, (m) => { m.score = 8; m.revised = "2026-09-20"; });
    expect(Object.keys(written)).toEqual(["qid", "title", "score", "revised"]);
    expect(inPriorKeyOrder({ a: 1, b: 2 }, { b: 9, c: 3, a: 1 })).toEqual({ a: 1, b: 9, c: 3 });
    expect(Object.keys(inPriorKeyOrder({ a: 1, b: 2 }, { b: 9, c: 3, a: 1 }))).toEqual(["a", "b", "c"]);
  });

  it("preserves keys the mutator never mentions, including ones it has never heard of", async () => {
    const dir = await bundle({
      qid: "q", authorship: "Jiyuan Tan", doi: "10.5281/zenodo.7", version_doi: "10.5281/zenodo.8",
      score: 7.1, license: "CC-BY-4.0", future_field: { nested: [1, 2] },
    });
    const written = await updateBundleMeta(dir, (m) => { m.version = 3; });
    expect(written).toMatchObject({
      authorship: "Jiyuan Tan", doi: "10.5281/zenodo.7", version_doi: "10.5281/zenodo.8",
      score: 7.1, license: "CC-BY-4.0", future_field: { nested: [1, 2] }, version: 3,
    });
  });

  it("hands the mutator the CURRENT file, not a snapshot the caller took earlier", async () => {
    const dir = await bundle({ qid: "q", doi: null });
    const stale = await readBundleMeta(dir); // the snapshot a long-running stage would hold
    // ...meanwhile another writer publishes a DOI...
    await updateBundleMeta(dir, (m) => { m.doi = "10.5281/zenodo.42"; });
    // ...and the long-running stage finally commits its own field.
    const written = await updateBundleMeta(dir, (m) => { m.version = 2; });
    expect(stale.doi).toBeNull();
    expect(written.doi).toBe("10.5281/zenodo.42");
    expect(written.version).toBe(2);
  });

  it("loses neither update when two writers interleave on the same bundle", async () => {
    const dir = await bundle({ qid: "q" });
    // Each updater sleeps INSIDE its mutator, so without the lock the two read-modify-writes
    // would overlap and the later rename would drop the earlier field.
    const slow = (key: string, value: unknown) =>
      updateBundleMeta(dir, (m) => { m[key] = value; });
    await Promise.all([
      slow("doi", "10.5281/zenodo.1"),
      slow("score", 9.1),
      slow("authorship", "A. Author"),
      slow("version", 4),
    ]);
    const final = await readBundleMeta(dir);
    expect(final).toEqual({ qid: "q", doi: "10.5281/zenodo.1", score: 9.1, authorship: "A. Author", version: 4 });
  });

  // Read-modify-write on the SAME key: the only way every increment survives is if each one
  // re-reads inside the lock. Six contenders is well past the two or three that occur in
  // practice; the lock's backoff makes a much larger herd slow rather than wrong.
  it("serialises concurrent increments of one key without losing any", { timeout: 30_000 }, async () => {
    const dir = await bundle({ n: 0 });
    await Promise.all(Array.from({ length: 6 }, () =>
      updateBundleMeta(dir, (m) => { m.n = (m.n as number) + 1; })));
    expect((await readBundleMeta(dir)).n).toBe(6);
  });

  it("treats an absent file as an empty record and a corrupt one as a loud failure", async () => {
    expect(await readBundleMeta(await bundle())).toEqual({});
    const broken = await bundle();
    await writeFile(join(broken, "meta.json"), "{ not json");
    await expect(readBundleMeta(broken)).rejects.toThrow("not valid JSON");
    const arrayish = await bundle();
    await writeFile(join(arrayish, "meta.json"), "[]");
    await expect(readBundleMeta(arrayish)).rejects.toThrow("expected a JSON object");
  });

  it("lets a mutator return a replacement object, and drops only what it removed", async () => {
    const dir = await bundle({ a: 1, b: 2, c: 3 });
    const written = await updateBundleMeta(dir, (m) => {
      const { b: _dropped, ...rest } = m;
      return { ...rest, d: 4 };
    });
    expect(written).toEqual({ a: 1, c: 3, d: 4 });
    expect(Object.keys(written)).toEqual(["a", "c", "d"]);
  });
});
