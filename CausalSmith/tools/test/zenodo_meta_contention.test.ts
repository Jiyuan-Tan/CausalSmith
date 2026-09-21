// Two writers, one meta.json.
//
// P4 (identity + emitted content), P5 (the referee score) and this tool (the DOIs) all
// write the same file, on a shared cluster filesystem, from processes that may run on
// different nodes. Atomic replacement alone does not make that safe: each writer reads,
// thinks, and writes back, so whoever renames last silently reverts the other. The
// symptom is a well-formed file that is simply missing a field somebody already earned
// — a published DOI reset to null by a re-emit that started before the deposit.
//
// The fix is that everyone goes through the pipeline package's `updateBundleMeta`,
// which takes a per-bundle lock and RE-READS inside it. This file is the check that the
// Zenodo side actually participates: the deposit writer and a simulated P4 are run
// against the same bundle and both their fields must survive.

import { describe, it, expect, beforeEach } from "vitest";
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { updateBundleMeta as updateViaZenodo, readSidecar, writeDepositRecord, bundleMarker, withCommandLock } from "../src/zenodo/bundle.js";
import { updateBundleMeta as updateViaPipeline, withBundleMetaLock } from "../src/presentation/meta_store.js";

const META = {
  qid: "stat_demo",
  spec: "spec",
  title: "A demo paper",
  abstract: "An abstract.",
  area: "Stat",
  created: "2026-07-21",
  version: 1,
  score: 8,
  score_rationale: "P5 owns this field",
};

let dir: string;

beforeEach(async () => {
  dir = path.join(await mkdtemp(path.join(os.tmpdir(), "zenodo-contention-")), "stat_demo_spec");
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(META, null, 2)}\n`, "utf8");
});

const meta = async () => JSON.parse(await readFile(path.join(dir, "meta.json"), "utf8"));

/** A latch: `wait()` resolves once `open()` is called. */
function latch(): { wait: Promise<void>; open: () => void } {
  let open!: () => void;
  const wait = new Promise<void>((r) => { open = r; });
  return { wait, open };
}

describe("the lock actually blocks — not just 'both writes happened to land'", () => {
  // `Promise.all` over two updates proves nothing on its own: an implementation with no
  // lock at all passes it whenever one update happens to finish before the other starts.
  // These tests hold the lock open across an awaited barrier and observe that the second
  // writer has NOT progressed, which is only possible if it is genuinely blocked.

  // NOTE: the meta lock is NOT reentrant — `updateBundleMeta` inside
  // `withBundleMetaLock` deadlocks, which is why the holder below writes the file
  // directly. The deposit code respects this: everything that runs while holding the
  // meta lock uses the `*Unlocked` variants, and the only nesting that happens is
  // command-lock → meta-lock, which are different files.
  it("makes a second meta writer wait while the first holds the lock", async () => {
    const holding = latch();
    const release = latch();
    let secondEntered = false;
    let secondFinished = false;

    const first = withBundleMetaLock(dir, async () => {
      holding.open();
      await release.wait;
      const current = JSON.parse(await readFile(path.join(dir, "meta.json"), "utf8"));
      await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...current, first: true }, null, 2)}\n`);
    });

    await holding.wait;
    const second = (async () => {
      secondEntered = true;
      await updateViaZenodo(dir, (m) => { m.doi = "10.5072/zenodo.99"; });
      secondFinished = true;
    })();

    // Give the second writer ample opportunity to run to completion if it can.
    await new Promise((r) => setTimeout(r, 300));
    expect(secondEntered).toBe(true);
    expect(secondFinished).toBe(false); // blocked on the lock the first writer holds

    release.open();
    await Promise.all([first, second]);
    expect(secondFinished).toBe(true);

    const m = await meta();
    expect(m.first).toBe(true);
    expect(m.doi).toBe("10.5072/zenodo.99");
  }, 30_000);

  it("makes a second COMMAND wait while the first holds the command lock", async () => {
    const holding = latch();
    const release = latch();
    let secondFinished = false;

    const first = withCommandLock(dir, async () => {
      holding.open();
      await release.wait;
    });
    await holding.wait;
    const second = withCommandLock(dir, async () => { secondFinished = true; });

    await new Promise((r) => setTimeout(r, 300));
    expect(secondFinished).toBe(false);

    release.open();
    await Promise.all([first, second]);
    expect(secondFinished).toBe(true);
  }, 30_000);

  it("releases the command lock when the body throws, so the next command proceeds", async () => {
    await expect(withCommandLock(dir, async () => { throw new Error("boom"); })).rejects.toThrow("boom");
    let ran = false;
    await withCommandLock(dir, async () => { ran = true; });
    expect(ran).toBe(true);
  }, 30_000);
});

describe("meta.json under two concurrent writers", () => {
  it("keeps both writers' fields when the deposit and a P4 re-emit interleave", async () => {
    // Both start from the same on-disk state, as two processes racing would.
    await Promise.all([
      updateViaZenodo(dir, (m) => {
        m.doi = "10.5072/zenodo.99";
        m.version_doi = "10.5072/zenodo.100";
      }),
      updateViaPipeline(dir, (m) => {
        m.wp_number = "CSWP-2026-008";
        m.revised = "2026-09-21";
      }),
    ]);
    const m = await meta();
    expect(m.doi).toBe("10.5072/zenodo.99");
    expect(m.version_doi).toBe("10.5072/zenodo.100");
    expect(m.wp_number).toBe("CSWP-2026-008");
    expect(m.revised).toBe("2026-09-21");
    // And nobody's untouched fields were lost.
    expect(m.score_rationale).toBe(META.score_rationale);
    expect(m.title).toBe(META.title);
  });

  // `proper-lockfile` backs off exponentially (100ms → 3s), so a queue of contenders
  // is intentionally slow to drain; the generous timeout is about the LOCK's retry
  // schedule, not about the writes, which are milliseconds each.
  it("survives many interleaved writers without losing a field", async () => {
    const writers: Promise<unknown>[] = [];
    for (let i = 0; i < 4; i += 1) {
      writers.push(updateViaPipeline(dir, (m) => { m[`p4_field_${i}`] = i; }));
      writers.push(updateViaZenodo(dir, (m) => { m.doi = "10.5072/zenodo.99"; }));
    }
    await Promise.all(writers);
    const m = await meta();
    for (let i = 0; i < 4; i += 1) expect(m[`p4_field_${i}`]).toBe(i);
    expect(m.doi).toBe("10.5072/zenodo.99");
    expect(m.score).toBe(8);
  }, 60_000);

  it("preserves key order and file formatting across a contended write", async () => {
    await Promise.all([
      updateViaZenodo(dir, (m) => { m.doi = "10.5072/zenodo.99"; }),
      updateViaPipeline(dir, (m) => { m.score = 9; }),
    ]);
    const raw = await readFile(path.join(dir, "meta.json"), "utf8");
    expect(raw.endsWith("}\n")).toBe(true);
    expect(raw).toContain('\n  "qid": "stat_demo"');
    // Pre-existing keys keep their positions; the new one is appended.
    const keys = Object.keys(await meta());
    expect(keys.slice(0, Object.keys(META).length)).toEqual(Object.keys(META));
    expect(keys).toContain("doi");
  });

  it("serializes sidecar writes against the same lock", async () => {
    const base = {
      environment: "sandbox" as const,
      api_base: "https://sandbox.zenodo.org/api",
      conceptrecid: 99,
      concept_doi: "10.5072/zenodo.99",
      marker: bundleMarker(dir, "sandbox"),
      published: null,
      draft: null,
      pending_reserve: null,
      publishing: null,
      updated_at: "2026-09-21T00:00:00.000Z",
    };
    await Promise.all([
      writeDepositRecord(dir, base),
      updateViaPipeline(dir, (m) => { m.wp_number = "CSWP-2026-008"; }),
      writeDepositRecord(dir, { ...base, conceptrecid: 99 }),
    ]);
    const s = await readSidecar(dir);
    expect(s.sandbox?.concept_doi).toBe("10.5072/zenodo.99");
    expect((await meta()).wp_number).toBe("CSWP-2026-008");
  });
});
