import { existsSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import { loadGraph } from "../../../src/discovery/vcs/graph.js";
import { applyUnitOutput, foldUnitHeads, reconcileToBase, scopeSubmissionProse, type PrRecord, type UnitSubmission } from "../../../src/discovery/vcs/pr.js";
import { VcsStore } from "../../../src/discovery/vcs/store.js";

// Every real solver round whose raw inputs are on disk is replayed against the base it
// saw. A replay may only do better than the record: no order-rule drop (layout is
// normalized, never a reason to lose content) and no more drops than were recorded.
// Runs the mill moves mid-test are skipped, never failed.

const ACTIVE = fileURLToPath(new URL("../../../../doc/research/active", import.meta.url));

async function realPrs(): Promise<Array<{ run: string; pr: PrRecord; storeDir: string }>> {
  const out: Array<{ run: string; pr: PrRecord; storeDir: string }> = [];
  if (!existsSync(ACTIVE)) return out;
  for (const run of await readdir(ACTIVE)) {
    const storeDir = path.join(ACTIVE, run, "discovery", "vcs");
    const prDir = path.join(storeDir, "prs");
    if (!existsSync(prDir)) continue;
    for (const name of await readdir(prDir)) {
      if (!name.endsWith(".inputs.json") || name.startsWith("legacy")) continue;
      try {
        const pr = JSON.parse(await readFile(path.join(prDir, name.replace(".inputs.json", ".json")), "utf8")) as PrRecord;
        if (pr.inputs !== undefined) out.push({ run, pr, storeDir });
      } catch { /* moved or partial: skip */ }
    }
  }
  return out;
}

describe("corpus: every recorded solver round replays no worse than it was recorded", async () => {
  const prs = await realPrs();
  it.each(prs.length > 0 ? prs.map((p) => [`${p.run} round ${p.pr.round} ${p.pr.id.slice(0, 12)}`, p] as const) : [])("%s", async (_label, { pr, storeDir }) => {
    const store = new VcsStore(storeDir);
    let base;
    let inputs: { units: UnitSubmission[] };
    try {
      base = await loadGraph(store, pr.base);
      inputs = JSON.parse(await readFile(pr.inputs!, "utf8"));
    } catch { return; }
    // inputs.json holds the raw submissions; openPr applies the deterministic prose lease
    // before folding, so the replay must too (otherwise every unit's prose collides on meta).
    const units = inputs.units.map((s) => scopeSubmissionProse(s, s.proseRole ?? "omit"));
    const heads = units.map((s) => applyUnitOutput(base, { ...s, siblingTargets: units.filter((o) => o !== s).flatMap((o) => o.targets) }));
    const fold = foldUnitHeads(base, heads);
    const rec = reconcileToBase(base, fold.graph);
    const drops = [...fold.conflicts.map((c) => c.id), ...rec.dropped.map((d) => d.id)];
    for (const d of rec.dropped) expect(d.reason).not.toMatch(/before it is defined|unattributable|still fails checks/);
    expect(drops.length).toBeLessThanOrEqual(pr.dropped.length);
  }, 120_000);
  if (prs.length === 0) it("no recorded rounds on this checkout", () => { expect(true).toBe(true); });
});
