import { describe, it, expect } from "vitest";
import { mkdtemp, readFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { recordGateNodes, recordSubstrateGateList } from "../src/pipeline_support.js";
import { substrateDebtPath } from "../src/paths.js";
import type { SubstrateGate } from "../src/judgment.js";
import type { PipelineContext } from "../src/types.js";

const ctx = (repoRoot: string): PipelineContext =>
  ({ repoRoot, qid: "stat_demo", specialization: "v1" } as PipelineContext);

/** Record the gates each reviewer reported, as the proof-review loop does. */
const recordFromReviews = (repoRoot: string, reviews: SubstrateGate[][]) =>
  recordSubstrateGateList(ctx(repoRoot), reviews.flat());

const gate: SubstrateGate = {
  name: "h : PinskerBound P₀ P₁",
  statement: "tvDist μ ν ≤ √(KL/2)",
  classical_fact: "Pinsker's inequality",
  missing_infra: "Scheffé / f-divergence layer",
};

describe("substrate-debt ledger", () => {
  it("appends a row, unions across reviewers, and dedups on re-run", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-substrate-"));
    const reviews = [[gate], [gate]];
    const file = await recordFromReviews(tmp, reviews);
    expect(file).toBe(substrateDebtPath(tmp));
    const first = await readFile(substrateDebtPath(tmp), "utf8");
    // union dedup by name: exactly one row for this gate
    expect(first.match(/PinskerBound/g)?.length).toBe(1);
    expect(first).toContain("| open |");

    // re-run with the same gate for the same run → no duplicate, no write
    const again = await recordFromReviews(tmp, reviews);
    expect(again).toBeUndefined();
    const second = await readFile(substrateDebtPath(tmp), "utf8");
    expect(second).toBe(first);
  });

  it("no-ops (no file) when there are no gates", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-substrate-"));
    const file = await recordFromReviews(tmp, [[]]);
    expect(file).toBeUndefined();
  });

  // recordGateNodes (the F1 gate-node path) writes the SAME global ledger; it must go through
  // the locked+atomic writer like recordSubstrateGateList so concurrent runs cannot clobber rows.
  it("recordGateNodes appends a gated row, dedups on re-run, and preserves other runs' rows", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-substrate-"));
    const debt = { name: "GateA", statement: "A holds", classical_fact: "classic", missing_infra: "layer" };
    const file = await recordGateNodes(ctx(tmp), [debt]);
    expect(file).toBe(substrateDebtPath(tmp));
    const first = await readFile(substrateDebtPath(tmp), "utf8");
    expect(first.match(/GateA/g)?.length).toBe(1);

    // Same gate re-recorded → no duplicate; a different run's row survives alongside.
    expect(await recordGateNodes(ctx(tmp), [debt])).toBeUndefined();
    await recordGateNodes(
      { repoRoot: tmp, qid: "other_qid", specialization: "v2" } as PipelineContext,
      [debt],
    );
    const second = await readFile(substrateDebtPath(tmp), "utf8");
    expect(second).toContain("stat_demo/v1");
    expect(second).toContain("other_qid/v2");
    expect(second.match(/GateA/g)?.length).toBe(2);
  });
});
