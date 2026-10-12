// D0.5.G replay lane: `review_general.json` records the inputs of the verdict it holds —
// a hash of the reviewed content, the referee standard token, model and effort. A later call
// with the same inputs replays the verdict with no model call; the instruction text is not an input.
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { canonicalLeanSubdir, formalizationDir, promptPath } from "../../src/paths.js";
import { runGeneralReview } from "../../src/discovery/stages/d0_5_general.js";

describe("D0.5.G recorded-verdict replay", () => {
  let repoRoot: string;
  let ctx: PipelineContext;
  let state: StateJson;
  let calls: string[];
  let deps: StageDeps;
  const verdict = {
    tier: "field", salvageable: true, flagged_conjecture_labels: [], critique: "A matched frontier.",
    flagship_potential: false, paper_score_ceiling: 7.6,
  };
  const recordFile = (): string => path.join(formalizationDir(repoRoot, ctx.qid), "reviews", "review_general.json");
  const review = (noteText = "\\section{Result} The rate is $n^{-1/2}$.") =>
    runGeneralReview({ ctx, state, deps, noteText });

  beforeEach(async () => {
    repoRoot = await mkdtemp(path.join(tmpdir(), "cs-d05g-replay-"));
    ctx = { repoRoot, qid: "stat_replay_fixture", specialization: "v1", dryRun: false, resume: false, noveltyTarget: "field" } as PipelineContext;
    const prompt = promptPath(repoRoot, "stage0_5_general_review.txt");
    await mkdir(path.dirname(prompt), { recursive: true });
    await writeFile(prompt, "stub referee instructions", "utf8");
    state = {
      stage_completed: "0",
      lean_subdir: canonicalLeanSubdir(ctx.qid),
      design_decisions: {},
      added_assumptions: [],
      proposed_from: { topic: "t", novelty_target: "field", cluster: "stat" },
      flags: {},
    } as unknown as StateJson;
    calls = [];
    const run = async ({ prompt: sent }: { prompt: string }) => {
      calls.push(sent);
      return { stdout: JSON.stringify(verdict), stderr: "" };
    };
    deps = { runCodex: run, runClaude: run } as unknown as StageDeps;
  });
  afterEach(async () => { await rm(repoRoot, { recursive: true, force: true }); });

  it("replays the recorded verdict with no model call, also after the instruction text was edited", async () => {
    const first = await review();
    expect(calls).toHaveLength(1);
    const record = JSON.parse(await readFile(recordFile(), "utf8")) as { inputs: Record<string, unknown>; reused_from_receipt: boolean };
    expect(record.reused_from_receipt).toBe(false);
    expect(record.inputs.content_sha256).toMatch(/^[0-9a-f]{64}$/);
    expect(typeof record.inputs.standard).toBe("string");
    expect(record.inputs).not.toHaveProperty("prompt_sha256");

    await writeFile(promptPath(repoRoot, "stage0_5_general_review.txt"), "REWORDED referee instructions", "utf8");
    const second = await review();
    expect(calls).toHaveLength(1);
    expect(second).toEqual(first);
    expect((JSON.parse(await readFile(recordFile(), "utf8")) as { reused_from_receipt: boolean }).reused_from_receipt).toBe(true);
  });

  it("judges again when the reviewed note changed", async () => {
    await review();
    await review("\\section{Result} The rate is $n^{-1/3}$.");
    expect(calls).toHaveLength(2);
  });

  it("judges again when the run brief or the novelty floor changed", async () => {
    await review();
    state.design_decisions = { estimand: "restricted to the overlap population" } as StateJson["design_decisions"];
    await review();
    expect(calls).toHaveLength(2);
    ctx.noveltyTarget = "flagship";
    await review();
    expect(calls).toHaveLength(3);
  });

  it("judges again when the record was written under another standard or keyed on the prompt", async () => {
    await review();
    const record = JSON.parse(await readFile(recordFile(), "utf8")) as { inputs: Record<string, string> };
    await writeFile(recordFile(), JSON.stringify({ ...record, inputs: { ...record.inputs, standard: "d05-general-v0" } }), "utf8");
    await review();
    expect(calls).toHaveLength(2);
    const { content_sha256, standard: _standard, ...rest } = record.inputs;
    await writeFile(recordFile(), JSON.stringify({ ...record, inputs: { ...rest, prompt_sha256: content_sha256 } }), "utf8");
    await review();
    expect(calls).toHaveLength(3);
  });

  it("CAUSALSMITH_D05_REUSE=0 turns the lane off", async () => {
    await review();
    process.env.CAUSALSMITH_D05_REUSE = "0";
    try { await review(); } finally { delete process.env.CAUSALSMITH_D05_REUSE; }
    expect(calls).toHaveLength(2);
  });
});
