import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { ensurePreD0Intent } from "../../src/discovery/pre_d0_boundary.js";
import { createInitialState } from "../../src/state.js";
import type { PipelineContext } from "../../src/types.js";

describe("pre-D0 intent", () => {
  const withRoot = async (fn: (repoRoot: string) => Promise<void>) => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-pre-d0-"));
    try { await fn(repoRoot); } finally { await rm(repoRoot, { recursive: true, force: true }); }
  };

  it("persists the --propose invocation and rehydrates it on a bare resume", () => withRoot(async (repoRoot) => {
    const state = createInitialState("stat_x");
    const launch: PipelineContext = {
      repoRoot, qid: "stat_x", specialization: "v1", resume: false, dryRun: false,
      proposeTopic: "topic A", noveltyTarget: "subfield",
    };
    expect(await ensurePreD0Intent(launch, state)).toBe(true);
    expect(state.pre_d0_intent).toMatchObject({ topic: "topic A", novelty_target: "subfield" });

    const resume: PipelineContext = { repoRoot, qid: "stat_x", specialization: "v1", resume: true, dryRun: false };
    expect(await ensurePreD0Intent(resume, state)).toBe(true);
    expect(resume.proposeTopic).toBe("topic A");
    expect(resume.noveltyTarget).toBe("subfield");
  }));

  it("migrates a legacy run from proposed_from and fails closed when nothing durable names the topic", () => withRoot(async (repoRoot) => {
    const state = createInitialState("stat_legacy");
    const ctx: PipelineContext = { repoRoot, qid: "stat_legacy", specialization: "v1", resume: true, dryRun: false };
    expect(await ensurePreD0Intent(ctx, state)).toBe(false);

    state.gaps = { gaps_path: "/x/gaps.json", n_open_problems: 3, status: "completed" };
    await expect(ensurePreD0Intent(ctx, state)).rejects.toThrow(/no durable pre_d0_intent/);

    state.proposed_from = {
      topic: "legacy topic", novelty_target: "field", pivot_budget_used: 0, final_verdict: "pending",
      proposal_path: "/x/proto_core.json", novelty_justification: "", chosen_qid: "stat_legacy",
      chosen_specialization: "v1", iterations: [],
    };
    expect(await ensurePreD0Intent(ctx, state)).toBe(true);
    expect(state.pre_d0_intent?.topic).toBe("legacy topic");
    expect(ctx.proposeTopic).toBe("legacy topic");
  }));

  it("rejects a conflicting topic and lets the operator's tier flag update the intent", () => withRoot(async (repoRoot) => {
    const state = createInitialState("stat_t");
    state.pre_d0_intent = { cursor_version: 1, topic: "topic A", novelty_target: "field" };
    const other: PipelineContext = {
      repoRoot, qid: "stat_t", specialization: "v1", resume: true, dryRun: false, proposeTopic: "topic B",
    };
    await expect(ensurePreD0Intent(other, state)).rejects.toThrow(/conflicts with the durable pre-D0 intent/);

    const downgrade: PipelineContext = {
      repoRoot, qid: "stat_t", specialization: "v1", resume: true, dryRun: false, noveltyTarget: "subfield",
    };
    expect(await ensurePreD0Intent(downgrade, state)).toBe(true);
    expect(state.pre_d0_intent.novelty_target).toBe("subfield");
    expect(downgrade.noveltyTarget).toBe("subfield");
  }));
});
