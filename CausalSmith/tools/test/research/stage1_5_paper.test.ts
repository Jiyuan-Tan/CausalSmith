/**
 * Stage 1.5 (plan gate + reuse-soundness review) boundary test: the consolidated
 * CKPT 1 and its two outcomes.
 */
import { checkpointGuidance } from "../../src/checkpoint_playbook.js";
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStage1_5 } from "../../src/formalization/stage1_5.js";
import { runReviewBoundary } from "../../src/shared/review_boundary.js";
import { promptPath, planPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";

let repoRoot: string;

function makeCtx(root: string): PipelineContext {
  return {
    repoRoot: root,
    qid: "pid_manski1990test",
    specialization: "default",
    dryRun: false,
    resume: false,
  };
}

function makeState(): StateJson {
  const base: Record<string, unknown> = {
    stage_completed: "1",
    lean_subdir: "CausalSmith/PartialID/PidManski1990Test",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: {
      missing_architecture: false,
    },
  };
  return base as unknown as StateJson;
}

/**
 * Build StageDeps whose runCodex returns the given review JSON.
 * The Stage 1.5 reviewer uses runCodex.
 */
function makeDeps(reviewJson: Record<string, unknown>): StageDeps {
  return {
    runCodex: async (_opts: unknown) => ({
      stdout: JSON.stringify(reviewJson),
      stderr: "",
    }),
    runClaude: async (_opts: unknown) => "",
  };
}

/**
 * Write minimal prompt stubs needed by runStage1_5 and its producer (runStage1).
 */
async function writePromptStubs(root: string): Promise<void> {
  const stubPrompt = async (name: string, body: string) => {
    const target = promptPath(root, name);
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, body);
  };

  await stubPrompt("stage1_5_reuse_soundness.txt", "stub stage1_5_reuse_soundness");
  await stubPrompt("stage1_template.txt", "stub stage1_template");

  // formalization dir for appendReview + baseBrief
  const fmlDir = path.join(root, "doc", "research", "active", "pid_manski1990test");
  await mkdir(fmlDir, { recursive: true });
  // F1.5's plan-gate prelint and F1 (its producer on a revise loop) now fail loud
  // on a missing core.json (readRequired — see the F-stage hardening pass); D0
  // always emits one in production, so tests must too.
  const coreDir = path.join(fmlDir, "discovery");
  await mkdir(coreDir, { recursive: true });
  await writeFile(
    path.join(coreDir, "core.json"),
    JSON.stringify({
      qid: "pid_manski1990test",
      symbols: [],
      assumptions: [],
      statements: [],
      target_estimand: "stub target estimand",
    }),
  );
  // The gate now actually RUNS against a real core.json (previously it no-op'd
  // whenever core.json was absent). Pair it with a gate-clean empty plan.json —
  // an empty core has no nodes to cover, so an empty plan gates ok:true — so the
  // pre-lint passes through to the LLM reviewer these tests are exercising.
  const plan = planPath(root, "pid_manski1990test", "default");
  await mkdir(path.dirname(plan), { recursive: true });
  await writeFile(plan, JSON.stringify({ qid: "pid_manski1990test", nodes: {} }));
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "stage15-paper-"));
  await writePromptStubs(repoRoot);
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("Stage 1.5 review boundary", () => {
  it("a passing review halts at the consolidated CKPT 1", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();

    const reviewJson = {
      status: "pass",
      notes: "plan reuse decisions are sound",
    };
    const deps = makeDeps(reviewJson);

    const result = await runStage1_5({ ctx, state, deps });

    expect(result.stage).toBe("1.5");
    // A pass halts at the consolidated CKPT 1 with the stage completed: the
    // orchestrator audits the settled F1 plan + F1.5 reuse review before F2.
    expect(result.status).toBe("checkpoint");
    expect(result.advance).toBe(true);
    expect(result.message).toContain("CONSOLIDATED CKPT 1 — PASSED");
  });

  it("a rejected plan halts at the same checkpoint, not passed, without rewinding", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const before = state.stage_completed;
    const deps = makeDeps({
      status: "reject",
      classification: "reuse-soundness",
      perItemFindings: [],
      verbatim_critique: "the core statement is ill-scoped; no plan can realize it",
    });

    const result = await runStage1_5({ ctx, state, deps });

    expect(result.status).toBe("checkpoint");
    expect(result.advance).toBe(false);
    expect(result.message).toContain("CONSOLIDATED CKPT 1 — NOT PASSED (rejected");
    expect(state.stage_completed).toBe(before);
    expect(checkpointGuidance("1.5", result.status, false, result.message)).toContain("plan NOT passed");
  });

  it("a plan still failing at the cap halts not passed after cap reviews and cap-1 retries", async () => {
    const ctx = makeCtx(repoRoot);
    let reviews = 0;
    let retries = 0;
    const result = await runReviewBoundary({
      ctx,
      boundary: "stage_1.5_to_1",
      stage: "1.5",
      cap: 3,
      checkpoint: { name: "CONSOLIDATED CKPT 1", passed: "audit" },
      producer: async () => {
        retries++;
        return { stage: "1", status: "completed", message: "re-planned" };
      },
      reviewer: async () => {
        reviews++;
        return { status: "revise", classification: "plan-gate", perItemFindings: [], verbatim_critique: "gate violation" };
      },
    });

    expect([reviews, retries]).toEqual([3, 2]);
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    expect(result.message).toContain("CONSOLIDATED CKPT 1 — NOT PASSED (still failing after 3 reviews; latest verdict revise/plan-gate): gate violation");
  });
});
