/**
 * Stage 1 (formalization plan) handler tests.
 *
 * Verifies that runStage1:
 *   - returns status: "checkpoint" when no usable plan was parsed (a completed
 *     reply with no plan on disk, or a blocked-infeasible reply); in production
 *     a usable plan makes F1 advance "completed" into F1.5, which owns the
 *     consolidated CKPT 1.
 *   - enters revise mode when pipeline history records a later stage and a
 *     prior plan exists, and rebuilds full reuse context when it does not.
 */
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStage1 } from "../../src/formalization/stage1.js";
import { pipelineLogPath, planPath, promptPath } from "../../src/paths.js";
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
    stage_completed: "0.5",
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
 * Build a StageDeps whose runClaude returns the given response JSON string.
 * Stage 1 uses runClaude (not runCodex) and expects the string directly.
 */
function makeDeps(): StageDeps {
  const responseJson = JSON.stringify({
    status: "completed",
    message: "NL formalization done",
    artifacts: [],
  });

  return {
    runClaude: async (_opts: unknown) => responseJson,
    runCodex: async (_opts: unknown) => {
      throw new Error("runCodex should not be called by Stage 1");
    },
  };
}

/**
 * Write the minimal prompt stub that runStage1 reads (stage1_template.txt).
 * baseBrief and readPrompt both need the prompts directory.
 */
async function writePromptStubs(root: string): Promise<void> {
  const target = promptPath(root, "stage1_template.txt");
  await mkdir(path.dirname(target), { recursive: true });
  await writeFile(target, "stub stage1_template");
  // formalization dir needed for baseBrief path resolution
  const fmlDir = path.join(root, "doc", "research", "active", "pid_manski1990test");
  await mkdir(fmlDir, { recursive: true });
  // F1 now fails loud on a missing core.json (readRequired — see the F-stage
  // hardening pass); D0 always emits one in production, so tests must too.
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
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "stage1-paper-"));
  await writePromptStubs(repoRoot);
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("Stage 1 formalization plan", () => {
  it("a completed reply with no usable plan on disk returns checkpoint", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const deps = makeDeps();

    const result = await runStage1({ ctx, state, deps });

    expect(result.stage).toBe("1");
    expect(result.status).toBe("checkpoint");
  });

  it("a blocked-infeasible reply returns checkpoint", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();

    const blockedJson = JSON.stringify({
      status: "blocked-infeasible",
      feasibility_verdict: "infeasible-out-of-scope",
      message: "proof requires functional analysis beyond Mathlib scope",
      feasibility_notes: "step 4 requires a non-constructive selection argument",
    });

    const deps: StageDeps = {
      runClaude: async (_opts: unknown) => blockedJson,
      runCodex: async (_opts: unknown) => {
        throw new Error("runCodex should not be called by Stage 1");
      },
    };

    const result = await runStage1({ ctx, state, deps });

    expect(result.stage).toBe("1");
    expect(result.status).toBe("checkpoint");
  });

  it("enters revise mode after an F-to-D rewind when a later stage is recorded in pipeline history", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    let prompt = "";
    const existingPlan = planPath(repoRoot, ctx.qid, ctx.specialization);
    await mkdir(path.dirname(existingPlan), { recursive: true });
    await writeFile(existingPlan, '{"preserve":"this existing plan"}');
    const existingGraph = path.join(
      repoRoot,
      "doc/research/active/pid_manski1990test/graph.json",
    );
    const existingNote = path.join(
      repoRoot,
      "doc/research/active/pid_manski1990test/formalization/formalization.md",
    );
    await mkdir(path.dirname(existingNote), { recursive: true });
    await writeFile(existingGraph, '{"preserve":"reviewed graph"}\n');
    await writeFile(existingNote, "preserve reviewed note\n");

    const log = pipelineLogPath(repoRoot, ctx.qid, ctx.specialization);
    await writeFile(log, JSON.stringify({ stage: "3", status: "completed" }) + "\n");

    const reviseHead = promptPath(repoRoot, "stage1_head_revise.txt");
    await mkdir(path.dirname(reviseHead), { recursive: true });
    await writeFile(reviseHead, "REVISION HEAD");
    const deps: StageDeps = {
      runClaude: async (opts: unknown) => {
        prompt = (opts as { prompt: string }).prompt;
        return JSON.stringify({ status: "completed", artifacts: [] });
      },
      runCodex: async () => {
        throw new Error("runCodex should not be called by Stage 1");
      },
    };

    await runStage1({ ctx, state, deps });

    expect(prompt).toContain("REVISION HEAD");
    expect(prompt).toContain(`Prior plan to patch (Edit in place): ${existingPlan}`);
    expect(prompt).toContain("Patch the existing plan");
    expect(await readFile(existingPlan, "utf8")).toBe('{"preserve":"this existing plan"}');
    expect(await readFile(existingGraph, "utf8")).toBe('{"preserve":"reviewed graph"}\n');
    expect(await readFile(existingNote, "utf8")).toBe("preserve reviewed note\n");
  });

  it("rebuilds full reuse context when history exists but the prior plan is missing", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    let prompt = "";
    await writeFile(
      pipelineLogPath(repoRoot, ctx.qid, ctx.specialization),
      JSON.stringify({ stage: "3", status: "completed" }) + "\n",
    );
    const deps: StageDeps = {
      runClaude: async (opts: unknown) => {
        prompt = (opts as { prompt: string }).prompt;
        return JSON.stringify({ status: "completed", artifacts: [] });
      },
      runCodex: async () => { throw new Error("runCodex should not be called by Stage 1"); },
    };

    await runStage1({ ctx, state, deps });

    expect(prompt).not.toContain("=== REVISE REUSE SCOPE ===");
    expect(prompt).not.toContain("Keep every settled reuse/define-local decision in the existing plan");
    expect(prompt).toContain("Write the formalization plan JSON");
  });
});
