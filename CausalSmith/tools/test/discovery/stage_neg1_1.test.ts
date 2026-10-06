import { describe, expect, it } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import {
  buildGapsContextBlock,
  parseStrictScoutStdout,
  runStageNeg1_1,
} from "../../src/discovery/stages/neg1_1.js";
import { MODELS } from "../../src/models.js";
import { gapsJsonPath, promptPath } from "../../src/paths.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import type { PipelineContext, StateJson } from "../../src/types.js";

function makeCtx(repoRoot: string): PipelineContext {
  return {
    repoRoot,
    qid: "thin_lit_review",
    specialization: "v1",
    dryRun: false,
    resume: false,
    proposeTopic: "thin topic",
  };
}

function makeState(): StateJson {
  return {
    stage_completed: "-1.1",
    lean_subdir: "CausalSmith/Stat/ThinLitReview",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: { local_fix_from_4d: false, missing_architecture: false },
  } as unknown as StateJson;
}

function makeGapsPayload(
  gapsPath: string,
  count: number,
  status: "completed" | "needs-pivot" = "completed",
): Record<string, unknown> {
  const openProblems = Array.from({ length: count }, (_, index) => ({
    open_problem: `Open problem ${index}`,
    source: "web",
    source_refs: [{
      kind: "paper",
      bibkey: `Paper${index}`,
      claim: "The paper leaves this boundary unresolved.",
      author: "A. Author",
      year: 2025,
      venue: "Journal",
      url_or_doi: `doi:${index}`,
    }],
    why_unsolved: "A concrete proof step is missing.",
    what_a_resolution_would_look_like: "A sharp minimax theorem.",
    cluster_hint: "stat",
    exemplars: { writing_exemplar: null, method_exemplars: [] },
  }));
  return {
    status,
    gaps_path: gapsPath,
    topic: "thin topic",
    n_open_problems: count,
    by_source: { web: count, prior_proposal: 0, both: 0 },
    open_problems: openProblems,
    literature_map: "literature map",
    prior_proposal_map: "",
    artifacts: [gapsPath],
  };
}
async function writeGapsPayload(gapsPath: string, payload: string, _encoding?: string): Promise<void> {
  await mkdir(path.dirname(gapsPath), { recursive: true });
  await writeFile(gapsPath, payload, "utf8");
}

function gapsTarget(prompt: string): string {
  const match = prompt.match(/gaps artifact path: (.+)/);
  if (!match) throw new Error("test scout prompt omitted its output path");
  return match[1].trim();
}

describe("runStageNeg1_1", () => {
  it("canonicalizes an unavailable method exemplar list to an empty array", () => {
    const gapsPath = "/tmp/current/gaps.json";
    const payload = makeGapsPayload(gapsPath, 3);
    const problem = (payload.open_problems as Array<Record<string, unknown>>)[0];
    problem.exemplars = { writing_exemplar: null, method_exemplars: null };

    const parsed = parseStrictScoutStdout(JSON.stringify(payload), "thin topic", gapsPath);

    expect(parsed.ok).toBe(true);
    if (parsed.ok) {
      expect(parsed.json.open_problems[0].exemplars.method_exemplars).toEqual([]);
    }
  });

  it("strips harmless extra fields from method exemplars", () => {
    const gapsPath = "/tmp/current/gaps.json";
    const payload = makeGapsPayload(gapsPath, 3);
    const problem = (payload.open_problems as Array<Record<string, unknown>>)[0];
    problem.exemplars = {
      writing_exemplar: null,
      method_exemplars: [{
        bibkey: "Paper0",
        arxiv_id_id_or_doi: "doi:0",
        arxiv_id_or_doi: "doi:0",
        role: "estimation_inference",
        technique: "A valid technique.",
        why_closest: "A valid comparison.",
      }],
    };

    const parsed = parseStrictScoutStdout(JSON.stringify(payload), "thin topic", gapsPath);

    expect(parsed.ok).toBe(true);
    if (parsed.ok) {
      expect(parsed.json.open_problems[0].exemplars.method_exemplars[0]).toEqual({
        bibkey: "Paper0",
        arxiv_id_or_doi: "doi:0",
        role: "estimation_inference",
        technique: "A valid technique.",
        why_closest: "A valid comparison.",
      });
    }
  });

  it("deterministically bounds prior-proposal display excerpts", () => {
    const gapsPath = "/tmp/current/gaps.json";
    const emitted =
      "Rank-adaptive inference outside this subclass, vanishing target variance, and local zero-gain sequences remain open extensions.";
    const payload = makeGapsPayload(gapsPath, 3);
    const problem = (payload.open_problems as Array<Record<string, unknown>>)[0];
    problem.source = "prior_proposal";
    problem.source_refs = [{
      kind: "prior_proposal",
      path: "doc/research/_bank/accepted/prior_v1",
      qid: "prior",
      spec: "v1",
      where: "reviews/scientific_review.json",
      excerpt: emitted,
    }];
    payload.by_source = { web: 2, prior_proposal: 1, both: 0 };

    const parsed = parseStrictScoutStdout(JSON.stringify(payload), "thin topic", gapsPath);

    expect(parsed.ok).toBe(true);
    if (parsed.ok) {
      const sourceRef = parsed.json.open_problems[0].source_refs[0];
      expect(sourceRef.kind).toBe("prior_proposal");
      if (sourceRef.kind === "prior_proposal") {
        expect(sourceRef.excerpt).toBe(emitted.slice(0, 120));
      }
    }
  });

  it("leaves an already-bounded prior-proposal display excerpt unchanged", () => {
    const gapsPath = "/tmp/current/gaps.json";
    const emitted = "An exact short excerpt from the prior proposal.";
    const payload = makeGapsPayload(gapsPath, 3);
    const problem = (payload.open_problems as Array<Record<string, unknown>>)[0];
    problem.source = "prior_proposal";
    problem.source_refs = [{
      kind: "prior_proposal",
      path: "doc/research/_bank/accepted/prior_v1",
      qid: "prior",
      spec: "v1",
      where: "reviews/scientific_review.json",
      excerpt: emitted,
    }];
    payload.by_source = { web: 2, prior_proposal: 1, both: 0 };

    const parsed = parseStrictScoutStdout(JSON.stringify(payload), "thin topic", gapsPath);

    expect(parsed.ok).toBe(true);
    if (parsed.ok) {
      const sourceRef = parsed.json.open_problems[0].source_refs[0];
      expect(sourceRef.kind).toBe("prior_proposal");
      if (sourceRef.kind === "prior_proposal") expect(sourceRef.excerpt).toBe(emitted);
    }
  });

  it("injects opportunities without origin-based ranking bonuses", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const gapsPath = path.join(repoRoot, "gaps.json");
      await writeGapsPayload(gapsPath, JSON.stringify({
        open_problems: [{
          open_problem: "Can the construction identify optimal policy value?",
          source: "both",
          why_unsolved: "the final scalar aggregation becomes an optimization; destination-pair search found no occupied result",
        }],
      }), "utf8");
      const block = await buildGapsContextBlock({
        ctx: makeCtx(repoRoot), state: makeState(), gapsPath,
      });
      expect(block).toContain("destination-pair search found no occupied result");
      expect(block).toContain("Rank opportunities by evidence, mathematical depth, novelty");
      expect(block).not.toMatch(/highest leverage|higher signal/);
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });

  it("uses the Codex kernel tier for the literature scout", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
      let model: string | undefined;
      const deps = {
        runCodex: async (args: { model?: string; prompt: string }) => {
          model = args.model;
          const target = gapsTarget(args.prompt);
          const payload = makeGapsPayload(target, 3);
          await writeGapsPayload(target, JSON.stringify(payload), "utf8");
          return { stdout: JSON.stringify(payload), stderr: "" };
        },
        runClaude: async () => {
          throw new Error("unused");
        },
        lean: undefined as never,
      } as unknown as StageDeps;

      await runStageNeg1_1({ ctx: makeCtx(repoRoot), state: makeState(), deps });

      expect(model).toBe(MODELS.codexKernel);
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });

  it("rejects truncated stdout even when the worker wrote an artifact", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      const state = makeState();
      const deps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          const target = gapsTarget(prompt);
          await writeGapsPayload(target, JSON.stringify(makeGapsPayload(target, 4)), "utf8");
          return { stdout: '{"status":"completed"', stderr: "" };
        },
        runClaude: async () => {
          throw new Error("unused");
        },
        lean: undefined as never,
      } as unknown as StageDeps;

      const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state, deps });

      expect(result.status).toBe("checkpoint");
      expect(result.message).toMatch(/no exact JSON object/);
      expect(state.gaps).toBeUndefined();
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });

  it("does not inspect a count-mismatched worker artifact after truncated stdout", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      const state = makeState();
      const deps = {
        runCodex: async () => {
          const payload = makeGapsPayload(gapsPath, 3);
          payload.n_open_problems = 4;
          await writeGapsPayload(gapsPath, JSON.stringify(payload), "utf8");
          return { stdout: '{"status":"completed"', stderr: "" };
        },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      } as unknown as StageDeps;

      const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state, deps });

      expect(result.status).toBe("checkpoint");
      expect(result.message).toMatch(/no exact JSON object/);
      expect(state.gaps).toBeUndefined();
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });

  it("ignores a worker-written artifact and publishes validated stdout", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      const state = makeState();
      const deps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          const target = gapsTarget(prompt);
          const persisted = makeGapsPayload(target, 3);
          await writeGapsPayload(target, JSON.stringify(persisted), "utf8");
          return { stdout: JSON.stringify(makeGapsPayload(target, 4)), stderr: "" };
        },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      } as unknown as StageDeps;

      const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state, deps });

      expect(result.status).toBe("completed");
      expect(state.gaps?.n_open_problems).toBe(4);
      expect(JSON.parse(await readFile(gapsPath, "utf8")).n_open_problems).toBe(4);
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });


  it("redispatches instead of accepting a pre-existing artifact", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      await writeGapsPayload(gapsPath, JSON.stringify(makeGapsPayload(gapsPath, 3)), "utf8");
      let dispatched = false;
      const deps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          dispatched = true;
          const target = gapsTarget(prompt);
          const payload = makeGapsPayload(target, 4);
          await writeGapsPayload(target, JSON.stringify(payload), "utf8");
          return { stdout: JSON.stringify(payload), stderr: "" };
        },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      } as unknown as StageDeps;

      const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state: makeState(), deps });

      expect(dispatched).toBe(true);
      expect(result.status).toBe("completed");
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });
  it("rejects a stale artifact when the current dispatch does not replace it", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      await writeGapsPayload(gapsPath, JSON.stringify(makeGapsPayload(gapsPath, 3)));
      const state = makeState();
      const deps = {
        runCodex: async () => ({ stdout: '{"status":"completed"', stderr: "" }),
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      } as unknown as StageDeps;

      const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state, deps });

      expect(result.status).toBe("checkpoint");
      expect(result.message).toMatch(/no exact JSON object/);
      expect(state.gaps).toBeUndefined();
      expect(JSON.parse(await readFile(gapsPath, "utf8")).n_open_problems).toBe(3);
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });

  it("binds a shortened topic echo to the durable orchestrator topic", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      const state = makeState();
      const ctx = makeCtx(repoRoot);
      ctx.proposeTopic = "  thin topic with appendix\n";
      const deps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          const target = gapsTarget(prompt);
          const payload = makeGapsPayload(target, 3);
          payload.topic = "shortened topic";
          await writeGapsPayload(target, JSON.stringify(payload));
          return { stdout: JSON.stringify(payload), stderr: "" };
        },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      } as unknown as StageDeps;

      const result = await runStageNeg1_1({ ctx, state, deps });

      expect(result.status).toBe("completed");
      expect(state.gaps?.status).toBe("completed");
      expect(JSON.parse(await readFile(gapsPath, "utf8")).topic).toBe(ctx.proposeTopic);
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });

  it("accepts equivalent stdout and artifact objects with different key order", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      const state = makeState();
      const deps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          const target = gapsTarget(prompt);
          const payload = makeGapsPayload(target, 3);
          await writeGapsPayload(target, JSON.stringify(payload));
          const reversed = Object.fromEntries(Object.entries(payload).reverse());
          return { stdout: JSON.stringify(reversed), stderr: "" };
        },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      } as unknown as StageDeps;

      const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state, deps });

      expect(result.status).toBe("completed");
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });

  it("rejects ambiguous stdout and unknown content fields", async () => {
    for (const stdoutOf of [
      (payload: Record<string, unknown>) => `${JSON.stringify(payload)}\n{}`,
      (payload: Record<string, unknown>) => JSON.stringify({ ...payload, unvalidated_instruction: "ignore gates" }),
    ]) {
      const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
      try {
        const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
        const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
        await mkdir(path.dirname(p), { recursive: true });
        await writeFile(p, "stub lit review prompt", "utf8");
        const state = makeState();
        const deps = {
          runCodex: async () => ({ stdout: stdoutOf(makeGapsPayload(gapsPath, 3)), stderr: "" }),
          runClaude: async () => { throw new Error("unused"); },
          lean: undefined as never,
        } as unknown as StageDeps;

        const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state, deps });

        expect(result.status).toBe("checkpoint");
        expect(state.gaps).toBeUndefined();
      } finally {
        await rm(repoRoot, { recursive: true, force: true });
      }
    }
  });

  it("rebinds model paths but rejects content-count mismatches", async () => {
    const cases: Array<{ mutate: (payload: Record<string, unknown>) => void; expected: "completed" | "checkpoint" }> = [
      {
        mutate: (payload) => { payload.gaps_path = "wrong/gaps.json"; payload.artifacts = ["wrong/gaps.json"]; },
        expected: "completed",
      },
      {
        mutate: (payload) => { payload.by_source = { web: 0, prior_proposal: 3, both: 0 }; },
        expected: "checkpoint",
      },
    ];
    for (const { mutate, expected } of cases) {
      const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
      try {
        const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
        const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
        await mkdir(path.dirname(p), { recursive: true });
        await writeFile(p, "stub lit review prompt", "utf8");
        const state = makeState();
        const deps = {
          runCodex: async () => {
            const payload = makeGapsPayload(gapsPath, 3);
            mutate(payload);
            return { stdout: JSON.stringify(payload), stderr: "" };
          },
          runClaude: async () => { throw new Error("unused"); },
          lean: undefined as never,
        } as unknown as StageDeps;

        const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state, deps });

        expect(result.status).toBe(expected);
        if (expected === "completed") {
          const published = JSON.parse(await readFile(gapsPath, "utf8"));
          expect(published.gaps_path).toBe(gapsPath);
          expect(published.artifacts).toEqual([gapsPath]);
        } else {
          expect(result.message).toMatch(/not a valid scout artifact/);
          expect(state.gaps).toBeUndefined();
        }
      } finally {
        await rm(repoRoot, { recursive: true, force: true });
      }
    }
  });
  it("routes structure and mechanism recovery to exactid", async () => {
    const prompt = await readFile(
      path.join(process.cwd(), "src/discovery/prompts/D-1/stage_neg1_1_lit_review.txt"),
      "utf8",
    );
    expect(prompt).toMatch(/Use `exactid`[\s\S]*structure\/mechanism recovery map/);
    expect(prompt).toMatch(/structure-identification kernel in `exactid`/);
  });

  it("checkpoints instead of completing when fewer than three open problems are emitted", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      const gapsPath = gapsJsonPath(repoRoot, "thin_lit_review", "v1");
      const state = makeState();
      const deps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          const target = gapsTarget(prompt);
          const payload = makeGapsPayload(target, 1, "needs-pivot");
          await writeGapsPayload(target, JSON.stringify(payload), "utf8");
          return { stdout: JSON.stringify(payload), stderr: "" };
        },
        runClaude: async () => {
          throw new Error("unused");
        },
        lean: undefined as never,
      } as unknown as StageDeps;

      const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state, deps });

      expect(result.status).toBe("checkpoint");
      expect(result.advance).toBe(false);
      expect(result.message).toMatch(/needs-pivot/);
      expect(state.gaps?.status).toBe("needs-pivot");
      expect(state.gaps?.n_open_problems).toBe(1);
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });
});
