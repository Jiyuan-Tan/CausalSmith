/**
 * Stage 2 (Lean scaffold) handler tests: the post-sync plan gate, revise-mode
 * file and proof preservation, the undelivered directive, node-anchor
 * discovery, and the completed / blocked-missing-architecture results.
 */
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStage2 } from "../../src/formalization/stage2.js";
import {
  findDuplicateLeanNodeAnchors,
  parseLeanNodeTags,
  undeliveredBlockFromPlan,
  blockingPostSyncPlanViolations,
  canonicalizeCitedPlanAfterF2,
  restoreDeletedReviseFiles,
} from "../../src/formalization/stage2.js";
import { promptPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { buildGraphFromCorePlan } from "../../src/graph/from_core.js";
import { graphDerivedSkeleton } from "../../src/graph/skeleton.js";
import { convergenceTargets } from "../../src/graph/review_scope.js";

let repoRoot: string;

describe("F2 post-sync plan gate", () => {
  it("blocks structural P2/P4 drift but leaves P5/P6 lookup drift advisory", () => {
    const violations = [
      { code: "P2", where: "def:class", message: "non-member" },
      { code: "P4", where: "thm:main", message: "uncovered assumption" },
      { code: "P5", where: "thm:main", message: "reuse lookup" },
      { code: "P6", where: "thm:main", message: "module lookup" },
    ] as const;
    expect(blockingPostSyncPlanViolations(violations as never).map((v) => v.code)).toEqual(["P2", "P4"]);
  });

  it("canonicalizes null optional keys and restores cited provenance on Prop and metadata defs", () => {
    const plan = {
      nodes: {
        "lem:prop-citation": { lean_kind: "assumption", gate: false, gate_class: null },
        "lem:scope-citation": { lean_kind: "def", gate: false, gate_class: null },
        "thm:unstamped-discharge": { lean_kind: "theorem", gate: false, gate_class: null },
        "thm:ordinary": { lean_kind: "theorem", gate: null, gate_class: null },
      },
    };
    const core = {
      statements: [
        { id: "lem:prop-citation", status: "cited", source: { carrier: "logical-claim" } },
        { id: "lem:scope-citation", status: "cited", source: { carrier: "bibliographic-metadata" } },
        { id: "thm:unstamped-discharge", status: "cited", source: { carrier: "logical-claim" } },
        { id: "thm:ordinary", status: "proved" },
      ],
    } as never;

    const result = canonicalizeCitedPlanAfterF2(plan, core);
    expect(result.changed).toBe(true);
    expect(plan.nodes["lem:prop-citation"]).toMatchObject({ gate: true, gate_class: "cited" });
    expect(plan.nodes["lem:scope-citation"]).toMatchObject({ gate: true, gate_class: "cited" });
    expect(plan.nodes["thm:unstamped-discharge"]).toEqual({ lean_kind: "theorem", gate: false });
    expect(plan.nodes["thm:ordinary"]).toEqual({ lean_kind: "theorem" });
  });

  it("keeps a canonicalized cited metadata def on the graph and F4 source-review surface", () => {
    const core = {
      qid: "cited_metadata",
      specialization: "v1",
      cluster: "stat",
      symbols: [],
      assumptions: [],
      definitions: [],
      statements: [{
        id: "lem:published-scope",
        kind: "lemma",
        statement: "The source is confined to its stated model and makes no broader claim.",
        depends_on: [],
        status: "cited",
        source: { cite: "source", locator: "Theorem 1", carrier: "bibliographic-metadata" },
      }],
      target_estimand: "none",
      bibliography: [],
    } as never;
    const plan = {
      qid: "cited_metadata",
      specialization: "v1",
      env: [],
      nodes: {
        "lem:published-scope": {
          lean_kind: "def",
          lean_name: "PublishedScope",
          disposition: "define-local",
          gate: false,
          gate_class: null,
          source: "cite:source",
        },
      },
      citations: [{
        id: "cite:source",
        title: "Source",
        authors: "Author",
        year: 2026,
        locator: "Theorem 1",
        verbatim_statement: "The source is confined to its stated model.",
      }],
    };

    canonicalizeCitedPlanAfterF2(plan, core);
    const graph = buildGraphFromCorePlan(core, "v1", plan as never);
    const node = graph.nodes.find((candidate) => candidate.id === "lem:published-scope");
    expect(node).toMatchObject({ kind: "gate", gate: { gate_class: "cited", source: "cite:source" } });
    expect(graphDerivedSkeleton(graph)).toContainEqual(expect.objectContaining({
      graph_node_id: "lem:published-scope",
      kind: "assumption",
    }));
    expect(convergenceTargets(graph).assumptionTargets).toContain("lem:published-scope");
  });

  it("restores frozen work metadata and claim edges after an F2 plan rewrite", () => {
    const core = {
      statements: [{
        id: "lem:cited", status: "cited", proof_tex: "ignored fallback",
        source: {
          cite: "Paper2026", locator: "Theorem 4", carrier: "logical-claim",
          verbatim_statement: "Frozen source statement.",
          attestation: { by: "main", note: "checked page 12" },
          doi: "10.1/frozen",
        },
      }],
      bibliography: [{ key: "Paper2026", citation: "A. Author (2026). Frozen title." }],
    } as never;
    const trustedPlan = {
      nodes: { "lem:cited": { source: { citation: "cite:paper", locator: "Theorem 4" } } },
      citations: [{ id: "cite:paper", bibkey: "Paper2026", authors: "A. Author", year: 2026, title: "Frozen title" }],
    };
    const rewritten = {
      nodes: {
        "lem:cited": {
          lean_kind: "assumption", gate: false, gate_class: null,
          source: "cite:paper",
        },
      },
      citations: [{
        id: "cite:paper", bibkey: "Invented", authors: "Invented", year: 1900, title: "Invented",
        locator: "Invented locator", verbatim_statement: "Invented statement.",
        attestation: { by: "d0-agent", note: "invented" },
      }],
    };

    const result = canonicalizeCitedPlanAfterF2(rewritten, core, trustedPlan);

    expect(result.changed).toBe(true);
    expect(rewritten.nodes["lem:cited"]).toMatchObject({
      gate: true,
      gate_class: "cited",
      source: {
        citation: "cite:paper",
        locator: "Theorem 4",
        verbatim_statement: "Frozen source statement.",
        attestation: { by: "main", note: "checked page 12" },
      },
    });
    expect(rewritten.citations).toEqual([{
      id: "cite:paper", bibkey: "Paper2026", authors: "A. Author", year: 2026,
      title: "Frozen title", doi: "10.1/frozen",
    }]);
  });

  it("fails closed when F2 writes duplicate citation ids", () => {
    const core = {
      statements: [{ id: "lem:cited", status: "cited", source: { cite: "Paper2026", locator: "Theorem 1" } }],
      bibliography: [{ key: "Paper2026", citation: "A. Author (2026). Frozen title." }],
    } as never;
    const trustedPlan = {
      nodes: { "lem:cited": { source: { citation: "cite:paper", locator: "Theorem 1" } } },
    };
    const rewritten = {
      nodes: { "lem:cited": { lean_kind: "assumption", source: "cite:paper" } },
      citations: [
        { id: "cite:paper", authors: "A", year: 2026, title: "One" },
        { id: "cite:paper", authors: "B", year: 1900, title: "Two" },
      ],
    };
    expect(() => canonicalizeCitedPlanAfterF2(rewritten, core, trustedPlan)).toThrow(
      "duplicate citation id 'cite:paper'",
    );
  });
});

describe("F2 revise file preservation", () => {
  it("restores a pre-existing module deleted by a revise producer", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "f2-revise-restore-"));
    const file = path.join(dir, "Preserved.lean");
    await writeFile(file, "theorem preserved : True := by trivial\n");
    const snapshot = new Map([[file, await readFile(file, "utf8")]]);
    await rm(file);

    expect(await restoreDeletedReviseFiles(snapshot)).toEqual([file]);
    expect(await readFile(file, "utf8")).toBe("theorem preserved : True := by trivial\n");
    await rm(dir, { recursive: true, force: true });
  });
});

/**
 * Construct a minimal PipelineContext that points at our temp repoRoot.
 * The prompt is written by beforeEach.
 */
function makeCtx(root: string): PipelineContext {
  return {
    repoRoot: root,
    qid: "manski1990test",
    specialization: "default",
    dryRun: false,
    resume: false,
  };
}

/**
 * Minimal StateJson with lean_subdir populated.
 */
function makeState(): StateJson {
  return {
    stage_completed: "1.5",
    lean_subdir: "CausalSmith/PartialID/Manski1990Test",
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
  } as unknown as StateJson;
}

/**
 * Build a fake StageDeps whose runner writes a stub .lean file and returns a
 * completed scaffold reply listing it.
 */
function makeDeps(leanDir: string): StageDeps {
  const leanFilePath = path.join(leanDir, "Manski1990Test.lean");
  const responseJson = JSON.stringify({
    status: "completed",
    message: "scaffold done",
    artifacts: [leanFilePath],
  });

  const write = async () => {
    await mkdir(leanDir, { recursive: true });
    await writeFile(leanFilePath, "-- generated stub\n");
  };
  return {
    // F2 dispatches codex (MODEL_PLAN.stage2) now; keep runClaude wired too so the
    // test is agnostic to the configured runner. The codex path reads `.stdout`.
    runClaude: async (_opts: unknown) => { await write(); return responseJson; },
    runCodex: async (_opts: unknown) => { await write(); return { stdout: responseJson, stderr: "" }; },
  };
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "stage2-paper-layout-"));
  // Write a stub stage2_scaffold.txt prompt (runStage2 reads it).
  const target = promptPath(repoRoot, "stage2_scaffold.txt");
  await mkdir(path.dirname(target), { recursive: true });
  await writeFile(target, "stub prompt");
  await writeFile(promptPath(repoRoot, "stage2_head_revise.txt"), "=== REVISE MODE ===");
});

describe("Stage 2 undelivered directive", () => {
  it("instructs F2 to remove the declaration and never replace it with sorry/gate/Prop", () => {
    const block = undeliveredBlockFromPlan(JSON.stringify({
      qid: "q",
      nodes: {
        "thm:secondary": {
          lean_kind: "theorem",
          lean_name: "secondary",
          disposition: "define-local",
          delivery_role: "secondary",
          delivery_status: "undelivered",
          delivery_reason: "citation overflow",
        },
      },
    }));
    expect(block).toContain("thm:secondary (secondary): citation overflow");
    expect(block).toContain("remove any existing Lean declaration");
    expect(block).toContain("Prop definition, axiom, gate, weakened theorem, or `sorry`");
  });
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("Stage 2 scaffold", () => {
  it("fails closed when a modern research run is missing its typed core", async () => {
    const ctx = { ...makeCtx(repoRoot), qid: "pid_missing_core_test" };
    await expect(runStage2({
      ctx,
      state: makeState(),
      deps: makeDeps(path.join(repoRoot, "unused-lean")),
    })).rejects.toThrow(/required typed core is unreadable/);
  });

  it("discovers node and environment tags recursively in nested helper modules", async () => {
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const nested = path.join(leanDir, "Helpers", "Nested.lean");
    await mkdir(path.dirname(nested), { recursive: true });
    await writeFile(nested, "-- @env: env:nested\n-- @node: thm:nested\ntheorem nested : True := by trivial\n");

    const tags = await parseLeanNodeTags(leanDir);
    expect(tags.nodes).toEqual(new Set(["thm:nested"]));
    expect(tags.envs).toEqual(new Set(["env:nested"]));
  });

  it("ignores indented in-body metadata while retaining column-zero canonical tags", async () => {
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const nested = path.join(leanDir, "Helpers", "Indented.lean");
    await mkdir(path.dirname(nested), { recursive: true });
    await writeFile(
      nested,
      "-- @node: def:primary\ndef primary : Prop :=\n  -- @node: def:primary\n  True\n",
    );

    const tags = await parseLeanNodeTags(leanDir);
    const duplicates = await findDuplicateLeanNodeAnchors(leanDir);

    expect(tags.nodes).toEqual(new Set(["def:primary"]));
    expect(duplicates).toEqual([]);
  });

  it("hard-stops F2 when nested helpers contain duplicate canonical node anchors", async () => {
    const ctx = { ...makeCtx(repoRoot), resume: true };
    const state = makeState();
    state.stage_completed = "5";
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const nested = path.join(leanDir, "Helpers", "Duplicate.lean");
    await mkdir(path.dirname(nested), { recursive: true });
    await writeFile(
      nested,
      "-- @node: thm:duplicate\ntheorem primary : True := by trivial\n" +
        "-- @node: thm:duplicate\nlemma companion : True := by trivial\n",
    );
    const responseJson = JSON.stringify({
      status: "completed",
      message: "scaffold done",
      artifacts: [nested],
    });
    const deps: StageDeps = {
      runClaude: async () => responseJson,
      runCodex: async () => ({ stdout: responseJson, stderr: "" }),
    };

    await expect(runStage2({ ctx, state, deps })).rejects.toThrow(
      /F2 duplicate @node gate failed[\s\S]*thm:duplicate/,
    );
  });

  it("explicit post-F2 resume uses revise semantics and restores unchanged active proofs", async () => {
    const ctx = { ...makeCtx(repoRoot), resume: true };
    const state = makeState();
    state.stage_completed = "5";

    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const leanFile = path.join(leanDir, "Manski1990Test.lean");
    const nestedHelper = path.join(leanDir, "Helpers", "Preserved.lean");
    await mkdir(leanDir, { recursive: true });
    await mkdir(path.dirname(nestedHelper), { recursive: true });
    await writeFile(leanFile, "theorem keepProof (n : Nat) : n + 0 = n := by\n  simp\n");
    await writeFile(nestedHelper, "theorem nestedKeepProof (n : Nat) : n + 0 = n := by\n  simp\n");

    let producerPrompt = "";
    const responseJson = JSON.stringify({
      status: "completed",
      message: "scaffold done",
      artifacts: [leanFile],
    });
    const overwriteWithColdStyleSorry = async (opts: { prompt?: string }) => {
      producerPrompt = opts.prompt ?? "";
      await writeFile(leanFile, "theorem keepProof (n : Nat) : n + 0 = n := by\n  sorry\n");
      return { stdout: responseJson, stderr: "" };
    };
    const deps: StageDeps = {
      runClaude: async (opts: unknown) => (await overwriteWithColdStyleSorry(opts as { prompt?: string })).stdout,
      runCodex: async (opts: unknown) => overwriteWithColdStyleSorry(opts as { prompt?: string }),
    };

    await runStage2({ ctx, state, deps });

    expect(producerPrompt).toContain("On-disk files to patch");
    expect(producerPrompt).toContain(nestedHelper);
    expect(producerPrompt).not.toContain("tag every emitted decl");
    const after = await readFile(leanFile, "utf8");
    expect(after).toMatch(/theorem keepProof \(n : Nat\) : n \+ 0 = n := by\s+simp/);
    expect(after).not.toMatch(/\bsorry\b/);
    expect(after).not.toContain("PRIOR PROOF (carry-over: auto");
    expect(await readFile(nestedHelper, "utf8")).toMatch(/nestedKeepProof[\s\S]*by\s+simp/);
  });

  it("a completed scaffold reply returns completed without raising the missing-architecture flag", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const deps = makeDeps(leanDir);

    const result = await runStage2({ ctx, state, deps });

    expect(result.status).toBe("completed");
    expect(result.stage).toBe("2");
    expect(state.flags.missing_architecture).toBe(false);
  });

  it("a blocked-missing-architecture reply blocks and records the missing items", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();

    const blockedJson = JSON.stringify({
      status: "blocked-missing-architecture",
      message: "missing FooClass",
      missing_items: [
        {
          kind: "typeclass",
          name_suggestion: "FooClass",
          purpose: "needed for theorem t1",
          why_substantial: "full new typeclass",
        },
      ],
    });

    const deps: StageDeps = {
      runClaude: async (_opts: unknown) => blockedJson,
      runCodex: async (_opts: unknown) => ({ stdout: blockedJson, stderr: "" }),
    };

    const result = await runStage2({ ctx, state, deps });

    expect(result.status).toBe("blocked");
    expect(state.flags.missing_architecture).toBe(true);
    expect(state.flags.missing_architecture_items?.[0].name_suggestion).toBe("FooClass");
  });
});
