// A re-plan (F1) and the review of a re-plan (F1.5) carry the nodes the change affects, not the
// whole core and plan (`revise_scope.ts`).

import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { CoreSchema } from "../../src/discovery/core/schema.js";
import { formalizationCoreContextValue } from "../../src/formalization/core_context.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";
import { replanReviewContext } from "../../src/formalization/review_codex.js";
import { beyondScopeReported, coreChangeSeeds, planChangeSeeds, reviseAffectedNodeIds } from "../../src/formalization/revise_scope.js";
import { runStage1 } from "../../src/formalization/stage1.js";
import { pipelineLogPath, planCorePath, planPath, promptPath } from "../../src/paths.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import type { PipelineContext, StateJson } from "../../src/types.js";

const QID = "pid_revisescopetest";

function rawCore(): Record<string, any> {
  return {
    qid: QID,
    symbols: [
      { name: "x", type: "real" },
      { name: "z", type: "real" },
    ],
    assumptions: [
      { id: "ass:shared", condition: "x is positive", free_symbols: ["x"], standard: { name: "positivity", cite: "fixture" } },
      { id: "ass:unrelated", condition: "UNRELATED_SENTINEL z is bounded", free_symbols: ["z"], standard: { name: "boundedness", cite: "fixture" } },
    ],
    definitions: [
      { id: "def:shared", name: "Shared", construction: "objects satisfying ass:shared", free_symbols: ["x"], by_member_properties: ["ass:shared"] },
    ],
    statements: [
      { id: "thm:target", kind: "theorem", statement: "target about x", free_symbols: ["x"], depends_on: ["def:shared"], route: "direct", status: "to-prove", proof_tex: "PROOF_SENTINEL" },
      { id: "lem:consumer", kind: "lemma", statement: "CONSUMER_SENTINEL uses target", free_symbols: ["x"], depends_on: ["thm:target"], status: "to-prove" },
      { id: "lem:unrelated", kind: "lemma", statement: "unrelated z result", free_symbols: ["z"], depends_on: ["ass:unrelated"], status: "to-prove" },
    ],
    sampling_model: { observed: "x" },
    target_estimand: "x",
    bibliography: [],
  };
}

function rawPlan(): Record<string, any> {
  const node = (lean_kind: string, lean_name: string, extra = {}) => ({
    lean_kind, lean_name, disposition: "define-local", reuse: null, modules: [], ...extra,
  });
  return {
    qid: QID,
    env: [{ id: "S1", world: "world", binds_symbols: ["x", "z"], binds_sampling_model: true, disposition: "define-local" }],
    nodes: {
      "ass:shared": node("assumption", "SharedAssumption"),
      "ass:unrelated": node("assumption", "UnrelatedAssumption"),
      "def:shared": node("structure", "Shared", { members: ["ass:shared"] }),
      "thm:target": node("theorem", "targetTheorem", { hyps: ["def:shared"] }),
      "lem:consumer": node("lemma", "consumerLemma"),
      "lem:unrelated": node("lemma", "unrelatedLemma", { hyps: ["ass:unrelated"] }),
    },
    citations: [],
  };
}

describe("the affected set of a revise", () => {
  const core = CoreSchema.parse(rawCore());
  const plan = PlanSchema.parse(rawPlan());

  it("a changed assumption reaches the class bundling it and the statements taking that class", () => {
    expect([...reviseAffectedNodeIds(core, plan, ["ass:shared"])].sort())
      .toEqual(["ass:shared", "def:shared", "thm:target"]);
  });

  it("a changed ordinary statement does not reach the statements that use it as a lemma", () => {
    expect([...reviseAffectedNodeIds(core, plan, ["thm:target", "not:a-node"])]).toEqual(["thm:target"]);
  });

  it("a statement the plan threads as a hypothesis is a premise: its users are affected", () => {
    const gated = PlanSchema.parse(rawPlan());
    gated.nodes["thm:target"]!.gate = true;
    expect(reviseAffectedNodeIds(core, gated, ["thm:target"]).has("lem:consumer")).toBe(true);
  });
});

describe("what moved between two cores and two plans", () => {
  it("a reworded node and a changed symbol's users are seeds; proof text is not in the view", () => {
    const before = formalizationCoreContextValue(CoreSchema.parse(rawCore()));
    const edited = rawCore();
    edited.statements[2].statement = "unrelated z result, sharpened";
    edited.statements[0].proof_tex = "A NEW PROOF";
    expect(coreChangeSeeds(before, formalizationCoreContextValue(CoreSchema.parse(edited))))
      .toEqual({ nodes: ["lem:unrelated"], symbols: [] });
    const resym = rawCore();
    resym.symbols[1].type = "nonnegative real";
    const moved = coreChangeSeeds(before, formalizationCoreContextValue(CoreSchema.parse(resym)));
    expect(moved.symbols).toEqual(["z"]);
    expect(moved.nodes.sort()).toEqual(["ass:unrelated", "lem:unrelated"]);
    // A symbol naming a changed definition carries the change to the nodes that use the symbol.
    const withRef = rawCore();
    withRef.symbols[1].ref = "def:shared";
    const redefined = structuredClone(withRef);
    redefined.definitions[0].construction = "objects satisfying ass:shared, restated";
    const viaSymbol = coreChangeSeeds(
      formalizationCoreContextValue(CoreSchema.parse(withRef)),
      formalizationCoreContextValue(CoreSchema.parse(redefined)),
    );
    expect(viaSymbol.nodes.sort()).toEqual(["ass:unrelated", "def:shared", "lem:unrelated"]);
  });

  it("a changed entry is named; a removed entry or a plan-level change is `other`", () => {
    const edited = rawPlan();
    edited.nodes["thm:target"].lean_name = "renamed";
    expect(planChangeSeeds(rawPlan(), edited)).toEqual({ nodes: ["thm:target"], envs: [], other: false });
    const removed = rawPlan();
    delete removed.nodes["lem:consumer"];
    expect(planChangeSeeds(rawPlan(), removed).other).toBe(true);
    expect(planChangeSeeds(rawPlan(), { ...rawPlan(), feasibility: "needs-new-infrastructure" }).other).toBe(true);
  });
});

describe("F1.5 review of a re-plan", () => {
  const core = CoreSchema.parse(rawCore());
  const paths = { plan: "/p/plan.json", core: "/p/core.json" };
  const basis = { plan: rawPlan(), core: formalizationCoreContextValue(core) };

  it("carries the changed entry and its context, and a reference line for the rest", () => {
    const planRaw = rawPlan();
    planRaw.nodes["lem:unrelated"].lean_name = "unrelatedLemmaV2";
    const scoped = replanReviewContext({ basis, planRaw, plan: PlanSchema.parse(planRaw), core, paths });
    expect(scoped?.changed).toEqual(["lem:unrelated"]);
    expect(scoped!.block).toContain("unrelatedLemmaV2");
    expect(scoped!.block).toContain("thm:target | theorem | theorem targetTheorem");
    expect(scoped!.block).not.toContain("target about x");
  });

  it("reviews the whole plan with no record, with nothing moved, and on a plan-level change", () => {
    const planRaw = rawPlan();
    const plan = PlanSchema.parse(planRaw);
    expect(replanReviewContext({ basis: null, planRaw, plan, core, paths })).toBeNull();
    expect(replanReviewContext({ basis, planRaw, plan, core, paths })).toBeNull();
    const cited = { ...rawPlan(), citations: [{ id: "c1", bibkey: "k", authors: "A", title: "T", year: 2020 }] };
    expect(replanReviewContext({ basis, planRaw: cited, plan, core, paths })).toBeNull();
    const resampled = CoreSchema.parse({ ...rawCore(), sampling_model: { observed: "x and z" } });
    const moved = rawPlan();
    moved.nodes["lem:unrelated"].lean_name = "unrelatedLemmaV2";
    expect(replanReviewContext({ basis, planRaw: moved, plan: PlanSchema.parse(moved), core: resampled, paths })).toBeNull();
    expect(beyondScopeReported('{"status":"pass","notes":"`looked_up_beyond_scope`: [lem:consumer, S1]"}')).toEqual(["lem:consumer", "S1"]);
  });
});

describe("F1 revise prompt", () => {
  let repoRoot: string;
  const ctx = (): PipelineContext => ({ repoRoot, qid: QID, specialization: "default", dryRun: false, resume: false }) as PipelineContext;
  const state = (): StateJson => ({
    stage_completed: "0.5",
    lean_subdir: "CausalSmith/PartialID/ReviseScopeTest",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    flags: { missing_architecture: false },
  }) as unknown as StateJson;
  const corePath = (): string => path.join(repoRoot, "doc", "research", "active", QID, "discovery", "core.json");
  const run = async (): Promise<string> => {
    let prompt = "";
    const deps: StageDeps = {
      runClaude: async (o: unknown) => {
        prompt = (o as { prompt: string }).prompt;
        const p = planPath(repoRoot, QID, "default");
        await mkdir(path.dirname(p), { recursive: true });
        await writeFile(p, JSON.stringify(rawPlan()), "utf8");
        return JSON.stringify({ status: "completed", artifacts: [] });
      },
      runCodex: async () => { throw new Error("runCodex should not be called by Stage 1"); },
    };
    await runStage1({ ctx: ctx(), state: state(), deps });
    return prompt;
  };

  beforeEach(async () => {
    repoRoot = await mkdtemp(path.join(tmpdir(), "revise-scope-"));
    for (const name of ["stage1_template.txt", "stage1_head_revise.txt"]) {
      const p = promptPath(repoRoot, name);
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, `stub ${name}`, "utf8");
    }
    await mkdir(path.dirname(corePath()), { recursive: true });
    await writeFile(corePath(), JSON.stringify(rawCore(), null, 2), "utf8");
    // A later stage ran: with a plan on disk, F1 patches it.
    await mkdir(path.dirname(pipelineLogPath(repoRoot, QID, "default")), { recursive: true });
    await writeFile(pipelineLogPath(repoRoot, QID, "default"), JSON.stringify({ stage: "3", status: "completed" }) + "\n", "utf8");
  });
  afterEach(async () => {
    await rm(repoRoot, { recursive: true, force: true });
  });

  it("a first plan reads the whole core; a re-plan reads the nodes that moved since", async () => {
    const first = await run();
    expect(first).toContain("PROOF_SENTINEL");
    expect(first).toContain("UNRELATED_SENTINEL");
    expect(JSON.parse(await readFile(planCorePath(repoRoot, QID), "utf8")).statements).toHaveLength(3);

    const edited = rawCore();
    edited.assumptions[0].condition = "x is strictly positive";
    await writeFile(corePath(), JSON.stringify(edited, null, 2), "utf8");
    const second = await run();
    expect(second).toContain("WHAT CHANGED IN THE CORE");
    expect(second).toContain("x is strictly positive");
    expect(second).toContain("target about x");
    expect(second).toContain("lem:unrelated | lemma | lemma unrelatedLemma");
    for (const absent of ["UNRELATED_SENTINEL", "CONSUMER_SENTINEL", "PROOF_SENTINEL"]) expect(second).not.toContain(absent);
    expect(await readFile(pipelineLogPath(repoRoot, QID, "default"), "utf8")).toContain("3 of 6 core nodes");
  });

  it("a re-plan with no record of the plan's core reads the whole core view", async () => {
    await run();
    await rm(planCorePath(repoRoot, QID));
    const second = await run();
    expect(second).toContain("UNRELATED_SENTINEL");
    expect(second).toContain("CONSUMER_SENTINEL");
    expect(second).not.toContain("PROOF_SENTINEL");
  });
});
