import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { runPlanGate, type PlanGateViolation } from "../../src/formalization/plan/plan_gate.js";
import type { Core } from "../../src/discovery/core/schema.js";
import { addNode, markPassed, setLean, setNodeReview, setProof } from "../../src/graph/mutate.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { statementHash } from "../../src/graph/hash.js";
import type { ExtractedDecl } from "../../src/graph/extractor.js";

// A small, schema-valid core exercising every node kind: a standalone atom, two
// shared member atoms, a class, a construction, and a theorem.
function makeCore(): Core {
  return {
    qid: "panel_demo",
    specialization: "v1",
    cluster: "stat",
    symbols: [
      { name: "X", type: "covariate" },
      { name: "Y", type: "outcome" },
      { name: "e", type: "propensity" },
    ],
    assumptions: [
      { id: "ass:overlap", condition: "0 < e(X) < 1", free_symbols: ["e", "X"], novel: { flag: true, justification: "weak overlap regime" } },
      { id: "ass:consistency", condition: "Y = Y(D)", free_symbols: ["Y"], novel: { flag: true, justification: "PO consistency" } },
      { id: "ass:ignorability", condition: "(Y(1),Y(0)) ⫫ D | X", free_symbols: ["Y", "X"], novel: { flag: true, justification: "unconfoundedness" } },
    ],
    definitions: [
      { id: "def:overlap-class", name: "OverlapClass", construction: "{ P : P satisfies ass:consistency, ass:ignorability }", by_member_properties: ["ass:consistency", "ass:ignorability"] },
      { id: "def:estimator", name: "tauHat", construction: "tauHat = average of psi", inputs: ["O"] },
    ],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "tauHat → tau", depends_on: ["ass:overlap", "ass:consistency", "ass:ignorability", "def:overlap-class", "def:estimator"], status: "proved" },
      { id: "oeq:tight", kind: "openendedquestion", statement: "is the feasible rate tight?", depends_on: ["thm:main"], status: "to-prove" },
    ],
    target_estimand: "tau = E[Y(1) - Y(0)]",
    bibliography: [],
  } as Core;
}

// A plan that maps makeCore() one-to-one. `consistency`/`ignorability` are reached
// by `thm:main` through the bundled class, so they need not be re-listed in hyps.
function makePlan() {
  return {
    qid: "panel_demo",
    specialization: "v1",
    cluster: "stat",
    lean_subdir: "Stat/Demo",
    env: [
      { id: "S1", world: "po-system", binds_symbols: ["X", "Y", "e"], binds_sampling_model: true, disposition: "reuse", reuse: "Causalean.PO.System.POStructure", modules: ["Causalean.PO.System"] },
    ],
    nodes: {
      "ass:overlap": { lean_kind: "assumption", lean_name: "assOverlap", disposition: "define-local", modules: ["Causalean.PO.Overlap"] },
      "ass:consistency": { lean_kind: "assumption", lean_name: "assConsistency", disposition: "define-local" },
      "ass:ignorability": { lean_kind: "assumption", lean_name: "assIgnorability", disposition: "define-local" },
      "def:overlap-class": { lean_kind: "structure", lean_name: "OverlapClass", members: ["ass:consistency", "ass:ignorability"], disposition: "define-local" },
      "def:estimator": { lean_kind: "def", lean_name: "tauHat", disposition: "define-local" },
      "thm:main": { lean_kind: "theorem", lean_name: "main", target_file: "Basic.lean", hyps: ["ass:overlap", "def:overlap-class"], disposition: "define-local" },
      "oeq:tight": { lean_kind: "def", lean_name: "tightOpenQuestion", disposition: "define-local" },
    },
    feasibility: "formalizable-now",
  };
}

function codes(vs: PlanGateViolation[]): string[] {
  return vs.map((v) => v.code);
}

describe("F1 plan gate — golden minimal plan", () => {
  it("a one-to-one plan over the demo core passes every check", () => {
    const res = runPlanGate(makePlan(), makeCore());
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });
});

describe("F1 plan gate — P1 coverage", () => {
  it("flags a missing node entry", () => {
    const plan = makePlan();
    delete (plan.nodes as Record<string, unknown>)["ass:overlap"];
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P1");
  });
  it("flags an extra node entry that is not a core node", () => {
    const plan = makePlan();
    (plan.nodes as Record<string, unknown>)["ass:bogus"] = { lean_kind: "assumption", lean_name: "x", disposition: "define-local" };
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P1");
  });
  it("accepts a secondary theorem only after it is synchronized into both core and plan", () => {
    const plan = makePlan();
    (plan.nodes as Record<string, unknown>)["thm:secondary-comparison"] = {
      lean_kind: "theorem",
      lean_name: "secondaryComparison",
      disposition: "define-local",
      target_file: "Comparison.lean",
      hyps: [],
      delivery_role: "secondary",
    };
    expect(runPlanGate(plan, makeCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P1", where: "thm:secondary-comparison" }),
    );
    const core = makeCore();
    core.statements.push({
      id: "thm:secondary-comparison",
      kind: "theorem",
      statement: "secondary comparison",
      depends_on: [],
      proof_tex: "Immediate from the proved comparison.",
      status: "proved",
    });
    expect(runPlanGate(plan, core).violations).toEqual([]);
  });
  it("flags an unbound symbol", () => {
    const plan = makePlan();
    plan.env[0].binds_symbols = ["X", "Y"]; // drops 'e'
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P1");
  });
});

describe("F1 plan gate — paper-owned proof obligations", () => {
  it("rejects a proved paper statement deferred without an external gate", () => {
    const plan = makePlan();
    (plan.nodes["thm:main"] as Record<string, unknown>).defer_tier = true;
    plan.feasibility = "needs-new-infrastructure";
    expect(runPlanGate(plan, makeCore()).violations).toContainEqual(
      expect.objectContaining({
        code: "P8",
        where: "thm:main",
        message: expect.stringContaining("paper-owned proved/to-prove statement"),
      }),
    );
  });
  it("rejects a paper-owned statement relabeled as an external gate", () => {
    const plan = makePlan();
    Object.assign(plan.nodes["thm:main"], {
      lean_kind: "assumption",
      defer_tier: true,
      gate: true,
      gate_class: "gated",
    });
    plan.feasibility = "needs-new-infrastructure";
    expect(runPlanGate(plan, makeCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P8", where: "thm:main", message: expect.stringContaining("planner-authored external gate") }),
    );
  });
  it("rejects deferred paper work even when the planner marks it undelivered", () => {
    const plan = makePlan();
    Object.assign(plan.nodes["thm:main"], {
      defer_tier: true,
      delivery_status: "undelivered",
      delivery_role: "secondary",
      delivery_reason: "too difficult",
    });
    plan.feasibility = "formalizable-now";
    expect(runPlanGate(plan, makeCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P8", where: "thm:main", message: expect.stringContaining("paper-owned proved/to-prove statement") }),
    );
  });
});

describe("F1 plan gate — P2/P3 structure", () => {
  it("flags a class whose members disagree with by_member_properties", () => {
    const plan = makePlan();
    plan.nodes["def:overlap-class"].members = ["ass:consistency"]; // drops ignorability
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P2");
  });
  it("flags a wrong lean_kind for a core kind", () => {
    const plan = makePlan();
    plan.nodes["def:overlap-class"].lean_kind = "def"; // class must be structure
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P3");
  });
  it("allows an open-ended question to be realized as a non-theorem Prop def", () => {
    const res = runPlanGate(makePlan(), makeCore());
    expect(res.violations.filter((v) => v.where === "oeq:tight")).toEqual([]);
  });
  it("rejects theorem/lemma dispositions for unresolved open-ended questions", () => {
    const plan = makePlan();
    plan.nodes["oeq:tight"].lean_kind = "theorem";
    const res = runPlanGate(plan, makeCore());
    expect(res.violations.some((v) => v.code === "P3" && v.where === "oeq:tight")).toBe(true);
  });
  it("rejects legacy proved open-ended questions as theorem dispositions (D0 must replace them)", () => {
    const core = makeCore();
    core.statements.find((s) => s.id === "oeq:tight")!.status = "proved";
    const plan = makePlan();
    plan.nodes["oeq:tight"].lean_kind = "lemma";
    expect(runPlanGate(plan, core).violations.some((v) => v.code === "P3" && v.where === "oeq:tight")).toBe(true);
  });
});

describe("F1 plan gate — P4 hyp closure", () => {
  it("flags a hyp not in depends_on", () => {
    const plan = makePlan();
    plan.nodes["thm:main"].hyps = ["ass:overlap", "def:overlap-class", "ass:phantom"];
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P4");
  });
  it("does not infer top-level hypothesis placement from assumption dependencies", () => {
    const plan = makePlan();
    // `consistency` and `ignorability` can occur under quantified implications in
    // the theorem conclusion. Their dependency edges alone do not imply that the
    // plan must expose them (or their class) as top-level Lean hypotheses.
    plan.nodes["thm:main"].hyps = ["ass:overlap"];
    expect(runPlanGate(plan, makeCore()).violations.filter((v) => v.code === "P4")).toEqual([]);
  });
});

describe("F1 plan gate — P5/P6/P7/P8 optional + derived", () => {
  it("flags a reuse decl absent from the library index (P5)", () => {
    const plan = makePlan();
    const res = runPlanGate(plan, makeCore(), { knownDecls: new Set(["SomethingElse"]) });
    expect(codes(res.violations)).toContain("P5");
  });
  it("passes P5 when the reuse decl is in the index", () => {
    const plan = makePlan();
    const res = runPlanGate(plan, makeCore(), { knownDecls: new Set(["Causalean.PO.System.POStructure"]) });
    expect(res.ok).toBe(true);
  });
  it("flags a malformed module path (P6)", () => {
    const plan = makePlan();
    plan.nodes["ass:overlap"].modules = ["not a module"];
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P6");
  });
  it("flags emitted-tag drift against the plan (P7)", () => {
    const plan = makePlan();
    const leanTags = { nodes: new Set(["thm:main"]), envs: new Set(["S1"]) }; // missing the other 5 nodes
    expect(codes(runPlanGate(plan, makeCore(), { leanTags }).violations)).toContain("P7");
  });
  it("passes P7 when every node is tagged", () => {
    const plan = makePlan();
    const leanTags = { nodes: new Set(Object.keys(plan.nodes)), envs: new Set(["S1"]) };
    expect(runPlanGate(plan, makeCore(), { leanTags }).ok).toBe(true);
  });
  it("accepts an exact completed pre-F2 auxiliary definition while leaving it unreviewed", () => {
    const plan = makePlan();
    const statement = "def helper : Nat := 1";
    let graph = createEmptyGraph("panel_demo", "v1");
    graph = addNode(graph, {
      id: "helper",
      kind: "definition",
      provenance: "agent-introduced",
      nl_statement: "helper",
      tex_anchor: "",
    });
    graph = setLean(graph, "helper", "Demo.helper", "Helpers.lean");
    graph = setProof(graph, "helper", "complete", 0);
    graph = setNodeReview(graph, "helper", "unreviewed", statementHash(statement));
    const annotatedDecls: ExtractedDecl[] = [{
      nodeId: "helper",
      declKind: "def",
      declName: "Demo.helper",
      namespace: "Demo",
      file: "Helpers.lean",
      statement,
      hasSorry: false,
    }];
    const leanTags = {
      nodes: new Set([...Object.keys(plan.nodes), "helper"]),
      envs: new Set(["S1"]),
    };
    const result = runPlanGate(plan, makeCore(), {
      leanTags,
      preF2Graph: graph,
      annotatedDecls,
      preF2AnnotatedDecls: annotatedDecls,
    });
    expect(result.violations).toEqual([]);
    expect(graph.nodes[0].review).toEqual({
      status: "unreviewed",
      passed_hash: statementHash(statement),
    });
  });
  it.each([
    ["missing pre-F2 declaration snapshot", (_graph: ReturnType<typeof createEmptyGraph>, _decls: ExtractedDecl[], preDecls: ExtractedDecl[]) => {
      preDecls.splice(0);
    }],
    ["changed statement", (_graph: ReturnType<typeof createEmptyGraph>, decls: ExtractedDecl[]) => {
      decls[0].statement = "lemma helper : False";
    }],
    ["rebound declaration", (_graph: ReturnType<typeof createEmptyGraph>, decls: ExtractedDecl[]) => {
      decls[0].declName = "Other.helper";
    }],
    ["incomplete proof", (graph: ReturnType<typeof createEmptyGraph>) => {
      graph.nodes[0].proof.state = "sorry";
    }],
    ["drift verdict", (graph: ReturnType<typeof createEmptyGraph>) => {
      graph.nodes[0].review.status = "drift";
    }],
  ])("refuses a plan-less helper with %s", (_label, mutate) => {
    const plan = makePlan();
    const statement = "lemma helper : True";
    let graph = createEmptyGraph("panel_demo", "v1");
    graph = addNode(graph, {
      id: "helper",
      kind: "lemma",
      provenance: "agent-introduced",
      nl_statement: "helper",
      tex_anchor: "",
    });
    graph = setLean(graph, "helper", "Demo.helper", "Helpers.lean");
    graph = setProof(graph, "helper", "complete", 0);
    graph = markPassed(graph, "helper", statementHash(statement));
    const annotatedDecls: ExtractedDecl[] = [{
      nodeId: "helper",
      declKind: "lemma",
      declName: "Demo.helper",
      namespace: "Demo",
      file: "Helpers.lean",
      statement,
      hasSorry: false,
    }];
    const preF2AnnotatedDecls = structuredClone(annotatedDecls);
    mutate(graph, annotatedDecls, preF2AnnotatedDecls);
    const leanTags = {
      nodes: new Set([...Object.keys(plan.nodes), "helper"]),
      envs: new Set(["S1"]),
    };
    expect(runPlanGate(plan, makeCore(), {
      leanTags,
      preF2Graph: graph,
      annotatedDecls,
      preF2AnnotatedDecls,
    }).violations).toContainEqual(expect.objectContaining({ code: "P7", where: "helper" }));
  });
  it("refuses a helper minted after the pre-F2 snapshot", () => {
    const plan = makePlan();
    const leanTags = {
      nodes: new Set([...Object.keys(plan.nodes), "new_helper"]),
      envs: new Set(["S1"]),
    };
    const annotatedDecls: ExtractedDecl[] = [{
      nodeId: "new_helper",
      declKind: "lemma",
      declName: "Demo.new_helper",
      namespace: "Demo",
      file: "Helpers.lean",
      statement: "lemma new_helper : True",
      hasSorry: false,
    }];
    expect(runPlanGate(plan, makeCore(), {
      leanTags,
      preF2Graph: createEmptyGraph("panel_demo", "v1"),
      annotatedDecls,
      preF2AnnotatedDecls: annotatedDecls,
    }).violations).toContainEqual(expect.objectContaining({ code: "P7", where: "new_helper" }));
  });
  it("flags stored feasibility disagreeing with the derived value (P8)", () => {
    const plan = makePlan();
    (plan.nodes["def:estimator"] as Record<string, unknown>).defer_tier = true; // derived ⇒ needs-new-infrastructure
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P8");
  });
});

// A minimal core+plan exercising a CITED node: `lem:borrowed-upper` is borrowed
// (D0 status:"cited", a leaf with its own source), consumed by `thm:main`.
function makeCitedCore(): Core {
  return {
    qid: "panel_cite",
    specialization: "v1",
    cluster: "stat",
    symbols: [{ name: "Y", type: "outcome" }],
    assumptions: [
      { id: "ass:reg", condition: "Y bounded", free_symbols: ["Y"], novel: { flag: true, justification: "regularity" } },
    ],
    definitions: [],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "rate holds", depends_on: ["ass:reg", "lem:borrowed-upper"], status: "proved" },
      { id: "lem:borrowed-upper", kind: "lemma", statement: "published upper bound", depends_on: [], status: "cited", source: { cite: "BK2022", locator: "Theorem 3" } },
    ],
    target_estimand: "theta",
    bibliography: [{ key: "BK2022", citation: "Bonvini, Kennedy (2022)" }],
  } as Core;
}

function makeCitedPlan() {
  return {
    qid: "panel_cite",
    specialization: "v1",
    cluster: "stat",
    lean_subdir: "Stat/Cite",
    env: [
      { id: "S1", world: "po-system", binds_symbols: ["Y"], binds_sampling_model: true, disposition: "reuse", reuse: "Causalean.PO.System.POStructure", modules: ["Causalean.PO.System"] },
    ],
    nodes: {
      "ass:reg": { lean_kind: "assumption", lean_name: "assReg", disposition: "define-local" },
      "lem:borrowed-upper": { lean_kind: "assumption", lean_name: "borrowedUpper", disposition: "define-local", gate: true, gate_class: "cited", source: "cite:bk2022" },
      "thm:main": { lean_kind: "theorem", lean_name: "main", target_file: "Basic.lean", hyps: ["ass:reg", "lem:borrowed-upper"], disposition: "define-local" },
    },
    citations: [{ id: "cite:bk2022", title: "Fast rates", authors: "Bonvini, Kennedy", year: 2022, arxiv: "2207.11825", locator: "Theorem 3" }],
    feasibility: "formalizable-now",
  };
}

describe("F1 plan gate — P9 cited mapping", () => {
  it("the F1 prompt separates borrowed cited inputs from paper-owned proof work", () => {
    const prompt = readFileSync(
      new URL("../../src/formalization/prompts/F1/stage1_template.txt", import.meta.url),
      "utf8",
    );
    expect(prompt).toMatch(/supported citation-discharge path/);
    expect(prompt).toMatch(/source-matched result outside this paper's contribution may remain cited even when a delivered headline invokes it/);
    expect(prompt).toMatch(/Every paper-owned\/new adaptation, embedding, normalization or experiment transfer, regime splice, and theorem step MUST be formalized/);
    expect(prompt).toMatch(/proof difficulty never makes it cited/);
    expect(prompt).toContain('source.carrier:"bibliographic-metadata"');
    expect(prompt).toContain('lean_kind:"def"');
    expect(prompt).toContain("NEVER threaded into `hyps`");
    expect(prompt).toContain("plan cannot relabel one as metadata");
    expect(prompt).not.toMatch(/status:"cited"[^\n]*encode the statement as a named Prop, and thread it into every consumer/);
    expect(prompt).not.toMatch(/Headline carve-out/);
  });

  it("a faithful cited mapping passes every check", () => {
    const res = runPlanGate(makeCitedPlan(), makeCitedCore());
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });

  it("rejects relabeling a frozen logical quantitative citation as unthreaded metadata", () => {
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      lean_kind: "def",
      lean_name: "borrowedScopeMetadata",
      gate: true,
      gate_class: "cited",
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    expect(runPlanGate(plan, makeCitedCore()).violations).toEqual(expect.arrayContaining([
      expect.objectContaining({ code: "P3", where: "lem:borrowed-upper" }),
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
      expect.objectContaining({ code: "P4", where: "thm:main" }),
    ]));
  });

  it("accepts frozen bibliographic metadata as a closed def without threading it", () => {
    const core = makeCitedCore();
    const cited = core.statements.find((statement) => statement.id === "lem:borrowed-upper")!;
    cited.statement = "The source is confined to a two-arm model and states no multi-arm theorem.";
    cited.source!.carrier = "bibliographic-metadata";
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      lean_kind: "def",
      lean_name: "borrowedScopeMetadata",
      gate: true,
      gate_class: "cited",
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    expect(runPlanGate(plan, core).violations).toEqual([]);
    expect(runPlanGate(plan, core, { annotatedDecls: [{
      nodeId: "lem:borrowed-upper",
      declKind: "def",
      declName: "borrowedScopeMetadata",
      namespace: "",
      file: "Basic.lean",
      statement: "def borrowedScopeMetadata : _root_.List _root_.String",
      sourceText: "def borrowedScopeMetadata : _root_.List _root_.String := [\"two arm\", \"bounded\"]",
      hasSorry: false,
    }] }).violations).toEqual([]);
    expect(runPlanGate(plan, core, { annotatedDecls: [{
      nodeId: "lem:borrowed-upper",
      declKind: "def",
      declName: "Demo.borrowedScopeMetadata",
      namespace: "Demo",
      file: "Basic.lean",
      statement: "def borrowedScopeMetadata : _root_.String",
      sourceText: "def borrowedScopeMetadata : _root_.String := \"two arm\"\n\nend Demo",
      hasSorry: false,
    }] }).violations).toEqual([]);
  });

  it("rejects discharging frozen bibliographic metadata into a theorem", () => {
    const core = makeCitedCore();
    core.statements.find((statement) => statement.id === "lem:borrowed-upper")!.source!.carrier = "bibliographic-metadata";
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      lean_kind: "theorem",
      gate: false,
      gate_class: undefined,
      citation_discharged: true,
      target_file: "Borrowed.lean",
      hyps: [],
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    expect(runPlanGate(plan, core).violations).toContainEqual(
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
    );
  });

  it("rejects threading frozen bibliographic metadata as a theorem hypothesis", () => {
    const core = makeCitedCore();
    core.statements.find((statement) => statement.id === "lem:borrowed-upper")!.source!.carrier = "bibliographic-metadata";
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], { lean_kind: "def" });
    expect(runPlanGate(plan, core).violations).toContainEqual(
      expect.objectContaining({ code: "P4", where: "thm:main", message: expect.stringContaining("cannot be a logical hyp") }),
    );
  });

  it("rejects an emitted theorem or Prop-valued def behind a metadata plan entry", () => {
    const core = makeCitedCore();
    core.statements.find((statement) => statement.id === "lem:borrowed-upper")!.source!.carrier = "bibliographic-metadata";
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], { lean_kind: "def", lean_name: "borrowedScopeMetadata" });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    const base = {
      nodeId: "lem:borrowed-upper", declName: "borrowedScopeMetadata", namespace: "",
      file: "Basic.lean", hasSorry: false,
    };
    for (const bad of [
      { ...base, declKind: "theorem", statement: "theorem borrowedScopeMetadata : True" },
      { ...base, declKind: "def", statement: "def borrowedScopeMetadata : Prop" },
      { ...base, declKind: "def", statement: "def borrowedScopeMetadata : (Prop)" },
      { ...base, declKind: "def", statement: "def borrowedScopeMetadata : Prop -- still logical" },
      { ...base, declKind: "def", statement: "def borrowedScopeMetadata : Sort 0" },
      { ...base, declKind: "def", statement: "def borrowedScopeMetadata : BibliographicCarrier" },
      { ...base, declKind: "def", statement: "def borrowedScopeMetadata : String" },
    ]) {
      expect(runPlanGate(plan, core, { annotatedDecls: [bad] }).violations).toContainEqual(
        expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
      );
    }
  });

  it("requires a fully-qualified plan name to match the emitted namespace", () => {
    const core = makeCitedCore();
    core.statements.find((statement) => statement.id === "lem:borrowed-upper")!.source!.carrier = "bibliographic-metadata";
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      lean_kind: "def", lean_name: "Expected.borrowedScopeMetadata",
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    expect(runPlanGate(plan, core, { annotatedDecls: [{
      nodeId: "lem:borrowed-upper", declKind: "def", declName: "Wrong.borrowedScopeMetadata",
      namespace: "Wrong", file: "Basic.lean", statement: "def borrowedScopeMetadata : _root_.List _root_.String", hasSorry: false,
    }] }).violations).toContainEqual(expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }));
  });

  it("rejects hyps on a non-theorem plan node", () => {
    const plan = makeCitedPlan();
    (plan.nodes["lem:borrowed-upper"] as typeof plan.nodes["lem:borrowed-upper"] & { hyps?: string[] }).hyps = ["ass:reg"];
    expect(runPlanGate(plan, makeCitedCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P4", where: "lem:borrowed-upper", message: expect.stringContaining("cannot carry hyps") }),
    );
  });

  it("rejects hyps on a core assumption promoted to a lemma", () => {
    const plan = makePlan();
    Object.assign(plan.nodes["ass:overlap"], {
      lean_kind: "lemma", target_file: "Basic.lean", hyps: ["ass:overlap"],
    });
    expect(runPlanGate(plan, makeCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P4", where: "ass:overlap", message: expect.stringContaining("only a core statement") }),
    );
  });

  it("rejects the proved shape without the gate.ts discharge stamp (F1 cannot self-discharge)", () => {
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      lean_kind: "theorem",
      lean_name: "borrowedUpperDischarge",
      gate: false,
      gate_class: undefined,
      target_file: "BorrowedUpperDischarge.lean",
      hyps: [],
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    expect(runPlanGate(plan, makeCitedCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
    );
  });

  it("accepts the supported discharged form as a proved non-gate theorem with retained provenance", () => {
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      lean_kind: "theorem",
      lean_name: "borrowedUpperDischarge",
      gate: false,
      gate_class: undefined,
      citation_discharged: true,
      target_file: "BorrowedUpperDischarge.lean",
      hyps: [],
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    const res = runPlanGate(plan, makeCitedCore());
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });

  it("rejects citation discharge through an unverified reuse shortcut", () => {
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      lean_kind: "theorem", gate: false, gate_class: undefined,
      citation_discharged: true, disposition: "reuse", reuse: "Does.Not.Exist", hyps: [],
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    expect(runPlanGate(plan, makeCitedCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
    );
  });

  it("requires the discharged cited node to match one sorry-free emitted declaration at F2", () => {
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      lean_kind: "theorem",
      lean_name: "borrowedUpperDischarge",
      gate: false,
      gate_class: undefined,
      citation_discharged: true,
      target_file: "BorrowedUpperDischarge.lean",
      hyps: [],
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    const badDecl: ExtractedDecl = {
      nodeId: "lem:borrowed-upper",
      declKind: "theorem",
      declName: "Demo.borrowedUpperDischarge",
      namespace: "Demo",
      file: "BorrowedUpperDischarge.lean",
      statement: "theorem borrowedUpperDischarge : True := by sorry",
      hasSorry: true,
    };
    expect(runPlanGate(plan, makeCitedCore(), { annotatedDecls: [badDecl] }).violations).toContainEqual(
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
    );
    expect(runPlanGate(plan, makeCitedCore(), {
      annotatedDecls: [{ ...badDecl, hasSorry: false }],
    }).violations).toEqual([]);
  });

  it("rejects clearing a cited gate without mapping it to a proved lemma/theorem", () => {
    const plan = makeCitedPlan();
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      gate: false,
      gate_class: undefined,
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    expect(runPlanGate(plan, makeCitedCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
    );
  });

  it("flags re-laundering a cited statement as a non-cited gate", () => {
    const plan = makeCitedPlan();
    (plan.nodes["lem:borrowed-upper"] as Record<string, unknown>).gate_class = "gated";
    expect(codes(runPlanGate(plan, makeCitedCore()).violations)).toContain("P9");
  });

  it("flags a cited node whose source does not resolve", () => {
    const plan = makeCitedPlan();
    (plan.nodes["lem:borrowed-upper"] as Record<string, unknown>).source = "cite:nonexistent";
    expect(codes(runPlanGate(plan, makeCitedCore()).violations)).toContain("P9");
  });

  it("flags F1 inventing a citation for a non-cited statement", () => {
    const plan = makeCitedPlan();
    (plan.nodes["thm:main"] as Record<string, unknown>).gate_class = "cited";
    expect(codes(runPlanGate(plan, makeCitedCore()).violations)).toContain("P9");
  });
});

describe("F1 plan gate — P10 undelivered guard", () => {
  it("rejects a planner-authored undelivered secondary theorem before downstream role review", () => {
    const core = makeCore();
    core.statements.find((s) => s.id === "oeq:tight")!.depends_on = [];
    const plan = makePlan();
    Object.assign(plan.nodes["thm:main"], {
      delivery_role: "secondary",
      delivery_status: "undelivered",
      delivery_reason: "citation instantiation would require a substantial non-headline substrate",
    });
    const leanTags = {
      nodes: new Set(Object.keys(plan.nodes).filter((id) => id !== "thm:main")),
      envs: new Set(["S1"]),
    };
    expect(runPlanGate(plan, core, { leanTags }).violations).toContainEqual(
      expect.objectContaining({ code: "P10", where: "thm:main" }),
    );
  });

  it("rejects undelivered headline/support roles and delivered consumers", () => {
    const plan = makePlan();
    Object.assign(plan.nodes["thm:main"], {
      delivery_role: "headline",
      delivery_status: "undelivered",
      delivery_reason: "too hard",
    });
    const res = runPlanGate(plan, makeCore());
    expect(res.violations.some((v) => v.code === "P10" && v.where === "thm:main")).toBe(true);
    expect(res.violations.some((v) => v.code === "P10" && v.where === "oeq:tight")).toBe(true);
  });
});
