import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, setLean, setNodeReview } from "../../src/graph/mutate.js";
import { GraphSchema, type ConvergenceLedger, type FormalizationGraph } from "../../src/graph/types.js";
import type { Core } from "../../src/discovery/core/schema.js";
import {
  auditConvergenceReview,
  buildLeanEvidenceIndex,
  buildSymbolReviewRows,
  dualClearedAt,
  ledgerNodeTargets,
  nodeConvergenceEvidence,
  reviewerRubricHash,
  symbolConvergenceEvidence,
} from "../../src/formalization/convergence_evidence.js";

const LEAN = [
  "import Mathlib.Data.Real.Basic",
  "",
  "-- an untagged helper: no @node, not a graph node, reached only by name",
  "def helperBound (n : ℕ) : ℝ := n + 1",
  "",
  "/-- @realizes K -/",
  "def kArms : ℕ := 2",
  "",
  "-- @node: def:class",
  "structure ModelClass where",
  "  /-- the bound -/",
  "  bound : ℝ",
  "  bound_pos : 0 < bound",
  "",
  "-- @node: thm:main",
  "theorem mainThm (M : ModelClass) (n : ℕ) : M.bound ≤ helperBound n + 1 := by",
  "  sorry",
  "",
  "-- @node: lem:side",
  "lemma sideLemma : True := by trivial",
].join("\n");

function fixtureGraph(): FormalizationGraph {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "thm:main", kind: "theorem", provenance: "from-note", nl_statement: "the main bound", tex_anchor: "" });
  g = addNode(g, { id: "def:class", kind: "definition", provenance: "from-note", nl_statement: "the model class", tex_anchor: "" });
  g = addNode(g, { id: "lem:side", kind: "lemma", provenance: "from-note", nl_statement: "a side fact", tex_anchor: "" });
  g = setLean(g, "thm:main", "mainThm", "Main.lean");
  g = setLean(g, "def:class", "ModelClass", "Main.lean");
  g = setLean(g, "lem:side", "sideLemma", "Main.lean");
  g = addEdge(g, { kind: "statement-uses", from: "thm:main", to: "def:class", source: "extracted" });
  for (const id of ["thm:main", "def:class", "lem:side"]) g = setNodeReview(g, id, "matched", "h");
  return g;
}

const core = {
  qid: "q",
  specialization: "v1",
  symbols: [{ name: "K", space: "\\{2,3,\\dots\\}", role: "core" }],
  assumptions: [],
  definitions: [],
  statements: [{ id: "thm:main", kind: "theorem", statement: "the main bound", depends_on: [], status: "proved", proof_tex: "p" }],
  target_estimand: "x",
  bibliography: [],
} as unknown as Core;

const receipt = (h: string) => ({ codex: { verdict: "matched" as const, evidence_hash: h }, claude: { verdict: "matched" as const, evidence_hash: h } });

let dir = "";
let rubric = "";

beforeEach(async () => {
  rubric = await reviewerRubricHash("rubric v1");
  dir = await mkdtemp(join(tmpdir(), "conv-evidence-"));
  await writeFile(join(dir, "Main.lean"), LEAN);
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

async function evidenceOf(nodeId: string, graph = fixtureGraph(), rubricHash = rubric): Promise<string> {
  const index = await buildLeanEvidenceIndex(dir);
  return nodeConvergenceEvidence({ graph, index, core, rubricHash, nodeId });
}

describe("node convergence evidence", () => {
  it("is stable across a re-parse of an unchanged tree", async () => {
    expect(await evidenceOf("thm:main")).toBe(await evidenceOf("thm:main"));
  });

  it("ignores a theorem's PROOF but not its statement", async () => {
    const before = await evidenceOf("thm:main");
    await writeFile(join(dir, "Main.lean"), LEAN.replace("theorem mainThm (M : ModelClass) (n : ℕ) : M.bound ≤ helperBound n + 1 := by\n  sorry", "theorem mainThm (M : ModelClass) (n : ℕ) : M.bound ≤ helperBound n + 1 := by\n  simp"));
    expect(await evidenceOf("thm:main")).toBe(before);
    await writeFile(join(dir, "Main.lean"), LEAN.replace("M.bound ≤ helperBound n + 1", "M.bound ≤ helperBound n + 2"));
    expect(await evidenceOf("thm:main")).not.toBe(before);
  });

  it("changes when an UNTAGGED helper the statement references changes body (transitive, not graph-edge-bound)", async () => {
    const before = await evidenceOf("thm:main");
    await writeFile(join(dir, "Main.lean"), LEAN.replace("def helperBound (n : ℕ) : ℝ := n + 1", "def helperBound (n : ℕ) : ℝ := n + 100"));
    expect(await evidenceOf("thm:main")).not.toBe(before);
  });

  it("changes when a referenced structure's field changes, and leaves an unrelated lemma alone", async () => {
    const t = await evidenceOf("thm:main");
    const l = await evidenceOf("lem:side");
    await writeFile(join(dir, "Main.lean"), LEAN.replace("  bound_pos : 0 < bound", "  bound_pos : 1 < bound"));
    expect(await evidenceOf("thm:main")).not.toBe(t);
    expect(await evidenceOf("lem:side")).toBe(l);
  });

  it("is unchanged by docstrings and comments (F5 may document without invalidating F4)", async () => {
    const before = await evidenceOf("thm:main");
    const documented = LEAN
      .replace("-- @node: thm:main\n", "-- @node: thm:main\n/-- The [main bound](goal) holds. -/\n")
      .replace("def helperBound", "/-- helper doc -/\ndef helperBound");
    await writeFile(join(dir, "Main.lean"), documented);
    expect(await evidenceOf("thm:main")).toBe(before);
  });

  it("changes when a top-level `variable` command in the file changes", async () => {
    const before = await evidenceOf("thm:main");
    await writeFile(join(dir, "Main.lean"), LEAN.replace("import Mathlib.Data.Real.Basic", "import Mathlib.Data.Real.Basic\nvariable (hn : 0 < 1)"));
    expect(await evidenceOf("thm:main")).not.toBe(before);
  });

  it("follows section `variable` binders, `notation` right-hand sides, and anonymous instances", async () => {
    const SECTIONED = [
      "structure Cls where",
      "  bound : Nat",
      "  bound_pos : 0 < bound",
      "def ateNaive : Nat := 1",
      "notation \"ATE\" => ateNaive",
      "variable (M : Cls)",
      "-- @node: thm:main",
      "theorem mainThm : M.bound ≤ ATE := by sorry",
    ].join("\n");
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "thm:main", kind: "theorem", provenance: "from-note", nl_statement: "bound", tex_anchor: "" });
    g = setLean(g, "thm:main", "mainThm", "Main.lean");
    await writeFile(join(dir, "Main.lean"), SECTIONED);
    const before = await evidenceOf("thm:main", g);
    await writeFile(join(dir, "Main.lean"), SECTIONED.replace("bound_pos : 0 < bound", "bound_pos : 5 < bound"));
    expect(await evidenceOf("thm:main", g)).not.toBe(before); // through the `variable` binder's type
    await writeFile(join(dir, "Main.lean"), SECTIONED.replace("def ateNaive : Nat := 1", "def ateNaive : Nat := 7"));
    expect(await evidenceOf("thm:main", g)).not.toBe(before); // through the notation's RHS
    await writeFile(join(dir, "Main.lean"), SECTIONED);
    await writeFile(join(dir, "Other.lean"), "-- @node: lem:x\ntheorem lemX : True := trivial\ninstance : Inhabited Nat := ⟨0⟩\n");
    const withInst = await evidenceOf("thm:main", g);
    expect(withInst).not.toBe(before); // an anonymous instance in ANOTHER file is global evidence
    await writeFile(join(dir, "Other.lean"), "-- @node: lem:x\ntheorem lemX : True := trivial\ninstance : Inhabited Nat := ⟨1⟩\n");
    expect(await evidenceOf("thm:main", g)).not.toBe(withInst);
    // A file with NO named declaration (notation/instances only) is still global evidence.
    await writeFile(join(dir, "Notation.lean"), "notation \"BND\" => 42\n");
    const withNotationFile = await evidenceOf("thm:main", g);
    expect(withNotationFile).not.toBe(withInst);
    await writeFile(join(dir, "Notation.lean"), "notation \"BND\" => 43\n");
    expect(await evidenceOf("thm:main", g)).not.toBe(withNotationFile);
  });

  it("changes with the rubric, the NL statement, and a gated substrate hypothesis", async () => {
    const before = await evidenceOf("thm:main");
    expect(await evidenceOf("thm:main", fixtureGraph(), await reviewerRubricHash("rubric v2"))).not.toBe(before);
    let g = fixtureGraph();
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "thm:main" ? { ...n, nl: { ...n.nl, statement: "a weaker bound" } } : n)) };
    expect(await evidenceOf("thm:main", g)).not.toBe(before);
    let gg = fixtureGraph();
    gg = addNode(gg, { id: "gate:x", kind: "gate", provenance: "from-note", nl_statement: "assumed substrate", tex_anchor: "" });
    gg = { ...gg, nodes: gg.nodes.map((n) => (n.id === "gate:x" ? { ...n, gate: { gate_class: "gated" as const } } : n)) };
    gg = addEdge(gg, { kind: "proof-uses", from: "thm:main", to: "gate:x", source: "declared" });
    expect(await evidenceOf("thm:main", gg)).not.toBe(before);
  });
});

describe("symbol convergence evidence", () => {
  it("binds a symbol cluster to its members' bodies", async () => {
    const index = await buildLeanEvidenceIndex(dir);
    const rows = await buildSymbolReviewRows(dir, core.symbols);
    expect(rows.map((r) => [r.id, r.empty])).toEqual([["sym:K", false]]);
    const before = symbolConvergenceEvidence({ index, rubricHash: rubric, row: rows[0] });
    await writeFile(join(dir, "Main.lean"), LEAN.replace("def kArms : ℕ := 2", "def kArms : ℕ := 0"));
    const index2 = await buildLeanEvidenceIndex(dir);
    const rows2 = await buildSymbolReviewRows(dir, core.symbols);
    expect(rows2[0].hash).toBe(rows[0].hash); // the prompt row is name-level: the delta key alone would NOT notice
    expect(symbolConvergenceEvidence({ index: index2, rubricHash: rubric, row: rows2[0] })).not.toBe(before);
  });

  it("ignores documentation-only hint and line motion but binds variable carrier code", async () => {
    const variable = [
      "variable -- @realizes K(first wording)",
      "  (k : Fin 3)",
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), variable);
    const before = (await buildSymbolReviewRows(dir, core.symbols))[0];
    const beforeEvidence = symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric, row: before,
    });
    await writeFile(join(dir, "Main.lean"), [
      "/-- unrelated documentation shifts the carrier line -/",
      "variable -- @realizes K(reworded hint)",
      "  (k : Fin 3)",
    ].join("\n"));
    const documented = (await buildSymbolReviewRows(dir, core.symbols))[0];
    expect(documented.row).not.toBe(before.row);
    expect(documented.hash).toBe(before.hash);
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric, row: documented,
    })).toBe(beforeEvidence);
    await writeFile(join(dir, "Main.lean"), variable.replace("Fin 3", "Fin 4"));
    const changed = (await buildSymbolReviewRows(dir, core.symbols))[0];
    expect(changed.hash).not.toBe(before.hash);
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric, row: changed,
    })).not.toBe(beforeEvidence);

    const stringCarrier = [
      "variable -- @realizes K(string-refined carrier)",
      '  (s : { x : String // x = "foo" })',
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), stringCarrier);
    const foo = (await buildSymbolReviewRows(dir, core.symbols))[0];
    await writeFile(join(dir, "Main.lean"), stringCarrier.replace('"foo"', '"bar"'));
    const bar = (await buildSymbolReviewRows(dir, core.symbols))[0];
    expect(bar.hash).not.toBe(foo.hash);
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric, row: bar,
    })).not.toBe(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric, row: foo,
    }));
    await writeFile(join(dir, "Main.lean"), stringCarrier.replace('"foo"', '"a  b"'));
    const spaced = (await buildSymbolReviewRows(dir, core.symbols))[0];
    await writeFile(join(dir, "Main.lean"), stringCarrier.replace('"foo"', '"a b"'));
    expect((await buildSymbolReviewRows(dir, core.symbols))[0].hash).not.toBe(spaced.hash);

    const arrayCarrier = [
      "variable -- @realizes K(array-refined carrier)",
      "  (h :",
      "    #[1, 2][0] = 1)",
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), arrayCarrier);
    const trueCarrier = (await buildSymbolReviewRows(dir, core.symbols))[0];
    await writeFile(join(dir, "Main.lean"), arrayCarrier.replace("#[1, 2]", "#[0, 2]"));
    expect((await buildSymbolReviewRows(dir, core.symbols))[0].hash).not.toBe(trueCarrier.hash);

    const escapedCarrier = [
      "variable -- @realizes K(escaped-id carrier)",
      "  (k : «T)foo»)",
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), escapedCarrier);
    const fooCarrier = (await buildSymbolReviewRows(dir, core.symbols))[0];
    await writeFile(join(dir, "Main.lean"), escapedCarrier.replace("«T)foo»", "«T)bar»"));
    expect((await buildSymbolReviewRows(dir, core.symbols))[0].hash).not.toBe(fooCarrier.hash);
    await writeFile(join(dir, "Main.lean"), escapedCarrier.replace("«T)foo»", "«T  foo»"));
    const doubleSpaceIdent = (await buildSymbolReviewRows(dir, core.symbols))[0];
    await writeFile(join(dir, "Main.lean"), escapedCarrier.replace("«T)foo»", "«T foo»"));
    expect((await buildSymbolReviewRows(dir, core.symbols))[0].hash).not.toBe(doubleSpaceIdent.hash);

    const aliasedCarrier = [
      "def Carrier := Fin 3",
      "variable (k : Carrier) -- @realizes K(alias carrier)",
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), aliasedCarrier);
    const alias3 = (await buildSymbolReviewRows(dir, core.symbols))[0];
    const aliasEvidence3 = symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric, row: alias3,
    });
    await writeFile(join(dir, "Main.lean"), aliasedCarrier.replace("Fin 3", "Fin 4"));
    const alias4 = (await buildSymbolReviewRows(dir, core.symbols))[0];
    expect(alias4.hash).toBe(alias3.hash);
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric, row: alias4,
    })).not.toBe(aliasEvidence3);

    const macroCarrier = [
      'syntax "MyCarrier" : term',
      "macro_rules",
      "  | `(MyCarrier) => `(Fin 3)",
      "variable (k : MyCarrier) -- @realizes K(macro carrier)",
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), macroCarrier);
    const macro3 = (await buildSymbolReviewRows(dir, core.symbols))[0];
    const macroEvidence3 = symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric, row: macro3,
    });
    await writeFile(join(dir, "Main.lean"), macroCarrier.replace("Fin 3", "Fin 4"));
    const macro4 = (await buildSymbolReviewRows(dir, core.symbols))[0];
    expect(macro4.hash).toBe(macro3.hash);
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric, row: macro4,
    })).not.toBe(macroEvidence3);

    const multilineString = [
      'def tag : String := "a  ',
      'b"',
      "def Carrier := { s : String // s = tag }",
      "variable (s : Carrier) -- @realizes K(string alias carrier)",
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), multilineString);
    const stringEvidence = symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    });
    await writeFile(join(dir, "Main.lean"), multilineString.replace("a  \n", "a\n"));
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    })).not.toBe(stringEvidence);

    const rawString = [
      "variable (s : String) -- @realizes K(raw-string carrier)",
      'def tag := r#"a"',
      "x  ",
      'y"#',
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), rawString);
    const rawEvidence = symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    });
    await writeFile(join(dir, "Main.lean"), rawString.replace("x  \n", "x\n"));
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    })).not.toBe(rawEvidence);

    const interpolated = [
      "variable (s : String) -- @realizes K(interpolated-string carrier)",
      'def tag := s!"a {("q  ',
      'r")} z"',
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), interpolated);
    const interpEvidence = symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    });
    await writeFile(join(dir, "Main.lean"), interpolated.replace("q  \n", "q\n"));
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    })).not.toBe(interpEvidence);

    const adjacentR = [
      "variable (s : String) -- @realizes K(adjacent-r string carrier)",
      'syntax "😀r" str : term',
      'macro_rules | `(😀r $s:str) => `($s)',
      'def tag : String := 😀r"a\\"x',
      "q  ",
      'r"',
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), adjacentR);
    const adjacentEvidence = symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    });
    await writeFile(join(dir, "Main.lean"), adjacentR.replace("q  \n", "q\n"));
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    })).not.toBe(adjacentEvidence);

    const positionSensitive = [
      "-- source-position-aware elaborator fixture",
      "def inspectPos := stx.getPos?",
      "variable (k : Fin 3) -- @realizes K(position-sensitive carrier)",
    ].join("\n");
    await writeFile(join(dir, "Main.lean"), positionSensitive);
    const positionEvidence = symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    });
    await writeFile(join(dir, "Main.lean"), `--xx\n${positionSensitive}`);
    expect(symbolConvergenceEvidence({
      index: await buildLeanEvidenceIndex(dir), rubricHash: rubric,
      row: (await buildSymbolReviewRows(dir, core.symbols))[0],
    })).not.toBe(positionEvidence);
  });
});

describe("dualClearedAt / ledgerNodeTargets", () => {
  it("requires BOTH peers matched at the exact evidence", () => {
    const ledger: ConvergenceLedger = {
      t: { codex: { verdict: "matched", evidence_hash: "e" }, claude: { verdict: "matched", evidence_hash: "e" } },
      one: { codex: { verdict: "matched", evidence_hash: "e" } },
      drift: { codex: { verdict: "matched", evidence_hash: "e" }, claude: { verdict: "drift", evidence_hash: "e" } },
      stale: { codex: { verdict: "matched", evidence_hash: "e" }, claude: { verdict: "matched", evidence_hash: "old" } },
    };
    expect(dualClearedAt(ledger, "t", "e")).toBe(true);
    expect(dualClearedAt(ledger, "t", "e2")).toBe(false);
    expect(dualClearedAt(ledger, "one", "e")).toBe(false);
    expect(dualClearedAt(ledger, "drift", "e")).toBe(false);
    expect(dualClearedAt(ledger, "stale", "e")).toBe(false);
    expect(dualClearedAt(undefined, "t", "e")).toBe(false);
  });

  it("governs statements/definitions/lemmas/assumptions but not cited gates or undelivered nodes", () => {
    let g = fixtureGraph();
    g = addNode(g, { id: "gate:c", kind: "gate", provenance: "from-note", nl_statement: "cited", tex_anchor: "" });
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "gate:c" ? { ...n, gate: { gate_class: "cited" as const, source: "cite:x" } } : n)) };
    g = addNode(g, { id: "thm:omit", kind: "theorem", provenance: "from-note", nl_statement: "omitted", tex_anchor: "" });
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "thm:omit" ? { ...n, delivery: { status: "undelivered" as const, role: "secondary" as const, reason: "r" } } : n)) };
    expect(ledgerNodeTargets(GraphSchema.parse(g)).sort()).toEqual(["def:class", "lem:side", "thm:main"]);
  });

  it("round-trips through the graph schema", () => {
    const g = { ...fixtureGraph(), convergenceReview: { "thm:main": receipt("e") } };
    expect(GraphSchema.parse(g).convergenceReview).toEqual({ "thm:main": receipt("e") });
    expect(() => GraphSchema.parse({ ...g, convergenceReview: { x: { codex: { verdict: "maybe", evidence_hash: "e" } } } })).toThrow();
  });
});

describe("auditConvergenceReview", () => {
  it("passes when every governed target is dual-receipted at current evidence, and names each gap otherwise", async () => {
    const promptFile = join(dir, "prompt.txt");
    await writeFile(promptFile, "rubric v1");
    const g = fixtureGraph();
    const index = await buildLeanEvidenceIndex(dir);
    const ev = (id: string) => nodeConvergenceEvidence({ graph: g, index, core, rubricHash: rubric, nodeId: id });
    const rows = await buildSymbolReviewRows(dir, core.symbols);
    const symEv = symbolConvergenceEvidence({ index, rubricHash: rubric, row: rows[0] });
    const ledger: ConvergenceLedger = {
      "thm:main": receipt(ev("thm:main")),
      "def:class": receipt(ev("def:class")),
      "lem:side": receipt(ev("lem:side")),
      "sym:K": receipt(symEv),
    };
    const good = { ...g, symbolReview: { "sym:K": { verdict: "matched", hash: rows[0].hash } }, convergenceReview: ledger };
    expect(await auditConvergenceReview({ graph: good, leanDir: dir, core, promptFile })).toEqual([]);

    // Tree edited after F4: the theorem's receipt is stale, the others still hold.
    await writeFile(join(dir, "Main.lean"), LEAN.replace("M.bound ≤ helperBound n + 1", "M.bound ≤ helperBound n + 2"));
    const stale = await auditConvergenceReview({ graph: good, leanDir: dir, core, promptFile });
    expect(stale.map((f) => f.node_id)).toEqual(["thm:main"]);
    expect(stale[0].message).toMatch(/stale/);
    await writeFile(join(dir, "Main.lean"), LEAN);

    // Rubric edited after F4: everything is stale.
    await writeFile(promptFile, "rubric v2");
    expect((await auditConvergenceReview({ graph: good, leanDir: dir, core, promptFile })).map((f) => f.node_id).sort())
      .toEqual(["def:class", "lem:side", "sym:K", "thm:main"]);
    await writeFile(promptFile, "rubric v1");

    // One peer missing / a delta-only clearance / a symbol not delta-passed.
    const half = { ...good, convergenceReview: { ...ledger, "lem:side": { codex: ledger["lem:side"].codex } } };
    expect((await auditConvergenceReview({ graph: half, leanDir: dir, core, promptFile })).map((f) => f.node_id)).toEqual(["lem:side"]);
    const noLedger = { ...good, convergenceReview: undefined };
    expect((await auditConvergenceReview({ graph: noLedger, leanDir: dir, core, promptFile })).map((f) => f.node_id).sort())
      .toEqual(["def:class", "lem:side", "sym:K", "thm:main"]);
    const symDrift = { ...good, symbolReview: { "sym:K": { verdict: "drift", hash: rows[0].hash } } };
    expect((await auditConvergenceReview({ graph: symDrift, leanDir: dir, core, promptFile })).map((f) => f.node_id)).toEqual(["sym:K"]);
    const nodeDrift = { ...good, nodes: good.nodes.map((n) => (n.id === "def:class" ? { ...n, review: { ...n.review, status: "drift" as const } } : n)) };
    expect((await auditConvergenceReview({ graph: nodeDrift, leanDir: dir, core, promptFile })).map((f) => f.node_id)).toEqual(["def:class"]);
  });
});
