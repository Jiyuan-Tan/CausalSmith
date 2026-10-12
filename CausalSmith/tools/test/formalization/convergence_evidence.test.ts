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
  buildSymbolReviewRows,
  dualClearedAt,
  dualMatchedReceipts,
  ledgerNodeTargets,
  loadPartialReceipts,
  partialReceiptsPath,
  nodeConvergenceEvidence,
  receiptsAt,
  REVIEW_STANDARD,
  symbolConvergenceEvidence,
} from "../../src/formalization/convergence_evidence.js";
import { buildLeanEvidenceIndex, legacyNodeEvidence } from "../../src/formalization/convergence_evidence_legacy.js";
import { closureHash, statementFingerprints, type StatementFingerprints } from "../../src/formalization/statement_fingerprints.js";
import { readScan } from "../../src/substrate/invariance.js";

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

/** A scan row: name, statement fingerprint, what the statement reads by name, module. */
type Row = [string, string, string[]?, string?];
const BASIS = { toolchain: "leanprover/lean4:v4.0", mathlib: "abc" };
function fingerprintsOf(rows: Row[], basis = BASIS): StatementFingerprints {
  const text = rows.map(([name, stmt_hash, deps = [], module = "Run.Main"]) => JSON.stringify({ name, kind: "def", stmt_hash, module, deps })).join("\n");
  return statementFingerprints(readScan(text, new Set(["Run.Main"])), "Run", basis);
}
/** The fixture's scan: the theorem reaches the untagged helper and, through it, a Causalean
 *  declaration; the structure and the side lemma reach nothing of the package. */
const ROWS: Row[] = [
  ["helperBound", "h1", ["Causalean.Stat.weight"]],
  ["kArms", "k1"],
  ["ModelClass", "m1"],
  ["mainThm", "t1", ["ModelClass", "helperBound"]],
  ["sideLemma", "s1"],
  ["Causalean.Stat.weight", "w1", [], "Causalean.Stat.Weighted"],
];
const FP = () => fingerprintsOf(ROWS);
const withHash = (rows: Row[], name: string, hash: string): Row[] => rows.map((r) => (r[0] === name ? [name, hash, r[2], r[3]] : r));

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
const rubric = REVIEW_STANDARD;

beforeEach(async () => {
  dir = await mkdtemp(join(tmpdir(), "conv-evidence-"));
  await writeFile(join(dir, "Main.lean"), LEAN);
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

const evidenceOf = (nodeId: string, fingerprints: StatementFingerprints | null = FP(), graph = fixtureGraph(), rubricHash = rubric): string | null =>
  nodeConvergenceEvidence({ graph, fingerprints, core, rubricHash, nodeId });

describe("node convergence evidence", () => {
  it("is keyed on what Lean elaborated: a changed statement re-opens exactly the targets whose closure reaches it", () => {
    const t = evidenceOf("thm:main");
    const d = evidenceOf("def:class");
    const l = evidenceOf("lem:side");
    expect(evidenceOf("thm:main")).toBe(t);
    // the untagged helper (not a graph node) changes: the theorem that reads it is re-opened
    const helper = fingerprintsOf(withHash(ROWS, "helperBound", "h2"));
    expect(evidenceOf("thm:main", helper)).not.toBe(t);
    expect(evidenceOf("def:class", helper)).toBe(d);
    expect(evidenceOf("lem:side", helper)).toBe(l);
    // a Causalean declaration the helper's statement reads changes: transitively the same
    expect(evidenceOf("thm:main", fingerprintsOf(withHash(ROWS, "Causalean.Stat.weight", "w2")))).not.toBe(t);
    // the structure's statement changes: its own target and the theorem that uses it
    const cls = fingerprintsOf(withHash(ROWS, "ModelClass", "m2"));
    expect(evidenceOf("def:class", cls)).not.toBe(d);
    expect(evidenceOf("thm:main", cls)).not.toBe(t);
    expect(evidenceOf("lem:side", cls)).toBe(l);
    // a declaration nothing reaches, added or changed, re-opens nothing
    expect(evidenceOf("thm:main", fingerprintsOf([...ROWS, ["extraLemma", "x1"]]))).toBe(t);
  });

  it("the closure hash moves with a member or an edge, under the member's name", () => {
    const fp = FP();
    expect(closureHash(fp, "mainThm")).toBe(closureHash(FP(), "mainThm"));
    expect(closureHash(fingerprintsOf(withHash(ROWS, "Causalean.Stat.weight", "w2")), "mainThm")).not.toBe(closureHash(fp, "mainThm"));
    expect(closureHash(fingerprintsOf(ROWS.map((r) => (r[0] === "mainThm" ? ["mainThm", "t1", ["ModelClass"]] : r))), "mainThm")).not.toBe(closureHash(fp, "mainThm"));
    expect(closureHash(fp, "sideLemma")).toBe(closureHash(fingerprintsOf(withHash(ROWS, "helperBound", "h2")), "sideLemma"));
  });

  it("a target with no fingerprint has no evidence, which clears nothing", () => {
    expect(evidenceOf("thm:main", null)).toBeNull();
    expect(evidenceOf("thm:main", fingerprintsOf(ROWS.filter((r) => r[0] !== "mainThm")))).toBeNull();
    // the anchor names a declaration of another file, or a same-named one of another namespace
    let g = fixtureGraph();
    g = setLean(g, "thm:main", "mainThm", "Other.lean");
    expect(evidenceOf("thm:main", FP(), g)).toBeNull();
    g = setLean(g, "thm:main", "Paper.mainThm", "Main.lean");
    expect(evidenceOf("thm:main", fingerprintsOf(withHash(ROWS, "mainThm", "t1").map((r) => (r[0] === "mainThm" ? ["Paper.mainThm", "t1", r[2]] : r))), g)).not.toBeNull();
    expect(evidenceOf("thm:main", FP(), g)).not.toBeNull(); // a namespace-qualified anchor finds the declared name
    expect(dualClearedAt({ "thm:main": receipt("e") }, "thm:main", null)).toBe(false);
    expect(receiptsAt({ "thm:main": receipt("e") }, "thm:main", null, ["e"])).toBeUndefined();
  });

  it("the review standard is a hand-bumped token, not a hash of the prompt or the reviewer source", () => {
    // Frozen at the value reviewerRubricHash returned on 2026-09-12 for the shipped
    // proof_reviewer.txt, so receipts written before the change stay valid. An accidental edit
    // here invalidates every convergence receipt in every run.
    expect(REVIEW_STANDARD).toBe("16865e36da9271bbf0e9906def5868e43c1ec0d8");
  });

  it("changes with the rubric, the NL statement, the build basis, and a gated substrate hypothesis", () => {
    const before = evidenceOf("thm:main");
    expect(evidenceOf("thm:main", FP(), fixtureGraph(), "review-standard-bumped")).not.toBe(before);
    let g = fixtureGraph();
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "thm:main" ? { ...n, nl: { ...n.nl, statement: "a weaker bound" } } : n)) };
    expect(evidenceOf("thm:main", FP(), g)).not.toBe(before);
    expect(evidenceOf("thm:main", fingerprintsOf(ROWS, { ...BASIS, mathlib: "def" }))).not.toBe(before);
    let gg = fixtureGraph();
    gg = addNode(gg, { id: "gate:x", kind: "gate", provenance: "from-note", nl_statement: "assumed substrate", tex_anchor: "" });
    gg = { ...gg, nodes: gg.nodes.map((n) => (n.id === "gate:x" ? { ...n, gate: { gate_class: "gated" as const } } : n)) };
    gg = addEdge(gg, { kind: "proof-uses", from: "thm:main", to: "gate:x", source: "declared" });
    expect(evidenceOf("thm:main", FP(), gg)).not.toBe(before);
  });
});

describe("symbol convergence evidence", () => {
  it("binds a symbol cluster to what its members elaborate to; a `variable` carrier to its file's declarations", async () => {
    const rows = await buildSymbolReviewRows(dir, core.symbols);
    expect(rows.map((r) => [r.id, r.empty])).toEqual([["sym:K", false]]);
    const before = symbolConvergenceEvidence({ fingerprints: FP(), rubricHash: rubric, row: rows[0] });
    expect(before).not.toBeNull();
    expect(symbolConvergenceEvidence({ fingerprints: fingerprintsOf(withHash(ROWS, "kArms", "k2")), rubricHash: rubric, row: rows[0] })).not.toBe(before);
    expect(symbolConvergenceEvidence({ fingerprints: fingerprintsOf(withHash(ROWS, "sideLemma", "s2")), rubricHash: rubric, row: rows[0] })).toBe(before);
    expect(symbolConvergenceEvidence({ fingerprints: fingerprintsOf(ROWS.filter((r) => r[0] !== "kArms")), rubricHash: rubric, row: rows[0] })).toBeNull();
    expect(symbolConvergenceEvidence({ fingerprints: null, rubricHash: rubric, row: rows[0] })).toBeNull();

    await writeFile(join(dir, "Main.lean"), "variable -- @realizes K\n  (k : Fin 3)\ntheorem usesK (k : Fin 3) : True := trivial\n");
    const carrier = (await buildSymbolReviewRows(dir, core.symbols))[0];
    const viaFile = symbolConvergenceEvidence({ fingerprints: fingerprintsOf([["usesK", "u1"]]), rubricHash: rubric, row: carrier });
    expect(viaFile).not.toBeNull();
    expect(symbolConvergenceEvidence({ fingerprints: fingerprintsOf([["usesK", "u2"]]), rubricHash: rubric, row: carrier })).not.toBe(viaFile);
    expect(symbolConvergenceEvidence({ fingerprints: fingerprintsOf([["elsewhere", "u1", [], "Run.Other"]]), rubricHash: rubric, row: carrier })).toBeNull();
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

describe("receipts of a pass that did not finish", () => {
  it("only entries both peers passed on the same evidence are kept for the next pass", async () => {
    const ledger: ConvergenceLedger = {
      "thm:a": receipt("h1"),
      "thm:b": { codex: { verdict: "matched", evidence_hash: "h2" } },
      "thm:c": { codex: { verdict: "matched", evidence_hash: "h3" }, claude: { verdict: "drift", evidence_hash: "h3" } },
      "thm:d": { codex: { verdict: "matched", evidence_hash: "h4" }, claude: { verdict: "matched", evidence_hash: "h5" } },
    };
    expect(Object.keys(dualMatchedReceipts(ledger))).toEqual(["thm:a"]);
    expect(await loadPartialReceipts(dir)).toEqual({});
    await writeFile(partialReceiptsPath(dir), JSON.stringify(ledger));
    expect(await loadPartialReceipts(dir)).toEqual({ "thm:a": receipt("h1") });
    await writeFile(partialReceiptsPath(dir), "{ not json");
    expect(await loadPartialReceipts(dir)).toEqual({});
  });
});

describe("receipts issued under the textual scheme", () => {
  it("one still current on the tree's text is re-issued at the fingerprint evidence; an `open` line voids it, a proof edit does not", async () => {
    const g = fixtureGraph();
    const legacyOf = async () => legacyNodeEvidence({ graph: g, index: await buildLeanEvidenceIndex(dir), core, rubricHash: rubric, nodeId: "thm:main" });
    const [narrow, wholeRun] = await legacyOf();
    const now = evidenceOf("thm:main", FP(), g)!;
    for (const old of [narrow, wholeRun]) {
      const ledger = { "thm:main": receipt(old) };
      expect(receiptsAt(ledger, "thm:main", now, await legacyOf())).toEqual(receipt(now));
      expect(receiptsAt(ledger, "thm:main", now, [])).toBeUndefined();
    }
    expect(receiptsAt({ "thm:main": receipt(now) }, "thm:main", now, [])).toEqual(receipt(now));
    // the text the old hash bound changed: the pair is not carried, whatever the statement means now
    await writeFile(join(dir, "Main.lean"), LEAN.replace("import Mathlib.Data.Real.Basic", "import Mathlib.Data.Real.Basic\nopen Real"));
    expect(receiptsAt({ "thm:main": receipt(narrow) }, "thm:main", now, await legacyOf())).toBeUndefined();
    await writeFile(join(dir, "Main.lean"), LEAN.replace("  sorry", "  simp"));
    expect(receiptsAt({ "thm:main": receipt(narrow) }, "thm:main", now, await legacyOf())).toEqual(receipt(now));
  });
});

describe("auditConvergenceReview", () => {
  it("passes when every governed target is dual-receipted at current evidence, and names each gap otherwise", async () => {
    const promptFile = join(dir, "prompt.txt");
    await writeFile(promptFile, "rubric v1");
    const g = fixtureGraph();
    const fp = FP();
    const audit = (graph: FormalizationGraph, fingerprints: StatementFingerprints | null = fp) =>
      auditConvergenceReview({ graph, leanDir: dir, core, promptFile, fingerprints: async () => fingerprints });
    const ev = (id: string) => evidenceOf(id, fp, g)!;
    const rows = await buildSymbolReviewRows(dir, core.symbols);
    const symEv = symbolConvergenceEvidence({ fingerprints: fp, rubricHash: rubric, row: rows[0] })!;
    const ledger: ConvergenceLedger = {
      "thm:main": receipt(ev("thm:main")),
      "def:class": receipt(ev("def:class")),
      "lem:side": receipt(ev("lem:side")),
      "sym:K": receipt(symEv),
    };
    const good = { ...g, symbolReview: { "sym:K": { verdict: "matched", hash: rows[0].hash } }, convergenceReview: ledger };
    expect(await audit(good)).toEqual([]);

    // Receipts issued under the textual scheme still clear their targets while that text stands.
    const index = await buildLeanEvidenceIndex(dir);
    const [, wholeRun] = legacyNodeEvidence({ graph: g, index, core, rubricHash: rubric, nodeId: "thm:main" });
    const earlier = { ...good, convergenceReview: { ...ledger, "thm:main": receipt(wholeRun) } };
    expect(await audit(earlier)).toEqual([]);

    // The theorem's statement changed after F4: its receipt is stale, the others still hold.
    const stale = await audit(good, fingerprintsOf(withHash(ROWS, "mainThm", "t2")));
    expect(stale.map((f) => f.node_id)).toEqual(["thm:main"]);
    expect(stale[0].message).toMatch(/stale/);

    // No fingerprints, or an anchor Lean elaborated nothing for: every such target is a finding.
    expect((await audit(good, null)).map((f) => f.node_id).sort()).toEqual(["def:class", "lem:side", "sym:K", "thm:main"]);
    const unbound = await audit(good, fingerprintsOf(ROWS.filter((r) => r[0] !== "sideLemma")));
    expect(unbound.map((f) => f.node_id)).toEqual(["lem:side"]);
    expect(unbound[0].message).toMatch(/elaborated no declaration/);

    // Reviewer prompt edited after F4: receipts hold — the rubric slot is the hand-bumped
    // REVIEW_STANDARD, so a wording change never re-buys a review.
    await writeFile(promptFile, "rubric v2");
    expect(await audit(good)).toEqual([]);

    // One peer missing / a delta-only clearance / a symbol not delta-passed.
    const half = { ...good, convergenceReview: { ...ledger, "lem:side": { codex: ledger["lem:side"].codex } } };
    expect((await audit(half)).map((f) => f.node_id)).toEqual(["lem:side"]);
    const noLedger = { ...good, convergenceReview: undefined };
    expect((await audit(noLedger)).map((f) => f.node_id).sort()).toEqual(["def:class", "lem:side", "sym:K", "thm:main"]);
    const symDrift = { ...good, symbolReview: { "sym:K": { verdict: "drift", hash: rows[0].hash } } };
    expect((await audit(symDrift)).map((f) => f.node_id)).toEqual(["sym:K"]);
    const nodeDrift = { ...good, nodes: good.nodes.map((n) => (n.id === "def:class" ? { ...n, review: { ...n.review, status: "drift" as const } } : n)) };
    expect((await audit(nodeDrift)).map((f) => f.node_id)).toEqual(["def:class"]);
  });
});
