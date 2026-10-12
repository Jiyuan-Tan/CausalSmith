import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir, readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { refreshGraphForGate, applyVerdictsToGraph, fingerprintKeys, carryOverFingerprints } from "../../src/graph/refresh.js";
import { statementFingerprints } from "../../src/formalization/statement_fingerprints.js";
import { readScan } from "../../src/substrate/invariance.js";
import { dirtyFrontier } from "../../src/graph/diff.js";
import { createEmptyGraph, graphPath, saveGraph } from "../../src/graph/store.js";
import { buildGraphFromMd } from "../../src/graph/from_note.js";
import { addNode } from "../../src/graph/mutate.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "refresh-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

const MD = `### T-block: t1 — Rate theorem
**Statement.** the rate bound holds.
`;
const LEAN = `
def rateBound : ℝ := 1

-- @node: t1
theorem t1_thm : rateBound = 1 := by sorry
`;

async function scaffold() {
  await writeFile(path.join(dir, "q_v1.md"), MD, "utf8");
  await saveGraph(graphPath(dir, "q", "v1"), await buildGraphFromMd("q", "v1", path.join(dir, "q_v1.md")));
  const leanDir = path.join(dir, "lean");
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "T1.lean"), LEAN, "utf8");
  return leanDir;
}

describe("refreshGraphForGate", () => {
  it("loads the graph, extracts, mints hidden defs, returns skeleton+dirty+coverage", async () => {
    const leanDir = await scaffold();
    const r = await refreshGraphForGate({ formalizationDir: dir, qid: "q", spec: "v1", leanDir });
    expect(r.graph).not.toBeNull();
    const t1 = r.graph!.nodes.find((n) => n.id === "t1")!;
    expect(t1.lean.decl_name).toBe("t1_thm");
    expect(r.graph!.nodes.some((n) => n.id === "aux_rateBound")).toBe(true);
    expect(r.skeleton.some((row) => row.obj_id === "T-1")).toBe(true);
    expect(r.dirty).toContain("t1");
    expect(r.coverage).not.toBeNull();
  });

  it("returns {graph:null} when no graph JSON exists", async () => {
    const leanDir = path.join(dir, "lean2");
    await mkdir(leanDir, { recursive: true });
    const r = await refreshGraphForGate({ formalizationDir: dir, qid: "none", spec: "v1", leanDir });
    expect(r.graph).toBeNull();
    expect(r.skeleton).toEqual([]);
  });

  it("hard-fails refresh when two declarations reuse one @node id", async () => {
    const leanDir = await scaffold();
    await writeFile(
      path.join(leanDir, "T1.lean"),
      [
        "-- @node: t1",
        "theorem t1_thm : True := by trivial",
        "",
        "-- @node: t1",
        "theorem t1_companion : True := by trivial",
      ].join("\n"),
      "utf8",
    );

    const r = await refreshGraphForGate({
      formalizationDir: dir,
      qid: "q",
      spec: "v1",
      leanDir,
    });

    expect(r.graph).toBeNull();
    expect(r.error).toMatch(/unlinked Lean @node annotations/);
    expect(r.error).toContain("t1->t1_thm@T1.lean");
    expect(r.error).toContain("t1->t1_companion@T1.lean");
  });

  it("self-heals a duplicate phantom helper tag reintroduced after an earlier round minted it", async () => {
    const leanDir = await scaffold();
    const file = path.join(leanDir, "T1.lean");
    await writeFile(file, [
      "-- @node: t1",
      "theorem t1_thm : True := by trivial",
      "",
      "-- @node: l1",
      "lemma helper_first : True := by trivial",
    ].join("\n"), "utf8");
    const first = await refreshGraphForGate({
      formalizationDir: dir, qid: "q", spec: "v1", leanDir,
    });
    expect(first.graph?.nodes.find((n) => n.id === "l1")?.provenance).toBe("agent-introduced");

    await writeFile(file, [
      "-- @node: t1",
      "theorem t1_thm : True := by trivial",
      "",
      "-- @node: l1",
      "lemma helper_first : True := by trivial",
      "",
      "-- @node: l1",
      "lemma helper_second : True := by trivial",
    ].join("\n"), "utf8");
    const second = await refreshGraphForGate({ formalizationDir: dir, qid: "q", spec: "v1", leanDir });

    expect(second.graph).not.toBeNull();
    expect(second.strippedTags?.map((x) => x.id)).toContain("l1");
    expect(second.graph?.nodes.some((n) => n.id === "l1")).toBe(false);
    expect(await readFile(file, "utf8")).not.toContain("@node: l1");
  });
});

const cw = (obj_id: string, verdict: string) =>
  ({ obj_id, kind: "theorem", title: "", tex: { label: "", line_range: "" }, lean: null, verdict }) as any;

describe("applyVerdictsToGraph", () => {
  it("maps verdicts → node status (equivalent→matched, drift→drift, unmatched→skip)", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = addNode(g, { id: "p2", kind: "definition", provenance: "from-note", nl_statement: "d", tex_anchor: "" });
    g = addNode(g, { id: "l3", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
    g = applyVerdictsToGraph(g, [cw("T-1", "equivalent"), cw("P-2", "drift"), cw("L-3", "unmatched")], { t1: "h1" });
    expect(g.nodes.find((n) => n.id === "t1")!.review).toEqual({ status: "matched", passed_hash: "h1" });
    expect(g.nodes.find((n) => n.id === "p2")!.review.status).toBe("drift");
    expect(g.nodes.find((n) => n.id === "l3")!.review.status).toBe("unreviewed"); // unmatched → skipped
  });

  it("prefers an exact case-sensitive uncolonized graph id over legacy normalization", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "hP_pointwise_witness", kind: "assumption", provenance: "agent-introduced", nl_statement: "witness", tex_anchor: "" });
    g = addNode(g, { id: "hp_pointwise_witness", kind: "assumption", provenance: "from-note", nl_statement: "legacy collision", tex_anchor: "" });

    g = applyVerdictsToGraph(g, [cw("hP_pointwise_witness", "equivalent")], { hP_pointwise_witness: "exact-hash" });

    expect(g.nodes.find((n) => n.id === "hP_pointwise_witness")!.review).toEqual({ status: "matched", passed_hash: "exact-hash" });
    expect(g.nodes.find((n) => n.id === "hp_pointwise_witness")!.review.status).toBe("unreviewed");
  });

  it("preserves colon ids and unambiguous legacy from-note aliases", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "thm:case-sensitive", kind: "theorem", provenance: "from-note", nl_statement: "core theorem", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "legacy theorem", tex_anchor: "" });

    g = applyVerdictsToGraph(g, [cw("thm:case-sensitive", "equivalent"), cw("T-1", "equivalent")], {
      "thm:case-sensitive": "core-hash",
      t1: "legacy-hash",
    });

    expect(g.nodes.find((n) => n.id === "thm:case-sensitive")!.review.passed_hash).toBe("core-hash");
    expect(g.nodes.find((n) => n.id === "t1")!.review.passed_hash).toBe("legacy-hash");
  });

  it("fails closed for ambiguous or missing reviewed targets", () => {
    let ambiguous = createEmptyGraph("q", "v1");
    ambiguous = addNode(ambiguous, { id: "a1", kind: "assumption", provenance: "from-note", nl_statement: "legacy", tex_anchor: "" });
    ambiguous = addNode(ambiguous, { id: "ass:other", kind: "assumption", provenance: "from-note", nl_statement: "core", tex_anchor: "" });
    ambiguous = {
      ...ambiguous,
      nodes: ambiguous.nodes.map((n) => n.id === "ass:other" ? { ...n, obj_id: "A-1" } : n),
    };

    expect(() => applyVerdictsToGraph(ambiguous, [cw("A-1", "equivalent")], {}))
      .toThrow('review verdict target resolution failed for "A-1": ambiguous aliases: a1, ass:other');
    expect(() => applyVerdictsToGraph(createEmptyGraph("q", "v1"), [cw("missing_Target", "equivalent")], {}))
      .toThrow('review verdict target resolution failed for "missing_Target": no graph node or unambiguous legacy/from-note alias');
  });

  it("persists a real sym-prefixed graph node but skips an explicitly synthetic symbol row", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "sym:r_star", kind: "definition", provenance: "from-note", nl_statement: "radius", tex_anchor: "" });
    const owners = new Map<string, string | null>([
      ["sym:r_star", "sym:r_star"],
      ["sym:synthetic", null],
    ]);

    g = applyVerdictsToGraph(
      g,
      [cw("sym:r_star", "equivalent"), cw("sym:synthetic", "equivalent")],
      { "sym:r_star": "real-sym-hash" },
      owners,
    );

    expect(g.nodes[0].review).toEqual({ status: "matched", passed_hash: "real-sym-hash" });
    expect(g.nodes).toHaveLength(1);
  });

  it("validates the whole verdict batch before applying any row", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "theorem", tex_anchor: "" });
    const owners = new Map<string, string | null>([
      ["T-1", "t1"],
      ["missing", "does-not-exist"],
    ]);

    expect(() => applyVerdictsToGraph(
      g,
      [cw("T-1", "equivalent"), cw("missing", "equivalent")],
      { t1: "h1" },
      owners,
    )).toThrow('review verdict target resolution failed for "missing": bound graph node "does-not-exist" is missing');
    expect(g.nodes[0].review.status).toBe("unreviewed");
  });
});

describe("fingerprintKeys / carryOverFingerprints / dirtyFrontier with fingerprints", () => {
  const basis = { toolchain: "leanprover/lean4:v4.0", mathlib: "abc" };
  const fp = (t1Stmt: string, rateStmt: string) =>
    statementFingerprints(
      readScan(
        [
          JSON.stringify({ name: "t1_thm", kind: "theorem", stmt_hash: t1Stmt, module: "Run.T1", deps: ["rateBound"] }),
          JSON.stringify({ name: "rateBound", kind: "def", stmt_hash: rateStmt, module: "Run.T1", deps: [] }),
        ].join("\n"),
        new Set(["Run.T1"]),
      ),
      "Run",
      basis,
    );
  const graphWith = (passed: string | null, passedFingerprint: string | null = null) => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "the rate bound holds.", tex_anchor: "" });
    g = addNode(g, { id: "aux_other", kind: "definition", provenance: "agent-introduced", nl_statement: "other", tex_anchor: "" });
    return {
      ...g,
      nodes: g.nodes.map((n) =>
        n.id === "t1"
          ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" }, review: { status: passed ? "matched" : "unreviewed", passed_hash: passed, passed_fingerprint: passedFingerprint } }
          : { ...n, lean: { decl_name: "unknownDecl", file: "T1.lean" } }),
    } as typeof g;
  };
  const text = { t1: "text-t1", aux_other: "text-aux" };

  it("keys a known anchor by its closure and gives an unknown one no key", () => {
    const keys = fingerprintKeys(graphWith("text-t1"), fp("s1", "r1"), text);
    expect(keys.t1).toMatch(/^fp:/);
    expect(keys.aux_other).toBeUndefined();
  });

  it("carries the key onto a verdict issued at the current text, not onto a stale one", () => {
    const keys = fingerprintKeys(graphWith("text-t1"), fp("s1", "r1"), text);
    const current = carryOverFingerprints(graphWith("text-t1"), text, keys);
    expect(current.nodes.find((n) => n.id === "t1")!.review.passed_fingerprint).toBe(keys.t1);
    expect(dirtyFrontier(current, text, keys)).toEqual([]);
    const stale = carryOverFingerprints(graphWith("stale-text"), text, keys);
    expect(stale.nodes.find((n) => n.id === "t1")!.review.passed_fingerprint).toBeNull(); // the fixture's own null
    expect(dirtyFrontier(stale, text, keys)).toEqual(["t1"]);
  });

  it("with a scan: a text-only change is clean, a reached definition's change is dirty", () => {
    const keys = fingerprintKeys(graphWith("text-t1"), fp("s1", "r1"), text);
    const g = carryOverFingerprints(graphWith("text-t1"), text, keys);
    expect(dirtyFrontier(g, { ...text, t1: "text-t1-with-comment" }, keys)).toEqual([]);
    expect(dirtyFrontier(g, text, fingerprintKeys(g, fp("s1", "r2"), text))).toEqual(["t1"]);
  });

  it("a keyed node whose @node tag is gone from the Lean has no key and is dirty under a scan", () => {
    const keys = fingerprintKeys(graphWith("text-t1"), fp("s1", "r1"), text);
    const g = carryOverFingerprints(graphWith("text-t1"), text, keys);
    const untagged = { aux_other: "text-aux" }; // no fresh hash for t1: its tag was removed
    const later = fingerprintKeys(g, fp("s1", "r1"), untagged);
    expect(later.t1).toBeUndefined();
    expect(dirtyFrontier(g, untagged, later)).toEqual(["t1"]);
  });

  it("without a scan, a fingerprint-keyed verdict is compared by source text exactly as before", () => {
    const keys = fingerprintKeys(graphWith("text-t1"), fp("s1", "r1"), text);
    const g = carryOverFingerprints(graphWith("text-t1"), text, keys);
    expect(dirtyFrontier(g, text)).toEqual([]);
    expect(dirtyFrontier(g, { ...text, t1: "text-t1-changed" })).toEqual(["t1"]);
  });

  it("applyVerdictsToGraph records the fingerprint key beside the text hash, and no key without one", () => {
    const g0 = graphWith(null);
    const keys = fingerprintKeys(g0, fp("s1", "r1"), text);
    const row = { obj_id: "t1", verdict: "equivalent" } as never;
    const withKey = applyVerdictsToGraph(g0, [row], text, undefined, keys).nodes.find((n) => n.id === "t1")!.review;
    expect(withKey).toMatchObject({ passed_hash: "text-t1", passed_fingerprint: keys.t1 });
    const without = applyVerdictsToGraph(g0, [row], text).nodes.find((n) => n.id === "t1")!.review;
    expect(without).toEqual({ status: "matched", passed_hash: "text-t1" });
  });
});
