import { mkdtemp, mkdir, rm, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import {
  buildCompleteCrosswalkFromGraph,
  findHiddenStatementDefs,
  findStatementSemanticDefs,
  persistCrosswalk,
  renderCrosswalkMd,
} from "../../src/formalization/crosswalk.js";
import type { FormalizationGraph } from "../../src/graph/types.js";
import { parseLeanDecls } from "../../src/formalization/crosswalk_parse.js";

// A Basic.lean mirroring the stat_ate_overlap_decay shape: a P-10 class def, a
// helper def that is no paper object, an L-7 lemma and a T-1 theorem `t1_thm`.
const BASIC = `import Mathlib

/-- A helper with no block id — must be skipped by the crosswalk. -/
noncomputable def overlapDen (x : Real) : Real := x + 1

/-! ## P-10 — Triangular-array weak-overlap class (build-inline)

Encodes A1, A2 and a boundary condition; A4/A5/A6 deferred to theorem hyps. -/
noncomputable def triangularClass (k b : Real) (n : Nat) : Set Real :=
  {x | 0 ≤ x}

/-- **L-7.** A lemma — excluded from the crosswalk. -/
lemma l7_aux : True := by sorry

theorem t1_thm (n : Nat) : n + 0 = n := by simp
`;

/** A graph node for the fixture: a content node linked to a run-local Lean decl. */
function node(id: string, objId: string, kind: FormalizationGraph["nodes"][number]["kind"], decl: string, statement: string): FormalizationGraph["nodes"][number] {
  return {
    id,
    obj_id: objId,
    kind,
    provenance: "from-note",
    nl: { statement, tex_anchor: "", frozen: true },
    lean: { decl_name: decl, file: "Basic.lean" },
    review: { status: "unreviewed", passed_hash: null },
    proof: { state: "sorry", sorry_count: 0 },
  };
}

/** The P-10 / T-1 paper as a formalization graph (what F5 builds the crosswalk from). */
const GRAPH: FormalizationGraph = {
  qid: "q",
  specialization: "s",
  nodes: [
    node("p10", "P-10", "definition", "triangularClass", "Triangular-array weak-overlap class"),
    node("t1", "T-1", "theorem", "t1_thm", "Corrected upper bound"),
  ],
  edges: [],
};

let dir: string;
let leanDir: string;

beforeEach(async () => {
  dir = await mkdtemp(path.join(os.tmpdir(), "crosswalk-"));
  leanDir = path.join(dir, "lean");
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "Basic.lean"), BASIC, "utf8");
});

afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("buildCompleteCrosswalkFromGraph", () => {
  it("anchors P-10 → triangularClass and T-1 → t1_thm with resolved line numbers", async () => {
    const rows = await buildCompleteCrosswalkFromGraph(GRAPH, leanDir);
    const p10 = rows.find((e) => e.obj_id === "P-10");
    const t1 = rows.find((e) => e.obj_id === "T-1");
    expect(p10).toBeDefined();
    expect(p10!.kind).toBe("definition");
    expect(p10!.lean).toMatchObject({ file: "Basic.lean", decl: "triangularClass", decl_kind: "def", line: 9 });
    expect(p10!.tex.label).toBe("P-10");
    expect(p10!.verdict).toBe("unmatched"); // unreviewed → the reviewer still owes a verdict
    expect(t1).toBeDefined();
    expect(t1!.kind).toBe("theorem");
    expect(t1!.lean).toMatchObject({ decl: "t1_thm", decl_kind: "theorem", line: 15 });
    expect(rows.map((e) => e.obj_id)).toEqual(["P-10", "T-1"]); // P-blocks before T-blocks
  });

  it("emits one row per content node and none for setup, gate or undelivered nodes", async () => {
    const g: FormalizationGraph = {
      ...GRAPH,
      nodes: [
        ...GRAPH.nodes,
        { ...node("setup", "S-1", "setup" as never, "overlapDen", "setup"), kind: "setup" as never },
        { ...node("gate", "G-1", "gate" as never, "overlapDen", "gate"), kind: "gate" as never },
        { ...node("l7", "L-7", "lemma", "l7_aux", "An undelivered lemma"), delivery: { status: "undelivered" } as never },
      ],
    };
    const rows = await buildCompleteCrosswalkFromGraph(g, leanDir);
    expect(rows.map((e) => e.obj_id)).toEqual(["P-10", "T-1"]);
    expect(rows.some((e) => e.lean?.decl === "overlapDen")).toBe(false);
  });

  it("downgrades unresolved local anchors instead of writing line:null", async () => {
    const g: FormalizationGraph = { ...GRAPH, nodes: [node("p1", "P-1", "definition", "MissingDecl", "S")] };
    const rows = await buildCompleteCrosswalkFromGraph(g, leanDir);
    expect(rows[0].lean).toBeNull();
  });

  it("marks a matched review as equivalent only when the row has a Lean anchor", async () => {
    const reviewed = (n: FormalizationGraph["nodes"][number]) => ({ ...n, review: { status: "matched" as const, passed_hash: "h" } });
    const g: FormalizationGraph = {
      ...GRAPH,
      nodes: [reviewed(GRAPH.nodes[0]), reviewed(node("p1", "P-1", "definition", "MissingDecl", "S"))],
    };
    const rows = await buildCompleteCrosswalkFromGraph(g, leanDir);
    expect(rows.find((e) => e.obj_id === "P-10")!.verdict).toBe("equivalent");
    expect(rows.find((e) => e.obj_id === "P-1")!.verdict).toBe("unmatched");
  });
});

describe("hidden-statement-def discovery", () => {
  it("BFS is not truncated by a named-argument `:=` in a hypothesis binder", async () => {
    // A theorem whose hypothesis uses Lean named-argument syntax `(𝒳 := 𝒳)`
    // BEFORE referencing the class def. A raw `indexOf(":=")` would cut the
    // statement at the named arg and never reach `hiddenClass` (and everything
    // it transitively reaches) — the bug that made the AUX hidden-def audit
    // silently cover almost nothing for `t2_thm`.
    const lean = `import Mathlib

/-- A build-inline membership predicate with no obj_id. -/
def hiddenInner (g : Real) : Prop := 0 ≤ g

/-- The class def, named in the CONCLUSION after the hypothesis named-arg. -/
def hiddenClass (k : Real) : Prop := hiddenInner k

/-- A wrapper that takes a named argument. -/
def wrap (p : Prop) : Prop := p

/-- **T-1.** -/
theorem t1_thm (n : Nat) (h : wrap (p := True)) : hiddenClass 0 := by sorry
`;
    await writeFile(path.join(leanDir, "Basic.lean"), lean, "utf8");
    const hidden = await findHiddenStatementDefs(leanDir);
    const names = hidden.map((h) => h.name);
    // The conclusion `hiddenClass 0` sits AFTER the `(p := True)` named-arg. A raw
    // first-`:=` cut would drop it (and its transitively-reached `hiddenInner`);
    // the depth-0 cut reaches both.
    expect(names).toContain("hiddenClass");
    expect(names).toContain("hiddenInner");
  });

  it("treats a typed-core @node theorem as a hidden-definition reachability seed", async () => {
    const lean = `import Mathlib

def atlasSemantics : Prop := True

structure AtlasPayload where
  exact : atlasSemantics

-- @node: thm:exact-real-atlas
theorem exactRealAtlas : Nonempty AtlasPayload := by sorry
`;
    await writeFile(path.join(leanDir, "Basic.lean"), lean, "utf8");
    const hidden = await findHiddenStatementDefs(leanDir);
    const payload = hidden.find((h) => h.name === "AtlasPayload");
    const semantics = hidden.find((h) => h.name === "atlasSemantics");
    expect(payload?.reachedFrom).toEqual(["thm:exact-real-atlas"]);
    expect(semantics?.reachedFrom).toEqual(["thm:exact-real-atlas"]);
    expect(payload?.contentHash).toMatch(/^[0-9a-f]{40}$/);
  });

  it("tracks deep computational statement dependencies without surfacing them as F2.5 AUX rows", async () => {
    const lean = `import Mathlib

def cadRealRootsAt (x : Real) : Set Real := {z | z = x}
def RealClosedFieldCADInterface : Prop := (cadRealRootsAt 0).Finite

-- @node: def:real-atlas-handle
def realAtlasHandleOutput : Prop := RealClosedFieldCADInterface

-- @node: thm:exact-real-atlas
theorem exactRealAtlas (hCAD : realAtlasHandleOutput) : True := by trivial
`;
    await writeFile(path.join(leanDir, "CAD.lean"), lean, "utf8");
    const semantic = await findStatementSemanticDefs(leanDir);
    expect(semantic.find((d) => d.name === "cadRealRootsAt")?.reachedFrom).toEqual([
      "thm:exact-real-atlas",
    ]);
    const hidden = await findHiddenStatementDefs(leanDir);
    expect(hidden.some((d) => d.name === "cadRealRootsAt")).toBe(false);
  });

  it("a comment, a tag or the next declaration's docstring does not move a semantic def's contentHash", async () => {
    const body = (extra: string) => `import Mathlib

-- @node: def:class
structure ModelClass where
  bound : Real${extra}

-- @node: thm:main
theorem mainThm (M : ModelClass) : M.bound = M.bound := by rfl
`;
    await writeFile(path.join(leanDir, "Hash.lean"), body(""), "utf8");
    const before = (await findStatementSemanticDefs(leanDir)).find((d) => d.name === "ModelClass")!;
    await writeFile(path.join(leanDir, "Hash.lean"), body("  -- @realizes B\n  -- a trailing remark\n\n/-- the main theorem's docstring -/"), "utf8");
    const after = (await findStatementSemanticDefs(leanDir)).find((d) => d.name === "ModelClass")!;
    expect(after.contentHash).toBe(before.contentHash);
    await writeFile(path.join(leanDir, "Hash.lean"), body("\n  bound_pos : 0 < bound"), "utf8");
    const changed = (await findStatementSemanticDefs(leanDir)).find((d) => d.name === "ModelClass")!;
    expect(changed.contentHash).not.toBe(before.contentHash);
  });

});

// A scaffold mirroring the policy-regret laundering shape:
//  - `lawClass` (Prop, ∃ real constants): reached only TRANSITIVELY via the
//    conclusion def `witnessRisk`, NO obj_id → the uniform-constant trap.
//  - `witnessRisk` (Prop): named directly in the CONCLUSION → surfaced.
//  - `hypClass` (Prop): named directly as a HYPOTHESIS → covered by H.1, must NOT
//    re-surface; but its body references `hiddenSub`, reached transitively under a
//    hypothesis (a hidden over-strengthening) → `hiddenSub` MUST surface.
//  - `bundleStruct` (structure): an assumption-bundle reached from the conclusion.
//  - `scoreVal` (ℝ computational) and `unreachedClass` (Prop, reached by nobody):
//    must stay hidden.
const LAUNDER = `import Mathlib

/-- Build-inline membership predicate — NO block id, ∃ over real constants. -/
def lawClass (P : Nat) : Prop := ∃ Co co : ℝ, 0 < Co ∧ 0 < co ∧ Co + co = (P : ℝ)

/-- An ℝ-valued helper reached only via another def's body — NOT in a conclusion. -/
def helperVal (P : Nat) : ℝ := (P : ℝ)

/-- Converse conclusion predicate referencing the membership predicate. -/
def witnessRisk (P : Nat) (rate : ℝ) : Prop := lawClass P ∧ rate ≤ helperVal P

/-- A predicate hidden UNDER a hypothesis predicate (reached transitively). -/
def hiddenSub (P : Nat) : Prop := P ≠ 0

/-- A hypothesis predicate named directly in the theorem — covered by the H.1 matrix. -/
def hypClass (P : Nat) : Prop := hiddenSub P ∧ P ≤ P

/-- An assumption-bundle structure reached from the conclusion. -/
structure bundleStruct (P : Nat) : Prop where
  fieldA : P = P

/-- An ℝ-valued quantity named DIRECTLY in the conclusion — its formula is checked. -/
def scoreVal (P : Nat) : ℝ := (P : ℝ)

/-- A Prop ∃-real class reached by NO theorem — must stay hidden. -/
def unreachedClass : Prop := ∃ K : ℝ, 0 < K

theorem t2_thm (P : Nat) (h : hypClass P) :
    ∃ rate : ℝ, witnessRisk P rate ∧ scoreVal P = scoreVal P ∧ bundleStruct P := by sorry
`;

describe("hidden-statement-def augmentation (laundering surface)", () => {
  let ldir: string;
  beforeEach(async () => {
    const d = await mkdtemp(path.join(os.tmpdir(), "crosswalk-launder-"));
    ldir = path.join(d, "lean");
    await mkdir(ldir, { recursive: true });
    await writeFile(path.join(ldir, "Basic.lean"), LAUNDER, "utf8");
  });

  it("surfaces a transitively-reached ∃-real-constant def with the uniform-constant flavor", async () => {
    const hidden = await findHiddenStatementDefs(ldir);
    const aux = hidden.find((h) => h.name === "lawClass");
    expect(aux).toBeDefined();
    expect(aux).toMatchObject({ kind: "def", flavor: "const-exist", file: "Basic.lean" });
    expect(aux!.reachedFrom).toContain("T-2"); // records the reaching theorem
  });

  it("surfaces a reached Prop conclusion def with the inline-predicate flavor", async () => {
    const hidden = await findHiddenStatementDefs(ldir);
    expect(hidden.find((h) => h.name === "witnessRisk")).toMatchObject({ flavor: "predicate" });
  });

  it("surfaces a predicate hidden TRANSITIVELY under a hypothesis, but not the direct hypothesis itself", async () => {
    const names = (await findHiddenStatementDefs(ldir)).map((h) => h.name);
    // hiddenSub is reached only via hypClass's body → must surface (hidden over-strengthening risk)
    expect(names).toContain("hiddenSub");
    // hypClass is named directly as a hypothesis → already in the H.1 matrix → must NOT re-surface
    expect(names).not.toContain("hypClass");
  });

  it("surfaces a reached assumption-bundle structure with the structure flavor", async () => {
    const hidden = await findHiddenStatementDefs(ldir);
    expect(hidden.find((h) => h.name === "bundleStruct")).toMatchObject({ kind: "structure", flavor: "structure" });
  });

  it("surfaces a conclusion-named ℝ quantity with the formula flavor", async () => {
    const hidden = await findHiddenStatementDefs(ldir);
    expect(hidden.find((h) => h.name === "scoreVal")).toMatchObject({ kind: "def", flavor: "quantity" });
  });

  it("does NOT surface ℝ helpers reached only off-conclusion, or unreached defs", async () => {
    const names = (await findHiddenStatementDefs(ldir)).map((h) => h.name);
    expect(names).not.toContain("helperVal"); // ℝ-valued, not in a conclusion
    expect(names).not.toContain("unreachedClass"); // reached by no theorem
  });
});

describe("persistCrosswalk + renderCrosswalkMd", () => {
  it("writes JSON + MD and the MD shows the P-10 row", async () => {
    const rows = await buildCompleteCrosswalkFromGraph(GRAPH, leanDir);
    const merged = rows.map((e) => (e.obj_id === "P-10" ? { ...e, verdict: "drift" as const, note: "n" } : e));
    const jsonPath = path.join(dir, "cw.json");
    const md = path.join(dir, "cw.md");
    await persistCrosswalk(jsonPath, md, merged);
    const parsed = JSON.parse(await readFile(jsonPath, "utf8"));
    expect(parsed.find((e: { obj_id: string }) => e.obj_id === "P-10").verdict).toBe("drift");
    const rendered = renderCrosswalkMd(merged);
    expect(rendered).toContain("P-10");
    expect(rendered).toContain("triangularClass");
    expect(rendered).toContain("| drift | n |");
  });
});

describe("parseLeanDecls shadow rule", () => {
  it("a *_shadow / *_deprecated / *_archived decl claims no paper id; the live decl is the sole holder", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "crosswalk-shadow-"));
    try {
      await writeFile(path.join(dir, "Basic.lean"), `import Mathlib

/-- Deprecated deterministic-CF shadow of **T-1**. Kept for provenance. -/
theorem t1_thm_deterministic_shadow (n : Nat) : n = n := by rfl

/-- **T-1 (faithful random cross-fit headline).** -/
theorem t1_thm (n : Nat) : 0 + n = n := by simp
`, "utf8");
      const decls = await parseLeanDecls(dir);
      expect(decls.find((d) => d.name === "t1_thm_deterministic_shadow")?.objId).toBeNull();
      expect(decls.find((d) => d.name === "t1_thm")?.objId).toBe("T-1");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
