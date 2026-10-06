import { describe, expect, it } from "vitest";
import { buildDeclView, isSideCondition, type ViewCard } from "../src/lib/leanDeclView.js";
import { isBinderRow, isChain, type StmtBody, type StatementItem } from "../src/lib/leanStatement.js";
import { parseCrosslinks } from "../src/lib/docmd.js";

const names = (rows: StatementItem[]) => rows.filter(isBinderRow).map((r) => r.names);
const text = (b: StmtBody | undefined) =>
  !b ? "" : isChain(b) ? "<chain>" : b.map((l) => l.text).join(" ");
const leaves = (cards: ViewCard[] | null): string[] => {
  const out: string[] = [];
  const walk = (c: ViewCard) => {
    if (c.code) out.push(text(c.code));
    for (const s of c.sub ?? []) walk(s);
  };
  for (const c of cards ?? []) walk(c);
  return out;
};

describe("buildDeclView · definitions", () => {
  const ipwLaw = `noncomputable def ipwLaw (d : Bool) (μ : Measure P.Ω) : Measure ℝ :=
  (μ.withDensity (fun ω => ENNReal.ofReal (S.ipwDensity d ω))).map S.factualY`;
  const params = [
    { n: "P", t: "POSystem", bi: "implicit" },
    { n: "γ", t: "Type u_1", bi: "implicit" },
    { n: "", t: "MeasurableSpace γ", bi: "inst" },
    { n: "S", t: "POBackdoorSystem P γ", bi: "explicit" },
    { n: "d", t: "Bool", bi: "explicit" },
    { n: "μ", t: "Measure P.Ω", bi: "explicit" },
  ];

  it("lays out parameters · def · given by, recovering section variables from the index", () => {
    const v = buildDeclView(ipwLaw, "def", params)!;
    expect(v.role).toBe("definition");
    expect(names(v.rows)).toEqual(["P", "γ", "S", "d", "μ"]);
    const section = v.rows.filter(isBinderRow).filter((r) => r.origin === "section").map((r) => r.names);
    expect(section).toEqual(["P", "γ", "S"]);
    // the def row applies the name to its EXPLICIT parameters only
    expect(v.defRow).toEqual({ head: "ipwLaw S d μ", type: [{ indent: 0, text: "Measure ℝ" }] });
    expect(v.cards).toBeNull();
    expect(text(v.flat)).toContain("μ.withDensity");
  });

  it("without index params shows only the authored telescope", () => {
    const v = buildDeclView(ipwLaw, "def")!;
    expect(names(v.rows)).toEqual(["d", "μ"]);
    expect(v.defRow?.head).toBe("ipwLaw d μ");
  });

  it("peels binders the TYPE introduces into parameter rows (Lean's own view)", () => {
    const src = `noncomputable def regimeUpToAux (S : Sys) (dbar : Fin n → δ) :
    (k : ℕ) → k ≤ n → { r : Regime // r.target = S.regimeTarget k }
  | 0, _ => sorry
  | k + 1, h => sorry`;
    const params = [
      { n: "n", t: "ℕ", bi: "implicit" },
      { n: "S", t: "Sys", bi: "explicit" },
      { n: "dbar", t: "Fin n → δ", bi: "explicit" },
      { n: "k", t: "ℕ", bi: "explicit" },
      { n: "", t: "k ≤ n", bi: "explicit" },
    ];
    const v = buildDeclView(src, "def", params)!;
    expect(names(v.rows)).toEqual(["n", "S", "dbar", "k", ""]);
    expect(v.rows.filter(isBinderRow).map((r) => r.chip)).toEqual(["decl", "decl", "decl", "decl", "hyp"]);
    expect(v.defRow).toEqual({ head: "regimeUpToAux S dbar k", type: [{ indent: 0, text: "{ r : Regime // r.target = S.regimeTarget k }" }] });
    // a ∀-typed value: `∀ v : SV, SX v`
    const w = buildDeclView("def eval (r : Regime) (ω : SOmega) : ∀ v : SV, SX v := by sorry", "def", [
      { n: "r", t: "Regime", bi: "explicit" }, { n: "ω", t: "SOmega", bi: "explicit" }, { n: "v", t: "SV", bi: "explicit" },
    ])!;
    expect(names(w.rows)).toEqual(["r", "ω", "v"]);
    expect(text(w.defRow!.type)).toBe("SX v");
  });

  it("keeps an anonymous DATA arrow of the type in the def row (only premises become rows)", () => {
    const v = buildDeclView("def poVariable (r : Regime P.V P.X) (Y : Finset P.V) : P.Ω → ValuesOn Y P.X := fun ω v => P.eval r ω v.val", "def", [
      { n: "P", t: "POSystem", bi: "implicit" }, { n: "r", t: "Regime P.V P.X", bi: "explicit" }, { n: "Y", t: "Finset P.V", bi: "explicit" }, { n: "", t: "P.Ω", bi: "explicit" },
    ])!;
    expect(names(v.rows)).toEqual(["P", "r", "Y"]);
    expect(text(v.defRow!.type)).toBe("P.Ω → ValuesOn Y P.X");
  });

  it("fills an unannotated abbrev's type from the elaborated result", () => {
    const v = buildDeclView("abbrev BBState (V : Type*) := V × BBDir", "abbrev", undefined, "Type u_2")!;
    expect(v.defRow).toEqual({ head: "BBState V", type: [{ indent: 0, text: "Type u_2" }] });
    expect(text(v.flat)).toBe("V × BBDir");
  });

  it("gives one clause per equation alternative", () => {
    const src = `def wEdge : WNode → WNode → Prop
  | Un, Xc => True
  | A,  Y  => True
  | _,  _  => False`;
    const v = buildDeclView(src, "def")!;
    expect(v.defRow?.head).toBe("wEdge");
    expect(text(v.defRow?.type)).toBe("WNode → WNode → Prop");
    expect(leaves(v.cards)).toEqual(["| Un, Xc => True", "| A, Y => True", "| _, _ => False"]);
    expect(v.cards!.map((c) => c.token)).toEqual(["⊢1", "⊢2", "⊢3"]);
  });

  it("turns a leading let-run into rows on the given-by clause", () => {
    const src = `def score (x : ℝ) : ℝ :=
  let y := x + 1
  let z := y * y
  z - 1`;
    const v = buildDeclView(src, "def")!;
    expect(v.cards).toHaveLength(1);
    expect(names(v.cards![0].hyps)).toEqual(["y", "z"]);
    expect(text(v.cards![0].code)).toBe("z - 1");
  });

  it("keeps a where-block definition as parameters · def · given by (one clause per field)", () => {
    const src = `def sys (n : ℕ) : System where
  size := n
  ok := by simp`;
    const v = buildDeclView(src, "def")!;
    expect(v.defRow?.head).toBe("sys n");
    expect(leaves(v.cards)).toEqual(["size := n", "ok := by simp"]);
  });

  it("treats `def … : Prop` as a definition whose given-by splits like a goal", () => {
    const src = `def Positive (M : Model) (X : Finset N) (hX : X ⊆ M.observed) : Prop :=
  0 < M.mass X ∧ ∀ x ∈ X, M.weight x ≠ 0`;
    const v = buildDeclView(src, "def")!;
    expect(v.role).toBe("propdef");
    expect(names(v.rows)).toEqual(["M", "X", "hX"]);
    expect(v.rows.filter(isBinderRow).map((r) => r.chip)).toEqual(["decl", "decl", "hyp"]);
    expect(v.defRow).toEqual({ head: "Positive M X hX", type: [{ indent: 0, text: "Prop" }] });
    expect(leaves(v.cards)).toEqual(["0 < M.mass X", "M.weight x ≠ 0"]);
    // the second conjunct's ∀ is lifted onto ITS card, not the parameters
    expect(names(v.cards![1].hyps)).toEqual(["x ∈ X"]);
  });

  it("declines an unbalanced / unrecognised source", () => {
    expect(buildDeclView("def broken (x := 1", "def")).toBeNull();
    expect(buildDeclView("inductive Broken (x", "inductive")).toBeNull();
  });
});

describe("buildDeclView · theorems, nested conclusions", () => {
  it("lifts a goal's leading telescope into the hypotheses and splits conjuncts into cards", () => {
    const src = `theorem thm (n : ℕ) (hn : 0 < n) : ∀ m : ℕ, n ≤ m → P n m ∧ (∀ k, k < n → Q k) := by sorry`;
    const v = buildDeclView(src, "theorem")!;
    expect(v.role).toBe("theorem");
    expect(names(v.rows)).toEqual(["n", "hn", "m", ""]);
    expect(v.rows.filter(isBinderRow).map((r) => r.chip)).toEqual(["decl", "hyp", "decl", "hyp"]);
    expect(leaves(v.cards)).toEqual(["P n m", "Q k"]);
    // the second conclusion is itself conditional: its own ∀ k / premise rows
    expect(names(v.cards![1].hyps)).toEqual(["k", ""]);
    expect(v.cards![0].token).toBe("⊢ ⊢1");
    expect(v.cards![1].token).toBe("⊢ ⊢2");
  });

  it("hoists an ∃ run and keeps its side conditions distinguishable", () => {
    const src = `theorem thm : ∃ C N : ℝ, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C := by sorry`;
    const v = buildDeclView(src, "theorem")!;
    expect(v.cards).toHaveLength(1);
    const only = v.cards![0];
    expect(only.intro?.map((l) => l.text)).toEqual(["∃ C N : ℝ,"]);
    expect(only.sub!.map(isSideCondition)).toEqual([true, false]);
  });

  it("numbers the claims under a lone ∃ frame, so (step:N) matches what the page shows", () => {
    const src = `def HasPath (X Y Z : Finset V) : Prop :=
  ∃ (p : List V), p.length ≥ 2 ∧ Active Z p ∧ p.head? ∈ X.image some ∧ p.getLast? ∈ Y.image some`;
    const v = buildDeclView(src, "def")!;
    expect(v.cards).toHaveLength(1);
    expect(v.cards![0].token).toBe("⊢");
    // a Prop-DEFINITION has a def row for the goal phrase, so claims carry only their own token
    expect(v.cards![0].sub!.map((c) => c.token)).toEqual(["⊢1", "⊢2", "⊢3", "⊢4"]);
  });

  it("accepts untyped binder groups ({Ω})", () => {
    const v = buildDeclView("lemma l {Ω} {m : MeasurableSpace Ω} (h : 0 < 1) : True := trivial", "lemma")!;
    // `{m : MeasurableSpace Ω}` folds into the `Ω` row it constrains (still hover-targetable)
    expect(names(v.rows)).toEqual(["Ω", "h"]);
    expect(v.rows.filter(isBinderRow)[0].dataNames).toBe("Ω m");
  });

  it("keeps a plain unconditional goal flat (no card chrome)", () => {
    const v = buildDeclView("theorem t (x : ℝ) : x = x := rfl", "theorem")!;
    expect(v.cards).toBeNull();
    expect(text(v.flat)).toBe("x = x");
  });
});

describe("buildDeclView · records", () => {
  it("attaches field docstrings to an assumption bundle's clauses", () => {
    const src = `structure Assumptions (S : Sys) : Prop where
  /-- Consistency links observed and potential outcomes. -/
  consistency : S.Consistency
  /-- Both arms have positive probability. -/
  overlap : ∀ᵐ ω ∂S.μ, 0 < S.e ω`;
    const v = buildDeclView(src, "structure")!;
    expect(v.role).toBe("assumption");
    expect(names(v.rows)).toEqual(["S"]);
    expect(v.fields!.map((f) => (isBinderRow(f) ? f.doc : "<comment>"))).toEqual([
      "Consistency links observed and potential outcomes.",
      "Both arms have positive probability.",
    ]);
  });

  it("keeps a data structure as parameters · fields", () => {
    const v = buildDeclView("structure Pt (n : ℕ) where\n  x : Fin n\n  y : ℝ", "structure")!;
    expect(v.role).toBe("record");
    expect(names(v.fields!)).toEqual(["x", "y"]);
  });
});

describe("docstring tokens for definitions", () => {
  it("(goal) targets ⊢ and (step:N) targets ⊢N", () => {
    const segs = parseCrosslinks("the [law](goal) is the [pushforward](step:2) of [reweighting](step:1)");
    expect(segs.filter((s) => s.links).map((s) => s.links)).toEqual([["⊢"], ["⊢2"], ["⊢1"]]);
  });
});

describe("buildDeclView · instances and inductives", () => {
  it("instance: parameters · instance · given by (term)", () => {
    const src = `scoped instance instMeasurableSpace_𝒲
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : InverseProblemSystem Ω μ) : MeasurableSpace S.𝒲 := S.inst𝒲`;
    const v = buildDeclView(src, "instance")!;
    expect(v.role).toBe("instance");
    // `{μ : Measure Ω}` folds into the Ω row it constrains (still hover-targetable)
    expect(names(v.rows)).toEqual(["Ω", "S"]);
    expect(v.rows.filter(isBinderRow)[0].dataNames).toBe("Ω μ");
    expect(v.defRow).toEqual({ head: "instMeasurableSpace_𝒲 S", type: [{ indent: 0, text: "MeasurableSpace S.𝒲" }] });
    expect(text(v.flat)).toBe("S.inst𝒲");
  });

  it("instance: anonymous, `where` structure literal → one clause per field, tokens without bare ⊢", () => {
    const src = `instance : SMul ℝ (NuisanceVec γ) where
  smul t η :=
    ⟨fun b x => t * η.μ_fn b x, fun x => t * η.e_fn x⟩
  foo := 1`;
    const v = buildDeclView(src, "instance", [{ n: "γ", t: "Type u_1", bi: "implicit" }], undefined, "instSMulReal")!;
    expect(names(v.rows)).toEqual(["γ"]);
    expect(v.defRow?.head).toBe("instSMulReal");
    expect(leaves(v.cards)).toEqual(["smul t η := ⟨fun b x => t * η.μ_fn b x, fun x => t * η.e_fn x⟩", "foo := 1"]);
    expect(v.cards!.map((c) => c.token)).toEqual(["⊢1", "⊢2"]);
  });

  it("instance given by equation alternatives → one clause each", () => {
    const v = buildDeclView("instance boolChainMeasurableSpace : ∀ n, MeasurableSpace (boolChainΩ n)\n  | d => ⊤\n  | y => ⊤", "instance")!;
    expect(v.defRow).toEqual({ head: "boolChainMeasurableSpace", type: [{ indent: 0, text: "∀ n, MeasurableSpace (boolChainΩ n)" }] });
    expect(leaves(v.cards)).toEqual(["| d => ⊤", "| y => ⊤"]);
  });

  it("def … where also splits into one clause per field", () => {
    const v = buildDeclView("def sys (n : ℕ) : System where\n  size := n\n  ok := by simp", "def")!;
    expect(leaves(v.cards)).toEqual(["size := n", "ok := by simp"]);
  });

  it("inductive: parameters · inductive · constructors, with docstrings and deriving", () => {
    const src = `inductive EdgeType
  /-- No assumption on the structural equation. -/
  | nonparametric
  | monotonic (kind : MonotonicityKind)
  | linear
  deriving DecidableEq, Repr`;
    const v = buildDeclView(src, "inductive", [], "Type")!;
    expect(v.role).toBe("inductive");
    expect(v.rows).toEqual([]);
    expect(v.defRow).toEqual({ head: "EdgeType", type: [{ indent: 0, text: "Type" }] });
    expect(v.fields!.map((f) => (isBinderRow(f) ? `${f.names} | ${text(f.body)} | ${f.doc ?? ""}` : "?"))).toEqual([
      "nonparametric |  | No assumption on the structural equation.",
      "monotonic | (kind : MonotonicityKind) | ",
      "linear |  | ",
    ]);
    expect(v.note).toBe("deriving DecidableEq, Repr");
    const w = buildDeclView("inductive SWIGNode (N : Type*)\n  | random : N → SWIGNode N\n  | fixed : N → SWIGNode N", "inductive", [{ n: "N", t: "Type u_1", bi: "explicit" }], "Type u_1")!;
    expect(w.defRow).toEqual({ head: "SWIGNode N", type: [{ indent: 0, text: "Type u_1" }] });
    expect(w.fields!.map((f) => (isBinderRow(f) ? text(f.body) : "?"))).toEqual(["N → SWIGNode N", "N → SWIGNode N"]);
  });

  it("numbered clauses of a definition carry only their own token (the goal phrase pairs with the def row)", () => {
    const v = buildDeclView("def wEdge : WNode → WNode → Prop\n  | Un, Xc => True\n  | _, _ => False", "def")!;
    expect(v.cards!.map((c) => c.token)).toEqual(["⊢1", "⊢2"]);
    const t = buildDeclView("theorem t : A ∧ B := by sorry", "theorem")!;
    expect(t.cards!.map((c) => c.token)).toEqual(["⊢ ⊢1", "⊢ ⊢2"]);
  });
});

describe("buildDeclView · audit regressions", () => {
  it("keeps ∀ᵐ / ∀ᶠ in the clause (they are not binder telescopes)", () => {
    const v = buildDeclView("theorem t (μ : Measure Ω) : ∀ᵐ x ∂μ, f x = g x := by sorry", "theorem")!;
    expect(names(v.rows)).toEqual(["μ"]);
    expect(text(v.flat)).toBe("∀ᵐ x ∂μ, f x = g x");
    const d = buildDeclView("def StrictOverlap (P : Sys) : Prop := ∀ᵐ ω ∂P.μ, 0 < P.e ω", "def")!;
    expect(names(d.rows)).toEqual(["P"]);
    expect(text(d.flat)).toBe("∀ᵐ ω ∂P.μ, 0 < P.e ω");
  });

  it("telescope-less instance: the type's own binders are not section variables", () => {
    const v = buildDeclView("noncomputable instance WΩ_borel : ∀ n, StandardBorelSpace (WΩ C n)\n  | Xc => inferInstance", "instance", [
      { n: "C", t: "Type", bi: "implicit" }, { n: "n", t: "WNode", bi: "explicit" },
    ])!;
    expect(v.rows.filter(isBinderRow).map((r) => `${r.names}${r.origin === "section" ? "*" : ""}`)).toEqual(["C*", "n"]);
    expect(v.defRow).toEqual({ head: "WΩ_borel n", type: [{ indent: 0, text: "StandardBorelSpace (WΩ C n)" }] });
  });

  it("inductive constructors are numbered clauses for (step:N)", async () => {
    const { numberedTokens } = await import("../src/lib/leanDeclView.js");
    const v = buildDeclView("inductive SWIGNode (N : Type*)\n  | random : N → SWIGNode N\n  | fixed : N → SWIGNode N", "inductive")!;
    expect([...numberedTokens(v)]).toEqual(["⊢1", "⊢2"]);
  });

  it("attaches each constructor docstring to ITS constructor", () => {
    const v = buildDeclView("inductive Foo\n  /-- doc A -/\n  | a : Foo\n  /-- doc B -/\n  | b : Foo\n  | ab : Foo", "inductive")!;
    expect(v.fields!.map((f) => (isBinderRow(f) ? `${f.names}=${f.doc ?? ""}` : "?"))).toEqual(["a=doc A", "b=doc B", "ab="]);
  });

  it("theorems and structures show section variables as shared rows", () => {
    const t = buildDeclView("theorem UAdj_symm (u v : V) : G.UAdj u v → G.UAdj v u := by sorry", "theorem", [
      { n: "V", t: "Type", bi: "implicit" }, { n: "G", t: "DAG V", bi: "explicit" }, { n: "u", t: "V", bi: "explicit" }, { n: "v", t: "V", bi: "explicit" }, { n: "", t: "G.UAdj u v", bi: "explicit" },
    ])!;
    expect(t.rows.filter(isBinderRow).map((r) => `${r.names}${r.origin === "section" ? "*" : ""}`)).toEqual(["V*", "G*", "u v", ""]);
  });
});

describe("buildDeclView · big-operator binders", () => {
  it("does not read the → inside `∑ d : Fin n → κ × Bool, …` as an implication", () => {
    const src = "theorem t (n : ℕ) : (∑ d : Fin n → κ × Bool, f d) ≤ c * ∑ d : Fin n → κ × Bool, g d := by sorry";
    const v = buildDeclView(src, "theorem")!;
    expect(names(v.rows)).toEqual(["n"]);
    expect(v.cards).toBeNull();
    expect(text(v.flat)).toContain("≤ c * ∑ d : Fin n → κ × Bool, g d");
  });
});
