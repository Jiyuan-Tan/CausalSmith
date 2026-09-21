module
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Common real-factor interface for positive finite-DAG models

This module contains the pointwise factor notions shared by uniformly positive continuous density
factorizations and positive finite-state mechanisms. The interface depends only on a real-valued
factor accessor, so the two probability theories do not duplicate their contrast and perturbation
layers.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Causalean.Graph.FiniteDensity.PositiveFactor

universe uV uX

variable {V : Type uV} [DecidableEq V] {X : V → Type uX}

/-- For [a vertex family](hyp:V), [coordinate spaces](hyp:X), the [real factor-accessor type](goal)
assigns to every vertex a real-valued function on full coordinate assignments. -/
abbrev Accessor (V : Type uV) (X : V → Type uX) := V → (∀ k : V, X k) → ℝ

/-- [Factor `i` does not depend on coordinate `j`](goal) for [a real factor accessor](hyp:factor):
changing [the parent coordinate](hyp:j) never changes [the child factor](hyp:i), whatever the rest
of the assignment. -/
def FactorIndependentOf (factor : Accessor V X) (i j : V) : Prop :=
  ∀ (x : ∀ k, X k) (xj : X j), factor i (Function.update x j xj) = factor i x

/-- The [four-point local contrast](goal) of [a real factor accessor](hyp:factor) at a
[child coordinate](hyp:i) and [parent coordinate](hyp:j), fixing a
[background assignment](hyp:x), compares the cross-products from
[two child values](hyp:xi,xi') and [two parent values](hyp:xj,xj'). Factor independence makes it
vanish, but for an arbitrary accessor the converse can fail. The converse results in later
modules require normalization and positive-model hypotheses. -/
def localContrast (factor : Accessor V X) (i j : V) (x : ∀ k, X k)
    (xi xi' : X i) (xj xj' : X j) : ℝ :=
  factor i (Function.update (Function.update x i xi) j xj) *
      factor i (Function.update (Function.update x i xi') j xj') -
    factor i (Function.update (Function.update x i xi) j xj') *
      factor i (Function.update (Function.update x i xi') j xj)

/-- A local edge witness for a real factor accessor at a child and parent coordinate records
[a common background assignment](hyp:base), [two child values](hyp:child₀,child₁),
[two parent values](hyp:parent₀,parent₁), and
[a nonzero cross-product contrast](hyp:nonzero).

For an arbitrary accessor, this certifies factor dependence only. Interpreting it as conditional
dependence requires the normalization and positive-model hypotheses imposed in later modules. -/
structure EdgeWitness (factor : Accessor V X) (i j : V) where
  /-- The common assignment fixing every coordinate not explicitly varied by the witness. -/
  base : ∀ k, X k
  /-- The first child-coordinate value. -/
  child₀ : X i
  /-- The second child-coordinate value. -/
  child₁ : X i
  /-- The first parent-coordinate value. -/
  parent₀ : X j
  /-- The second parent-coordinate value. -/
  parent₁ : X j
  /-- The displayed factor contrast is nonzero. -/
  nonzero : localContrast factor i j base child₀ child₁ parent₀ parent₁ ≠ 0

/-- Two [real factor accessors](hyp:factorM,factorN) are [uniformly close](goal) at [a
radius](hyp:ε) when every pointwise factor difference has absolute value below that radius. -/
def FactorSupClose (factorM factorN : Accessor V X) (ε : ℝ) : Prop :=
  ∀ i x, |factorN i x - factorM i x| < ε

/-- A [nonzero local contrast witness](hyp:w) for [a factor accessor](hyp:factorM) remains
[nonzero throughout some positive uniform neighborhood](goal). -/
theorem EdgeWitness.eventually_nonzero [Fintype V]
    (factorM : Accessor V X) {i j : V} (w : EdgeWitness factorM i j) :
    ∃ ε > 0, ∀ factorN : Accessor V X,
      FactorSupClose factorM factorN ε →
      localContrast factorN i j w.base w.child₀ w.child₁ w.parent₀ w.parent₁ ≠ 0 := by
  let a : Fin 4 → ℝ := ![
    factorM i (Function.update (Function.update w.base i w.child₀) j w.parent₀),
    factorM i (Function.update (Function.update w.base i w.child₁) j w.parent₁),
    factorM i (Function.update (Function.update w.base i w.child₀) j w.parent₁),
    factorM i (Function.update (Function.update w.base i w.child₁) j w.parent₀)]
  let q : (Fin 4 → ℝ) → ℝ := fun z ↦ z 0 * z 1 - z 2 * z 3
  have hqa : q a ≠ 0 := by
    simpa [q, a, localContrast] using w.nonzero
  have hq : Continuous q := by
    unfold q
    exact ((continuous_apply 0).mul (continuous_apply 1)).sub
      ((continuous_apply 2).mul (continuous_apply 3))
  have hne : {z | q z ≠ 0} ∈ nhds a := hq.continuousAt.eventually_ne hqa
  rcases Metric.mem_nhds_iff.mp hne with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro factorN hclose
  let b : Fin 4 → ℝ := ![
    factorN i (Function.update (Function.update w.base i w.child₀) j w.parent₀),
    factorN i (Function.update (Function.update w.base i w.child₁) j w.parent₁),
    factorN i (Function.update (Function.update w.base i w.child₀) j w.parent₁),
    factorN i (Function.update (Function.update w.base i w.child₁) j w.parent₀)]
  have hba : dist b a < ε := by
    rw [dist_pi_lt_iff hε]
    intro k
    fin_cases k
    · simpa [b, a, Real.dist_eq] using hclose i
        (Function.update (Function.update w.base i w.child₀) j w.parent₀)
    · simpa [b, a, Real.dist_eq] using hclose i
        (Function.update (Function.update w.base i w.child₁) j w.parent₁)
    · simpa [b, a, Real.dist_eq] using hclose i
        (Function.update (Function.update w.base i w.child₀) j w.parent₁)
    · simpa [b, a, Real.dist_eq] using hclose i
        (Function.update (Function.update w.base i w.child₁) j w.parent₀)
  have hqb : q b ≠ 0 := hball (Metric.mem_ball.mpr hba)
  change q b ≠ 0
  exact hqb

end Causalean.Graph.FiniteDensity.PositiveFactor
