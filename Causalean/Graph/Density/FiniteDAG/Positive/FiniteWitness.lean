module
public import Causalean.Graph.Density.FiniteDAG.Positive.Finite

/-!
# Stable finite-state DAG edge witnesses

This module packages nonzero finite-state local contrasts and proves that their nonvanishing,
and therefore edgewise conditional dependence, persists throughout one uniform factor
neighborhood.
-/

@[expose] public section

open scoped ENNReal BigOperators

noncomputable section

namespace Causalean.Graph.FiniteDensity

open Causalean Causalean.Graph Causalean.Graph.FiniteDensity MeasureTheory

universe uV uX

variable {V : Type uV} [Fintype V] [DecidableEq V]
variable {X : V → Type uX} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]
variable {G : DAG V}

namespace PositiveFiniteDAGMechanism

variable (M : PositiveFiniteDAGMechanism G X)

/-- A local edge witness records four coordinate values at which the child's cross-product
contrast is nonzero. -/
abbrev EdgeWitness (i j : V) := PositiveFactor.EdgeWitness M.factorAccessor i j

/-- A nonzero local factor contrast on an edge proves failure of conditional independence of the
edge endpoints given the child's other parents. -/
theorem EdgeWitness.not_condIndep {i j : V} (hji : G.edge j i)
    (w : M.EdgeWitness i j) :
    ¬ M.CondIndepCoordinates i j ((G.parents i).erase j) := by
  intro hCI
  exact w.nonzero ((M.edge_condIndep_iff_localContrast_zero hji).mp hCI
    w.base w.child₀ w.child₁ w.parent₀ w.parent₁)

/-- Two finite DAG mechanisms are uniformly factor-close when every local factor differs by less
than the prescribed radius at every full assignment. -/
def FactorSupClose (N : PositiveFiniteDAGMechanism G X) (ε : ℝ) : Prop :=
  PositiveFactor.FactorSupClose M.factorAccessor N.factorAccessor ε

/-- A fixed nonzero local contrast remains nonzero for every sufficiently small uniform
perturbation of all local factors. -/
theorem EdgeWitness.eventually_nonzero {i j : V} (w : M.EdgeWitness i j) :
    ∃ ε > 0, ∀ N : PositiveFiniteDAGMechanism G X,
      M.FactorSupClose N ε →
      N.localContrast i j w.base w.child₀ w.child₁ w.parent₀ w.parent₁ ≠ 0 := by
  rcases PositiveFactor.EdgeWitness.eventually_nonzero M.factorAccessor w with
    ⟨ε, hε, hopen⟩
  refine ⟨ε, hε, ?_⟩
  intro N hclose
  exact hopen N.factorAccessor hclose

/-- A [positive finite-state DAG mechanism](hyp:M) and [a nonzero local-contrast witness for
each directed edge](hyp:w) have [one positive uniform factor neighborhood in which all edge
conditional dependences persist](goal). -/
theorem all_edge_witnesses_open
    (w : ∀ i j, G.edge j i → M.EdgeWitness i j) :
    ∃ ε > 0, ∀ N : PositiveFiniteDAGMechanism G X,
      M.FactorSupClose N ε →
      ∀ i j (hji : G.edge j i),
        ¬ N.CondIndepCoordinates i j ((G.parents i).erase j) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
      letI := hV
      refine ⟨1, zero_lt_one, ?_⟩
      intro N hclose i
      exact isEmptyElim i
  | inr hV =>
      letI := hV
      let radius : V × V → ℝ := fun p ↦
        if hp : G.edge p.2 p.1 then
          Classical.choose (EdgeWitness.eventually_nonzero M (w p.1 p.2 hp))
        else 1
      have hradius_pos (p : V × V) : 0 < radius p := by
        by_cases hp : G.edge p.2 p.1
        · simp only [radius, dif_pos hp]
          exact (Classical.choose_spec
            (EdgeWitness.eventually_nonzero M (w p.1 p.2 hp))).1
        · simp [radius, hp]
      have hradius_spec (i j : V) (hji : G.edge j i) :
          ∀ N : PositiveFiniteDAGMechanism G X,
            M.FactorSupClose N (radius (i, j)) →
              N.localContrast i j (w i j hji).base (w i j hji).child₀
                (w i j hji).child₁ (w i j hji).parent₀ (w i j hji).parent₁ ≠ 0 := by
        simp only [radius, dif_pos hji]
        exact (Classical.choose_spec
          (EdgeWitness.eventually_nonzero M (w i j hji))).2
      let ε := Finset.univ.inf' Finset.univ_nonempty radius
      have hε : 0 < ε := by
        exact (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun p _ ↦ hradius_pos p
      refine ⟨ε, hε, ?_⟩
      intro N hclose i j hji
      let wN : N.EdgeWitness i j :=
        { base := (w i j hji).base
          child₀ := (w i j hji).child₀
          child₁ := (w i j hji).child₁
          parent₀ := (w i j hji).parent₀
          parent₁ := (w i j hji).parent₁
          nonzero := hradius_spec i j hji N (fun k x ↦
            (hclose k x).trans_le
              (Finset.inf'_le radius (Finset.mem_univ (i, j)))) }
      exact EdgeWitness.not_condIndep N hji wN

end PositiveFiniteDAGMechanism

end Causalean.Graph.FiniteDensity
