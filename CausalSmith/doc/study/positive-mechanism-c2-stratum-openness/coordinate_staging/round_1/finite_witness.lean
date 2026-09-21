import Causalean.Graph.FiniteDensity.Positive.Finite

/-!
# Stable finite-state DAG edge witnesses

This module packages nonzero finite-state local contrasts and proves that their nonvanishing,
and therefore edgewise conditional dependence, persists throughout one uniform factor
neighborhood.
-/

open scoped ENNReal BigOperators

noncomputable section

namespace Causalean.Graph.FiniteDensity

open Causalean Causalean.Graph.FiniteDensity MeasureTheory

universe uV uX

variable {V : Type uV} [Fintype V] [DecidableEq V]
variable {X : V → Type uX} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]
variable {G : DAG V}

namespace PositiveFiniteDAGMechanism

variable (M : PositiveFiniteDAGMechanism G X)

/-- A local edge witness records four coordinate values at which the child's cross-product
contrast is nonzero. -/
structure EdgeWitness (i j : V) where
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
  nonzero : M.localContrast i j base child₀ child₁ parent₀ parent₁ ≠ 0

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
  ∀ i x, |N.factor i x - M.factor i x| < ε

/-- A fixed nonzero local contrast remains nonzero for every sufficiently small uniform
perturbation of all local factors. -/
theorem EdgeWitness.eventually_nonzero {i j : V} (w : M.EdgeWitness i j) :
    ∃ ε > 0, ∀ N : PositiveFiniteDAGMechanism G X,
      M.FactorSupClose N ε →
      N.localContrast i j w.base w.child₀ w.child₁ w.parent₀ w.parent₁ ≠ 0 := by
  let a : Fin 4 → ℝ := ![
    M.factor i (Function.update (Function.update w.base i w.child₀) j w.parent₀),
    M.factor i (Function.update (Function.update w.base i w.child₁) j w.parent₁),
    M.factor i (Function.update (Function.update w.base i w.child₀) j w.parent₁),
    M.factor i (Function.update (Function.update w.base i w.child₁) j w.parent₀)]
  let q : (Fin 4 → ℝ) → ℝ := fun z ↦ z 0 * z 1 - z 2 * z 3
  have hqa : q a ≠ 0 := by
    simpa [q, a, localContrast] using w.nonzero
  have hq : Continuous q := by
    unfold q
    fun_prop
  have hne : {z | q z ≠ 0} ∈ nhds a :=
    hq.continuousAt.eventually_ne hqa
  rcases Metric.mem_nhds_iff.mp hne with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro N hclose
  let b : Fin 4 → ℝ := ![
    N.factor i (Function.update (Function.update w.base i w.child₀) j w.parent₀),
    N.factor i (Function.update (Function.update w.base i w.child₁) j w.parent₁),
    N.factor i (Function.update (Function.update w.base i w.child₀) j w.parent₁),
    N.factor i (Function.update (Function.update w.base i w.child₁) j w.parent₀)]
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
  simpa [q, b, localContrast] using hqb

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
