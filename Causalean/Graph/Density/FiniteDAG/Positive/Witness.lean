module
public import Causalean.Graph.Density.FiniteDAG.Positive.Edge

/-!
# Stable contrast witnesses on compact coordinates

For uniformly positive continuous DAG densities on compact coordinates, this module packages
nonzero four-point local-factor contrasts as witnesses that an edge is not conditionally
independent given the other parents. It also proves that finitely many such witnesses persist
under one uniform factor neighborhood.
-/

@[expose] public section

open scoped ENNReal BigOperators
open Set Function MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

open Causalean Causalean.Graph Causalean.Graph.FiniteDensity

universe uV uX

variable {V : Type uV} [Fintype V] [DecidableEq V]
variable {X : V → Type uX} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : DAG V}
variable [∀ i, TopologicalSpace (X i)] [∀ i, BorelSpace (X i)]
variable [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
variable [∀ i, StandardBorelSpace (X i)] [∀ i, (μ i).IsOpenPosMeasure]

namespace UniformlyPositiveContinuousFactorization

variable (M : UniformlyPositiveContinuousFactorization G X μ)

/-- A compact-density edge witness records four domain points at which the child's local
cross-product contrast is nonzero. -/
abbrev EdgeWitness (i j : V) := PositiveFactor.EdgeWitness M.factorAccessor i j

/-- A nonzero local factor contrast on an edge rules out conditional independence of the edge
endpoints given the other parents. -/
theorem EdgeWitness.not_condIndep {i j : V} (hji : G.edge j i)
    (w : M.EdgeWitness i j) :
    ¬ M.CondIndepCoordinates i j ((G.parents i).erase j) := by
  intro hCI
  exact w.nonzero ((M.edge_condIndep_iff_localContrast_zero hji).mp hCI
    w.base w.child₀ w.child₁ w.parent₀ w.parent₁)

/-- Two compact positive mechanisms are uniformly close when the real values of all local
density factors differ by less than one common radius over every node and domain point. -/
def FactorSupClose (N : UniformlyPositiveContinuousFactorization G X μ) (ε : ℝ) : Prop :=
  PositiveFactor.FactorSupClose M.factorAccessor N.factorAccessor ε

/-- A fixed nonzero compact-domain contrast remains a nonzero witness, and hence continues to
rule out edge conditional independence, throughout a sufficiently small uniform neighborhood. -/
theorem EdgeWitness.eventually_not_condIndep {i j : V} (hji : G.edge j i)
    (w : M.EdgeWitness i j) :
    ∃ ε > 0, ∀ N : UniformlyPositiveContinuousFactorization G X μ,
      M.FactorSupClose N ε →
      ¬ N.CondIndepCoordinates i j ((G.parents i).erase j) := by
  rcases PositiveFactor.EdgeWitness.eventually_nonzero M.factorAccessor w with
    ⟨ε, hε, hopen⟩
  refine ⟨ε, hε, ?_⟩
  intro N hclose
  let wN : N.EdgeWitness i j :=
    { base := w.base
      child₀ := w.child₀
      child₁ := w.child₁
      parent₀ := w.parent₀
      parent₁ := w.parent₁
      nonzero := hopen N.factorAccessor hclose }
  exact EdgeWitness.not_condIndep N hji wN

/-- A [uniformly positive continuous factorization on compact coordinates](hyp:M) with
[a nonzero local-contrast witness for each directed edge](hyp:w) has
[a common stability neighborhood](goal) in which every edge remains conditionally dependent
given its other parents. -/
theorem all_edge_witnesses_open
    (w : ∀ i j, G.edge j i → M.EdgeWitness i j) :
    ∃ ε > 0, ∀ N : UniformlyPositiveContinuousFactorization G X μ,
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
          Classical.choose (EdgeWitness.eventually_not_condIndep M hp (w p.1 p.2 hp))
        else 1
      have hradius_pos (p : V × V) : 0 < radius p := by
        by_cases hp : G.edge p.2 p.1
        · simp only [radius, dif_pos hp]
          exact (Classical.choose_spec
            (EdgeWitness.eventually_not_condIndep M hp (w p.1 p.2 hp))).1
        · simp [radius, hp]
      have hradius_spec (i j : V) (hji : G.edge j i) :
          ∀ N : UniformlyPositiveContinuousFactorization G X μ,
            M.FactorSupClose N (radius (i, j)) →
              ¬ N.CondIndepCoordinates i j ((G.parents i).erase j) := by
        simp only [radius, dif_pos hji]
        exact (Classical.choose_spec
          (EdgeWitness.eventually_not_condIndep M hji (w i j hji))).2
      let ε := Finset.univ.inf' Finset.univ_nonempty radius
      have hε : 0 < ε := by
        exact (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun p _ ↦ hradius_pos p
      refine ⟨ε, hε, ?_⟩
      intro N hclose i j hji
      apply hradius_spec i j hji N
      intro k x
      exact (hclose k x).trans_le
        (Finset.inf'_le radius (Finset.mem_univ (i, j)))

end UniformlyPositiveContinuousFactorization

end Causalean.Graph.FiniteDensity
