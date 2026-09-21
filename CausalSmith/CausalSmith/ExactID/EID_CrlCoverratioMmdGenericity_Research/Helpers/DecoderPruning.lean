module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderGraph

/-!
# Exact parent pruning

This file packages the set-theoretic conclusion of equation (19): once the
conditional-independence test characterizes exactly the supersets of the true
parent set, that set is the unique inclusion-minimal admissible set and the
decoder's selected graph is the permuted latent graph.
-/

public section

open Causalean.Graph


open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: exactParentPruning_at_order
/-- At one common order, the conditional-independence characterization makes the true parent
set the unique inclusion-minimal admissible set.  Given [the stated inputs and conditions](hyp:hparents,hiff), [the stated conclusion](goal) follows. -/
lemma exactParentPruning_at_order
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (laws : ObservedProbabilityLawFamily n)
    (order : Fin n → ℕ)
    (hparents : ∀ i, environmentParentSet W i ⊆ predecessorSet order i)
    (hiff : ∀ i A, A ⊆ predecessorSet order i →
      (CondIndepGiven (laws.1 0) (observedLawRankCoordinate laws order i)
        (familyProjection (observedLawRankCoordinate laws order)
          (predecessorSet order i \ A))
        (familyProjection (observedLawRankCoordinate laws order) A) ↔
      environmentParentSet W i ⊆ A)) :
    ∀ i, MinimalAdmissibleParentSet laws order i (environmentParentSet W i) ∧
      ∀ A, MinimalAdmissibleParentSet laws order i A →
        A = environmentParentSet W i := by
  intro i
  have hp := hparents i
  have hpa : AdmissibleParentSet laws order i (environmentParentSet W i) :=
    ⟨hp, (hiff i _ hp).2 Finset.Subset.rfl⟩
  have hpmin : MinimalAdmissibleParentSet laws order i (environmentParentSet W i) := by
    refine ⟨hpa, ?_⟩
    intro B hB _
    exact (hiff i B hB.1).1 hB.2
  refine ⟨hpmin, ?_⟩
  intro A hA
  apply Finset.Subset.antisymm
  · exact hA.2 _ hpa ((hiff i A hA.1.1).1 hA.1.2)
  · exact (hiff i A hA.1.1).1 hA.1.2

-- @node: exactParentPruning_of_condIndepCharacterization
/-- If admissibility is equivalent to containing the true environment-label parents for every
valid ordering, parent pruning has that parent set as its unique minimum.  Given [the stated inputs and conditions](hyp:hpred,hiff), [the stated conclusion](goal) follows. -/
lemma exactParentPruning_of_condIndepCharacterization
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (laws : ObservedProbabilityLawFamily n)
    (hpred : ∀ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap laws.1) order →
      ∀ i, environmentParentSet W i ⊆ predecessorSet order i)
    (hiff : ∀ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap laws.1) order →
      ∀ i A, A ⊆ predecessorSet order i →
        (CondIndepGiven (laws.1 0) (observedLawRankCoordinate laws order i)
          (familyProjection (observedLawRankCoordinate laws order)
            (predecessorSet order i \ A))
          (familyProjection (observedLawRankCoordinate laws order) A) ↔
        environmentParentSet W i ⊆ A)) :
    ∀ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap laws.1) order →
      ∀ i, MinimalAdmissibleParentSet laws order i (environmentParentSet W i) ∧
        ∀ A, MinimalAdmissibleParentSet laws order i A →
          A = environmentParentSet W i := by
  intro order horder i
  have hparents : environmentParentSet W i ⊆ predecessorSet order i :=
    hpred order horder i
  have hparentsAdmissible :
      AdmissibleParentSet laws order i (environmentParentSet W i) := by
    refine ⟨hparents, ?_⟩
    exact (hiff order horder i (environmentParentSet W i) hparents).2
      (Finset.Subset.rfl)
  have hparentsMinimal :
      MinimalAdmissibleParentSet laws order i (environmentParentSet W i) := by
    refine ⟨hparentsAdmissible, ?_⟩
    intro B hB _hBparents
    exact (hiff order horder i B hB.1).1 hB.2
  refine ⟨hparentsMinimal, ?_⟩
  intro A hA
  apply Finset.Subset.antisymm
  · exact hA.2 (environmentParentSet W i) hparentsAdmissible
      ((hiff order horder i A hA.1.1).1 hA.1.2)
  · exact (hiff order horder i A hA.1.1).1 hA.1.2

-- @node: selectedParentDAG_eq_permutedGraph_of_exactPruning
/-- Exact unique parent pruning at the selected topological order makes the decoder's returned
DAG equal to the environment-label pullback of the latent DAG.  Given [the stated inputs and conditions](hyp:hprune), [the stated conclusion](goal) follows. -/
lemma selectedParentDAG_eq_permutedGraph_of_exactPruning
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (laws : ObservedProbabilityLawFamily n)
    (hprune : ∀ i,
      MinimalAdmissibleParentSet laws (selectedTopologicalOrder laws) i
          (environmentParentSet W i) ∧
        ∀ A, MinimalAdmissibleParentSet laws (selectedTopologicalOrder laws) i A →
          A = environmentParentSet W i) :
    (populationDecoder laws).2.2.edge = permutedGraph G W := by
  funext j i
  apply propext
  change selectedParentRelation laws (selectedTopologicalOrder laws) j i ↔
    permutedGraph G W j i
  have hunique : ∃! A : Finset (Fin n),
      MinimalAdmissibleParentSet laws (selectedTopologicalOrder laws) i A := by
    refine ⟨environmentParentSet W i, (hprune i).1, ?_⟩
    intro A hA
    exact (hprune i).2 A hA
  have hselected : selectedParentSet laws (selectedTopologicalOrder laws) i =
      some (environmentParentSet W i) := by
    rw [selectedParentSet, dif_pos hunique]
    congr
    exact (hprune i).2 _ (Classical.choose_spec hunique.exists)
  constructor
  · rintro ⟨A, hA, hjA⟩
    rw [hselected] at hA
    injection hA with hA
    subst A
    simpa [environmentParentSet, permutedGraph] using hjA
  · intro hji
    refine ⟨environmentParentSet W i, hselected, ?_⟩
    simpa [environmentParentSet, permutedGraph] using hji

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
