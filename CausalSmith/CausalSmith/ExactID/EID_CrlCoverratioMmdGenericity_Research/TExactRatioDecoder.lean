module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Decoder
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.CondIndepIntersection
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.CitedGates
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.FiniteDensityBridge
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderCore
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderRank
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderGraph
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderPruning
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderTriangularInverse
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderConditionalKernel
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderCompProd
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderContinuousVersion
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderRankAssembly
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderRepresentation
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderOrderedLocalMarkov
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderRankCondIndep
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderRankPruning
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Exact ratio decoder

This file states the population transitive-closure, continuous conditional-rank,
parent-pruning, ordering-independence, and representation-uniqueness conclusions.
Faithfulness is confined to a separate overlap corollary.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- The componentwise `C²` ambiguity relating two compatible representations. -/
def ComponentwiseC2Equivalent
    {n : ℕ} {G₁ G₂ : DAG (Fin n)}
    {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂) : Prop :=
  observedSupport G₁ W₁ = observedSupport G₂ W₂ ∧
  ∃ σ : Equiv.Perm (Fin n),
    (∀ j i, G₂.edge (σ j) (σ i) ↔ G₁.edge j i) ∧
    (∀ e, W₂.targetPerm e = σ (W₁.targetPerm e)) ∧
    ∃ h hinv : Fin n → ℝ → ℝ,
      (∀ i, ContDiffOn ℝ 2 (h i) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ i, ContDiffOn ℝ 2 (hinv i) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ i, Set.MapsTo (h i) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ i, Set.MapsTo (hinv i) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ i z, z ∈ Set.Icc (0 : ℝ) 1 → hinv i (h i z) = z) ∧
      (∀ i z, z ∈ Set.Icc (0 : ℝ) 1 → h i (hinv i z) = z) ∧
      (∀ x ∈ observedSupport G₁ W₁, ∀ i,
        W₂.unmix x (σ i) = h i (W₁.unmix x i))

-- @node: componentwiseC2Equivalent_of_common_rank_and_aligned_edges
/-- Common law-selected scalar ranks and aligned edges assemble the componentwise `C²`
equivalence, including explicit inverse charts on the closed latent interval.  Given [the stated inputs and conditions](hyp:hpos₁,hmix₁,hpos₂,hmix₂,hrank₁,hrank₂,hsupport,hedge), [the stated conclusion](goal) follows. -/
lemma componentwiseC2Equivalent_of_common_rank_and_aligned_edges
    {n : ℕ} {G₁ G₂ : DAG (Fin n)}
    {s : SignVector n} {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂)
    (hpos₁ : PositiveNormalizedSmoothMechanisms G₁ θ₁)
    (hmix₁ : SharedDiffeomorphicMixing G₁ θ₁ W₁)
    (hpos₂ : PositiveNormalizedSmoothMechanisms G₂ θ₂)
    (hmix₂ : SharedDiffeomorphicMixing G₂ θ₂ W₂)
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ)
    (hrank₁ : ∀ e v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order e (W₁.mix v) : ℝ) =
        signedInterventionCDF s θ₁ (W₁.targetPerm e) (v (W₁.targetPerm e)))
    (hrank₂ : ∀ e v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order e (W₂.mix v) : ℝ) =
        signedInterventionCDF s θ₂ (W₂.targetPerm e) (v (W₂.targetPerm e)))
    (hsupport : observedSupport G₁ W₁ = observedSupport G₂ W₂)
    (hedge : ∀ j i,
      G₂.edge ((W₁.targetPerm.symm.trans W₂.targetPerm) j)
          ((W₁.targetPerm.symm.trans W₂.targetPerm) i) ↔ G₁.edge j i) :
    ComponentwiseC2Equivalent W₁ W₂ := by
  let σ : Equiv.Perm (Fin n) := W₁.targetPerm.symm.trans W₂.targetPerm
  let base : LatentState n := 0
  let h : Fin n → ℝ → ℝ := fun i z =>
    W₂.unmix (W₁.mix (Function.update base i z)) (σ i)
  let hinv : Fin n → ℝ → ℝ := fun i z =>
    W₁.unmix (W₂.mix (Function.update base (σ i) z)) i
  have hbase (i : Fin n) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
      Function.update base i z ∈ latentCube n := by
    intro k hk
    by_cases hki : k = i
    · subst k; simpa [Function.update]
    · simp [base, Function.update, hki]
  have hsigma (i : Fin n) : σ i = W₂.targetPerm (W₁.targetPerm.symm i) := rfl
  have hmaps (i : Fin n) : Set.MapsTo (h i) (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) := by
    intro z hz
    have hy₁ : W₁.mix (Function.update base i z) ∈ observedSupport G₁ W₁ :=
      ⟨_, hbase i z hz, rfl⟩
    have hy₂ : W₁.mix (Function.update base i z) ∈ observedSupport G₂ W₂ := by
      rw [← hsupport]; exact hy₁
    rcases hy₂ with ⟨v, hv, heq⟩
    dsimp only [h]
    rw [← heq, hmix₂.2.2.1 v hv]
    exact hv (σ i) (Set.mem_univ _)
  have hinvmaps (i : Fin n) : Set.MapsTo (hinv i) (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) := by
    intro z hz
    have hy₂ : W₂.mix (Function.update base (σ i) z) ∈ observedSupport G₂ W₂ :=
      ⟨_, hbase (σ i) z hz, rfl⟩
    have hy₁ : W₂.mix (Function.update base (σ i) z) ∈ observedSupport G₁ W₁ := by
      rw [hsupport]; exact hy₂
    rcases hy₁ with ⟨v, hv, heq⟩
    dsimp only [hinv]
    rw [← heq, hmix₁.2.2.1 v hv]
    exact hv i (Set.mem_univ _)
  have hdepend : ∀ x ∈ observedSupport G₁ W₁, ∀ i,
      W₂.unmix x (σ i) = h i (W₁.unmix x i) := by
    intro x hx i
    have hx₂ : x ∈ observedSupport G₂ W₂ := by rw [← hsupport]; exact hx
    let y := W₁.mix (Function.update base i (W₁.unmix x i))
    have hxi : W₁.unmix x i ∈ Set.Icc (0 : ℝ) 1 := by
      rcases hx with ⟨v, hv, rfl⟩
      simpa only [hmix₁.2.2.1 v hv] using hv i (Set.mem_univ _)
    have hy₁ : y ∈ observedSupport G₁ W₁ := ⟨_, hbase i _ hxi, rfl⟩
    have hy₂ : y ∈ observedSupport G₂ W₂ := by rw [← hsupport]; exact hy₁
    have hcoord : W₁.unmix x (W₁.targetPerm (W₁.targetPerm.symm i)) =
        W₁.unmix y (W₁.targetPerm (W₁.targetPerm.symm i)) := by
      simp only [W₁.targetPerm.apply_symm_apply]
      rw [show W₁.unmix y = Function.update base i (W₁.unmix x i) by
        exact hmix₁.2.2.1 _ (hbase i _ hxi)]
      simp
    have hc := alignedCoordinate_eq_of_common_rank W₁ W₂ hmix₁ hpos₂ hmix₂
      laws order hrank₁ hrank₂ x y hx hx₂ hy₁ hy₂ (W₁.targetPerm.symm i) hcoord
    simpa only [W₁.targetPerm.apply_symm_apply, hsigma, h] using hc
  refine ⟨hsupport, σ, hedge, ?_, h, hinv, ?_, ?_, hmaps, hinvmaps, ?_, ?_, hdepend⟩
  · intro e
    simp [σ]
  · intro i
    have hup : ContDiffOn ℝ 2 (Function.update base i) (Set.Icc (0 : ℝ) 1) :=
      (contDiff_update 2 base i).contDiffOn
    have hf : ContDiffOn ℝ 2 (W₁.mix ∘ Function.update base i) (Set.Icc 0 1) :=
      hmix₁.1.comp hup (hbase i)
    have hfmap : Set.MapsTo (W₁.mix ∘ Function.update base i) (Set.Icc (0 : ℝ) 1)
        (observedSupport G₂ W₂) := by
      intro z hz
      rw [← hsupport]
      exact ⟨_, hbase i z hz, rfl⟩
    have hg : ContDiffOn ℝ 2
        (W₂.unmix ∘ W₁.mix ∘ Function.update base i) (Set.Icc (0 : ℝ) 1) := by
      convert hmix₂.2.1.comp hf hfmap using 1
    change ContDiffOn ℝ 2
      ((fun v : LatentState n ↦ v (σ i)) ∘
        (W₂.unmix ∘ W₁.mix ∘ Function.update base i)) (Set.Icc (0 : ℝ) 1)
    exact (contDiff_apply ℝ ℝ (σ i)).contDiffOn.comp hg (Set.mapsTo_univ _ _)
  · intro i
    have hup : ContDiffOn ℝ 2 (Function.update base (σ i)) (Set.Icc (0 : ℝ) 1) :=
      (contDiff_update 2 base (σ i)).contDiffOn
    have hf : ContDiffOn ℝ 2 (W₂.mix ∘ Function.update base (σ i)) (Set.Icc 0 1) :=
      hmix₂.1.comp hup (hbase (σ i))
    have hfmap : Set.MapsTo (W₂.mix ∘ Function.update base (σ i)) (Set.Icc (0 : ℝ) 1)
        (observedSupport G₁ W₁) := by
      intro z hz
      rw [hsupport]
      exact ⟨_, hbase (σ i) z hz, rfl⟩
    have hg : ContDiffOn ℝ 2
        (W₁.unmix ∘ W₂.mix ∘ Function.update base (σ i)) (Set.Icc (0 : ℝ) 1) := by
      convert hmix₁.2.1.comp hf hfmap using 1
    change ContDiffOn ℝ 2
      ((fun v : LatentState n ↦ v i) ∘
        (W₁.unmix ∘ W₂.mix ∘ Function.update base (σ i))) (Set.Icc (0 : ℝ) 1)
    exact (contDiff_apply ℝ ℝ i).contDiffOn.comp hg (Set.mapsTo_univ _ _)
  · intro i z hz
    let y₁ := W₁.mix (Function.update base i z)
    let y₂ := W₂.mix (Function.update base (σ i) (h i z))
    have hy₁₁ : y₁ ∈ observedSupport G₁ W₁ := ⟨_, hbase i z hz, rfl⟩
    have hy₁₂ : y₁ ∈ observedSupport G₂ W₂ := by rw [← hsupport]; exact hy₁₁
    have hhmem := hmaps i hz
    have hy₂₂ : y₂ ∈ observedSupport G₂ W₂ := ⟨_, hbase (σ i) _ hhmem, rfl⟩
    have hy₂₁ : y₂ ∈ observedSupport G₁ W₁ := by rw [hsupport]; exact hy₂₂
    let e := W₂.targetPerm.symm (σ i)
    have he : e = W₁.targetPerm.symm i := by
      apply W₂.targetPerm.injective
      simp [e, hsigma]
    have hcoord : W₂.unmix y₁ (W₂.targetPerm e) =
        W₂.unmix y₂ (W₂.targetPerm e) := by
      rw [W₂.targetPerm.apply_symm_apply]
      rw [show W₂.unmix y₂ = Function.update base (σ i) (h i z) by
        exact hmix₂.2.2.1 _ (hbase (σ i) _ hhmem)]
      simp only [Function.update_self]
      rfl
    have hc := alignedCoordinate_eq_of_common_rank W₂ W₁ hmix₂ hpos₁ hmix₁
      laws order hrank₂ hrank₁ y₁ y₂ hy₁₂ hy₁₁ hy₂₂ hy₂₁ e hcoord
    rw [he, W₁.targetPerm.apply_symm_apply] at hc
    rw [show W₁.unmix y₁ = Function.update base i z by
      exact hmix₁.2.2.1 _ (hbase i z hz)] at hc
    simpa only [Function.update_self, hinv, y₂] using hc.symm
  · intro i z hz
    let y₂ := W₂.mix (Function.update base (σ i) z)
    let y₁ := W₁.mix (Function.update base i (hinv i z))
    have hy₂₂ : y₂ ∈ observedSupport G₂ W₂ := ⟨_, hbase (σ i) z hz, rfl⟩
    have hy₂₁ : y₂ ∈ observedSupport G₁ W₁ := by rw [hsupport]; exact hy₂₂
    have himem := hinvmaps i hz
    have hy₁₁ : y₁ ∈ observedSupport G₁ W₁ := ⟨_, hbase i _ himem, rfl⟩
    have hy₁₂ : y₁ ∈ observedSupport G₂ W₂ := by rw [← hsupport]; exact hy₁₁
    let e := W₁.targetPerm.symm i
    have hcoord : W₁.unmix y₂ (W₁.targetPerm e) =
        W₁.unmix y₁ (W₁.targetPerm e) := by
      rw [W₁.targetPerm.apply_symm_apply]
      rw [show W₁.unmix y₁ = Function.update base i (hinv i z) by
        exact hmix₁.2.2.1 _ (hbase i _ himem)]
      simp only [Function.update_self]
      rfl
    have hc := alignedCoordinate_eq_of_common_rank W₁ W₂ hmix₁ hpos₂ hmix₂
      laws order hrank₁ hrank₂ y₂ y₁ hy₂₁ hy₂₂ hy₁₁ hy₁₂ e hcoord
    have hsige : W₂.targetPerm e = σ i := by simp [e, σ]
    rw [hsige] at hc
    rw [show W₂.unmix y₂ = Function.update base (σ i) z by
      exact hmix₂.2.2.1 _ (hbase (σ i) z hz)] at hc
    simpa only [Function.update_self, h, y₁] using hc.symm

-- @node: componentwiseC2Equivalent_of_common_exactPruning
/-- Exact law-only pruning for two compatible causal-minimal representations first aligns their
graphs; their common selected rank coordinates then assemble the componentwise `C²` ambiguity.
No cover-separation condition is imposed on the competitor.  Given [the stated inputs and conditions](hyp:hpos₁,hmix₁,hone₁,hsign₁,hpos₂,hmix₂,hone₂,hsign₂,hlaw,htc₁,hprune₁,hprune₂), [the stated conclusion](goal) follows. -/
lemma componentwiseC2Equivalent_of_common_exactPruning
    {n : ℕ} {G₁ G₂ : DAG (Fin n)} (s : SignVector n)
    {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂)
    (hpos₁ : PositiveNormalizedSmoothMechanisms G₁ θ₁)
    (hmix₁ : SharedDiffeomorphicMixing G₁ θ₁ W₁)
    (hone₁ : OnePerfectInterventionPerNode G₁ θ₁ W₁)
    (hsign₁ : FixedOwnDerivativeSign G₁ s θ₁)
    (hpos₂ : PositiveNormalizedSmoothMechanisms G₂ θ₂)
    (hmix₂ : SharedDiffeomorphicMixing G₂ θ₂ W₂)
    (hone₂ : OnePerfectInterventionPerNode G₂ θ₂ W₂)
    (hsign₂ : FixedOwnDerivativeSign G₂ s θ₂)
    (hlaw : W₂.law = W₁.law)
    (htc₁ : Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W₁.law) =
      Relation.TransGen (permutedGraph G₁ W₁))
    (hprune₁ : ∀ i,
      MinimalAdmissibleParentSet (observedProbabilityLawFamily W₁.law)
          (selectedTopologicalOrder (observedProbabilityLawFamily W₁.law)) i
          (environmentParentSet W₁ i) ∧
        ∀ A, MinimalAdmissibleParentSet (observedProbabilityLawFamily W₁.law)
            (selectedTopologicalOrder (observedProbabilityLawFamily W₁.law)) i A →
          A = environmentParentSet W₁ i)
    (hprune₂ : ∀ i,
      MinimalAdmissibleParentSet (observedProbabilityLawFamily W₁.law)
          (selectedTopologicalOrder (observedProbabilityLawFamily W₁.law)) i
          (environmentParentSet W₂ i) ∧
        ∀ A, MinimalAdmissibleParentSet (observedProbabilityLawFamily W₁.law)
            (selectedTopologicalOrder (observedProbabilityLawFamily W₁.law)) i A →
          A = environmentParentSet W₂ i) :
    ComponentwiseC2Equivalent W₁ W₂ := by
  let laws := observedProbabilityLawFamily W₁.law
  let order := selectedTopologicalOrder laws
  have hgraph₁ : (selectedParentDAG laws order).edge = permutedGraph G₁ W₁ :=
    selectedParentDAG_eq_permutedGraph_of_exactPruning W₁ laws hprune₁
  have hgraph₂ : (selectedParentDAG laws order).edge = permutedGraph G₂ W₂ :=
    selectedParentDAG_eq_permutedGraph_of_exactPruning W₂ laws hprune₂
  have hperm : permutedGraph G₁ W₁ = permutedGraph G₂ W₂ :=
    hgraph₁.symm.trans hgraph₂
  have htc₂ : Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W₂.law) =
      Relation.TransGen (permutedGraph G₂ W₂) := by
    rw [hlaw, htc₁, hperm]
  have horder : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W₁.law) order := by
    exact selectedTopologicalOrder_valid_of_assumptions
      (s := s) W₁ hpos₁ hmix₁ hone₁
  have horder₂ : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W₂.law) order := by
    simpa only [hlaw] using horder
  have hrank₁ : ∀ e v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order e (W₁.mix v) : ℝ) =
        signedInterventionCDF s θ₁ (W₁.targetPerm e) (v (W₁.targetPerm e)) := by
    intro e v hv
    simpa only [laws, order, signedInterventionCDF] using
      (exactRatioDecoder_continuousRankClauses s W₁ hpos₁ hmix₁ hone₁ hsign₁
        htc₁ order horder e).2.2.2.2 v hv
  have hrank₂ : ∀ e v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order e (W₂.mix v) : ℝ) =
        signedInterventionCDF s θ₂ (W₂.targetPerm e) (v (W₂.targetPerm e)) := by
    intro e v hv
    simpa only [laws, order, hlaw, signedInterventionCDF] using
      (exactRatioDecoder_continuousRankClauses s W₂ hpos₂ hmix₂ hone₂ hsign₂
        htc₂ order horder₂ e).2.2.2.2 v hv
  have hsupport := observedSupport_eq_of_observationalLaw_eq W₁ W₂
    hpos₁ hmix₁ hone₁ hpos₂ hmix₂ hone₂ hlaw
  exact componentwiseC2Equivalent_of_common_rank_and_aligned_edges W₁ W₂
    hpos₁ hmix₁ hpos₂ hmix₂ laws order hrank₁ hrank₂ hsupport
    (aligned_edge_iff_of_permutedGraph_eq W₁ W₂ hperm)

/-- On the faithful overlap with von Kügelgen et al. (2023), the present law-only decoder uses
one unknown-target intervention per node, strictly fewer than the comparator's two interventions
per node in arbitrary dimension, while retaining representation uniqueness. -/
def VonKugelgenTwoVersusOneComparison
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (W : ObservedWorld G θ) : Prop :=
  vonKugelgenComparatorScope =
      "von Kugelgen et al. (2023), Nonparametric Identifiability of Causal Representations from Unknown Interventions, Theorems 3.2 and 3.4 and Section 7 (vonKugelgenEtAl2023UnknownInterventions; https://papers.nips.cc/paper_files/paper/2023/file/97fe251c25b6f99a2a23b330a75b11d4-Paper-Conference.pdf): Theorem 3.2 is bivariate with one unknown-target perfect intervention per node and a continuous witness genericity condition; Theorem 3.4 uses two paired perfect interventions per node in arbitrary dimension; the one-intervention extension for n greater than two is stated as a conjecture." ∧
  (Faithfulness G θ →
    (∀ i : Fin n, ∃! e : Fin n, W.targetPerm e = i) ∧
    (1 : ℕ) < 2 ∧
    ∀ (G' : DAG (Fin n)) (θ' : Mechanism n G')
      (W' : ObservedWorld G' θ'),
      PositiveNormalizedSmoothMechanisms G' θ' → CausalMinimality G' θ' →
      FixedOwnDerivativeSign G' s θ' → SharedDiffeomorphicMixing G' θ' W' →
      OnePerfectInterventionPerNode G' θ' W' → W'.law = W.law →
      ComponentwiseC2Equivalent W W')

/-- Explicit scope boundary for the comparison with von Kügelgen et al. (2023): the present
result assumes positive `C³` densities on the compact latent cube and `C²` mixing.  In positive
dimension that cube is strictly smaller than the full Euclidean latent space, and derivative
order two is not the comparator's `C¹` order. -/
def FullRnC1NoncoverageClause
    {n : ℕ} {G : DAG (Fin n)} (θ : Mechanism n G)
    (W : ObservedWorld G θ) : Prop :=
  vonKugelgenComparatorScope =
      "von Kugelgen et al. (2023), Nonparametric Identifiability of Causal Representations from Unknown Interventions, Theorems 3.2 and 3.4 and Section 7 (vonKugelgenEtAl2023UnknownInterventions; https://papers.nips.cc/paper_files/paper/2023/file/97fe251c25b6f99a2a23b330a75b11d4-Paper-Conference.pdf): Theorem 3.2 is bivariate with one unknown-target perfect intervention per node and a continuous witness genericity condition; Theorem 3.4 uses two paired perfect interventions per node in arbitrary dimension; the one-intervention extension for n greater than two is stated as a conjecture." ∧
  PositiveNormalizedSmoothMechanisms G θ ∧
  SharedDiffeomorphicMixing G θ W ∧
  (n ≠ 0 → latentCube n ≠ Set.univ) ∧
  (2 : ℕ) ≠ 1

/-- Relative to Wendong et al. (2023) and Yao et al. (2025), the graph, topological order, and
environment-to-coordinate alignment are outputs computed from the observed laws, rather than
supplied structural inputs. -/
def WendongYaoSuppliedStructureComparison
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (W : ObservedWorld G θ) : Prop :=
  let laws := observedProbabilityLawFamily W.law
  caucaComparatorScope =
      "Wendong et al. (2023), Causal Component Analysis, Definition 3.2, Theorem 4.2, and Appendix E.2 (WendongEtAl2023CauCA; https://papers.nips.cc/paper_files/paper/2023/file/67089958e98b243d5cc1881ad60418b8-Paper-Conference.pdf): the graph G is assumed known, intervention targets are observed and fixed across candidate models, and one perfect stochastic intervention per node, each satisfying Assumption 4.1, gives identification up to componentwise scaling." ∧
  yaoComparatorScope =
      "Yao et al. (2025), Unifying Causal Representation Learning with the Invariance Principle, Assumption D.1, Corollary D.1, and the immediately following remark (YaoEtAl2025InvariancePrinciple; arXiv:2409.02772v2; https://arxiv.org/abs/2409.02772v2): exactly one imperfect intervention is supplied per node, the target labels preserve a supplied topological order, componentwise identification follows from marginal and score invariances, and identifying the order is explicitly treated as a separate subproblem." ∧
  IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law)
      (selectedTopologicalOrder laws) ∧
  (populationDecoder laws).2.2.edge = permutedGraph G W ∧
  (∀ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i, environmentParentSet W i ⊆ predecessorSet order i) ∧
  ∀ i v, v ∈ latentCube n →
    (observedLawRankCoordinate laws (selectedTopologicalOrder laws) i (W.mix v) : ℝ) =
      if s.value (W.targetPerm i) = 1
      then interventionCDF θ (W.targetPerm i) (v (W.targetPerm i))
      else 1 - interventionCDF θ (W.targetPerm i) (v (W.targetPerm i))

/-- Formal scope/comparison payload: the frozen von-Kügelgen intervention-count and
noncoverage clauses, recovery of the structure supplied by Wendong/Yao, and the bivariate MMD
witness. -/
def ExactRatioDecoderComparisonClauses
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
  (θ : Mechanism n G) (W : ObservedWorld G θ) : Prop :=
  VonKugelgenTwoVersusOneComparison s θ W ∧
  FullRnC1NoncoverageClause θ W ∧
  WendongYaoSuppliedStructureComparison s θ W ∧
  (n = 2 → ∀ ⦃j i⦄, G.edge j i →
    0 < observedLawDiscrepancy gaussianFeatureMap W.law
      (W.targetPerm.symm j) (W.targetPerm.symm i))

/-- All mathematical conclusions of the exact population decoder theorem. -/
def ExactRatioDecoderConclusion
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (W : ObservedWorld G θ) : Prop :=
  let laws := observedProbabilityLawFamily W.law
  Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) =
      Relation.TransGen (permutedGraph G W) ∧
  IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law)
      (selectedTopologicalOrder laws) ∧
  (∀ order, IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i,
      IsContinuousConditionalRatioCDFVersion laws order i
        (observedConditionalRatioCDF laws order i) ∧
      (∃ C, IsContinuousConditionalRatioCDFVersion laws order i C ∧
        ∀ t v, v ∈ latentCube n →
          (C t (familyProjection (observedLawLogRatio W.law)
              (predecessorSet order i) (W.mix v)) : ℝ) =
            equationElevenConditionalRatioCDF θ (W.targetPerm i) t v) ∧
      (∀ C, IsContinuousConditionalRatioCDFVersion laws order i C →
        ∀ z ∈ observedConditionalRatioSupport W.law order i,
          C z.1 z.2 = observedConditionalRatioCDF laws order i z.1 z.2) ∧
      (∀ t v, v ∈ latentCube n →
        (observedConditionalRatioCDF laws order i t
            (familyProjection (observedLawLogRatio W.law)
              (predecessorSet order i) (W.mix v)) : ℝ) =
          equationElevenConditionalRatioCDF θ (W.targetPerm i) t v) ∧
      ∀ v, v ∈ latentCube n →
        (observedLawRankCoordinate laws order i (W.mix v) : ℝ) =
          if s.value (W.targetPerm i) = 1
          then interventionCDF θ (W.targetPerm i) (v (W.targetPerm i))
          else 1 - interventionCDF θ (W.targetPerm i) (v (W.targetPerm i))) ∧
  (∀ order, IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i, environmentParentSet W i ⊆ predecessorSet order i) ∧
  (∀ order, IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i A, A ⊆ predecessorSet order i →
      (CondIndepGiven (W.law 0) (observedLawRankCoordinate laws order i)
        (familyProjection (observedLawRankCoordinate laws order)
          (predecessorSet order i \ A))
        (familyProjection (observedLawRankCoordinate laws order) A) ↔
      environmentParentSet W i ⊆ A)) ∧
  (∀ order, IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order →
    ∀ i, MinimalAdmissibleParentSet laws order i (environmentParentSet W i) ∧
      ∀ A, MinimalAdmissibleParentSet laws order i A →
        A = environmentParentSet W i) ∧
  ObservedWorldLawCoherent W ∧
  (populationDecoder laws).2.2.edge = permutedGraph G W ∧
  (∀ (G' : DAG (Fin n)) (θ' : Mechanism n G')
      (W' : ObservedWorld G' θ'),
    PositiveNormalizedSmoothMechanisms G' θ' →
    CausalMinimality G' θ' →
    FixedOwnDerivativeSign G' s θ' →
    SharedDiffeomorphicMixing G' θ' W' →
    OnePerfectInterventionPerNode G' θ' W' →
    W'.law = W.law → ComponentwiseC2Equivalent W W') ∧
  (n = 2 → ∀ ⦃j i⦄, G.edge j i →
    0 < observedLawDiscrepancy gaussianFeatureMap W.law
      (W.targetPerm.symm j) (W.targetPerm.symm i)) ∧
  ExactRatioDecoderComparisonClauses s θ W

/-- The formal comparator payload follows from exact graph recovery, representation uniqueness,
the bivariate edge witness, and predecessor containment; target uniqueness is supplied by the
world's target permutation.  Given [the stated inputs and conditions](hyp:hpos,hmix,hgraph,hunique,hbiv,hpred,horder,hrank), [the stated conclusion](goal) follows. -/
lemma exactRatioDecoderComparisonClauses_of_mainConclusions
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hgraph : (populationDecoder (observedProbabilityLawFamily W.law)).2.2.edge =
      permutedGraph G W)
    (hunique : ∀ (G' : DAG (Fin n)) (θ' : Mechanism n G')
        (W' : ObservedWorld G' θ'),
      PositiveNormalizedSmoothMechanisms G' θ' → CausalMinimality G' θ' →
      FixedOwnDerivativeSign G' s θ' → SharedDiffeomorphicMixing G' θ' W' →
      OnePerfectInterventionPerNode G' θ' W' → W'.law = W.law →
      ComponentwiseC2Equivalent W W')
    (hbiv : n = 2 → ∀ ⦃j i⦄, G.edge j i →
      0 < observedLawDiscrepancy gaussianFeatureMap W.law
        (W.targetPerm.symm j) (W.targetPerm.symm i))
    (hpred : ∀ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order →
      ∀ i, environmentParentSet W i ⊆ predecessorSet order i)
    (horder : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law)
      (selectedTopologicalOrder (observedProbabilityLawFamily W.law)))
    (hrank : ∀ i v, v ∈ latentCube n →
      (observedLawRankCoordinate (observedProbabilityLawFamily W.law)
          (selectedTopologicalOrder (observedProbabilityLawFamily W.law)) i (W.mix v) : ℝ) =
        if s.value (W.targetPerm i) = 1
        then interventionCDF θ (W.targetPerm i) (v (W.targetPerm i))
        else 1 - interventionCDF θ (W.targetPerm i) (v (W.targetPerm i))) :
    ExactRatioDecoderComparisonClauses s θ W := by
  refine ⟨?_, ?_, ⟨rfl, rfl, horder, hgraph, hpred, hrank⟩, hbiv⟩
  · refine ⟨rfl, ?_⟩
    intro _hfaith
    refine ⟨?_, by norm_num, hunique⟩
    intro i
    refine ⟨W.targetPerm.symm i, W.targetPerm.apply_symm_apply i, ?_⟩
    intro e he
    exact W.targetPerm.injective (he.trans (W.targetPerm.apply_symm_apply i).symm)
  · refine ⟨rfl, hpos, hmix, ?_, by norm_num⟩
    intro hn hcube
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let v : LatentState n := fun _ ↦ 2
    have hv : v ∈ latentCube n := by
      rw [hcube]
      exact Set.mem_univ v
    let i : Fin n := ⟨0, hnpos⟩
    have hi := hv i (Set.mem_univ i)
    norm_num at hi

-- @node: thm:exact-ratio-decoder
/-- Cover-separated positive smooth causal-minimal mechanisms are decoded exactly from their
observed environment laws, up to relabeling and componentwise `C²` diffeomorphisms.  Given [the stated inputs and conditions](hyp:hpos,hminimal,hmix,hone,hsign,hcover,world), [the stated conclusion](goal) follows. -/
theorem exact_ratio_decoder
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (world : ∀ θ' : Mechanism n G, ObservedWorld G θ')
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hminimal : CausalMinimality G θ)
    (hmix : SharedDiffeomorphicMixing G θ (world θ))
    (hone : OnePerfectInterventionPerNode G θ (world θ))
    (hsign : FixedOwnDerivativeSign G s θ)
    (hcover : (⟨θ, ⟨hpos, hminimal, hsign⟩⟩ : StratumPoint G s) ∈
      coverSeparatedSet (s := s) gaussianFeatureMap (world θ).targetPerm) :
    ExactRatioDecoderConclusion s θ (world θ) := by
  have hcoherent : ObservedWorldLawCoherent (world θ) :=
    observedWorldLawCoherent_of_assumptions (world θ) hpos hmix hone
  have _hratio : ∀ i v, v ∈ latentCube n →
      observedLawLogRatio (world θ).law i ((world θ).mix v) =
        Real.log
          (θ.q ((world θ).targetPerm i) (v ((world θ).targetPerm i)) /
            θ.p ((world θ).targetPerm i) v) := fun i =>
    observedLawLogRatio_comp_mix_eq (world θ) hpos hmix hone i
  have hcoverCanonical : ∀ ⦃a b : Fin n⦄, ancestralCover G a b →
      0 < populationDiscrepancy gaussianFeatureMap
        (canonicalObservedWorld G θ (world θ).targetPerm)
        ((world θ).targetPerm.symm a) ((world θ).targetPerm.symm b) := by
    simpa only [coverSeparatedSet, Set.mem_setOf_eq] using hcover
  have hcoverWorld := canonical_coverDiscrepancy_to_supplied gaussianFeatureMap
    (world θ) hpos hmix hone hcoverCanonical
  have hgraph := ratioGraph_reconstruction_order_and_predecessors
    (s := s) (world θ) hpos hmix hone hcoverWorld
  have _htriangularInverse : ∀ order,
      IsTopologicalOrdering
          (observedLawRatioGraph gaussianFeatureMap (world θ).law) order →
        ∀ i, PredecessorLatentCube order i ≃ₜ
          Set.range (predecessorScoreMap (world θ) order i) := by
    intro order horder i
    exact predecessorScoreHomeomorph s (world θ) hpos hmix hone hsign
      horder (permutedGraphOrdered_of_transitiveClosure
        (world θ) order horder hgraph.1) i
  have _hequationTenDensity : ∀ order,
      IsTopologicalOrdering
          (observedLawRatioGraph gaussianFeatureMap (world θ).law) order →
        ∀ i,
          let B := mechanismUnitCubeFactorization hpos
          let q := mechanismInterventionDensity (world θ) hpos i
          let A := decoderRetainedLatentSet (world θ) order i
          (∫⋯∫⁻_(Finset.univ \ A),
              B.interventionDensity ((world θ).targetPerm i) q
              ∂fun _ : Fin n =>
                Causalean.Graph.FiniteDensity.unitIntervalReference) =
            fun v => q.density (v ((world θ).targetPerm i)) *
              B.partialDensity (A.erase ((world θ).targetPerm i)) v := by
    intro order horder i
    exact equationTen_interventionMarginalDensity (world θ) hpos horder
      (permutedGraphOrdered_of_transitiveClosure (world θ) order horder hgraph.1) i
  have _hequationTenFiberProduct : ∀ order,
      IsTopologicalOrdering
          (observedLawRatioGraph gaussianFeatureMap (world θ).law) order →
        ∀ i (v : LatentState n) (w : ℝ),
          let B := mechanismUnitCubeFactorization hpos
          let q := mechanismInterventionDensity (world θ) hpos i
          let A := decoderRetainedLatentSet (world θ) order i
          (∫⋯∫⁻_(Finset.univ \ A),
              B.interventionDensity ((world θ).targetPerm i) q
              ∂fun _ : Fin n ↦
                Causalean.Graph.FiniteDensity.unitIntervalReference)
              (Function.update v ((world θ).targetPerm i) w) =
            q.density w *
              B.partialDensity (A.erase ((world θ).targetPerm i)) v := by
    intro order horder i v w
    exact equationTen_interventionMarginalDensity_fiber_product
      (world θ) hpos horder
        (permutedGraphOrdered_of_transitiveClosure (world θ) order horder hgraph.1) i v w
  have hcontinuousRankClauses := exactRatioDecoder_continuousRankClauses
    s (world θ) hpos hmix hone hsign hgraph.1
  have hbivariate : n = 2 → ∀ ⦃j i⦄, G.edge j i →
      0 < observedLawDiscrepancy gaussianFeatureMap (world θ).law
        ((world θ).targetPerm.symm j) ((world θ).targetPerm.symm i) := by
    intro hn
    subst n
    exact bivariate_edge_discrepancy_pos_of_coverSeparated (world θ) hcoverWorld
  have hprob : ∀ e, IsProbabilityMeasure ((world θ).law e) :=
    observedWorld_laws_isProbabilityMeasure (world θ) hpos hmix hone
  let laws := observedProbabilityLawFamily (world θ).law
  have hlaws : laws.1 = (world θ).law := by
    simp [laws, observedProbabilityLawFamily, hprob]
  have hiff : ∀ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap (world θ).law) order →
      ∀ i A, A ⊆ predecessorSet order i →
        (CondIndepGiven ((world θ).law 0) (observedLawRankCoordinate laws order i)
          (familyProjection (observedLawRankCoordinate laws order)
            (predecessorSet order i \ A))
          (familyProjection (observedLawRankCoordinate laws order) A) ↔
        environmentParentSet (world θ) i ⊆ A) := by
    intro order horder i A hA
    have hrank : ∀ e v, v ∈ latentCube n →
        (observedLawRankCoordinate laws order e ((world θ).mix v) : ℝ) =
          signedInterventionCDF s θ ((world θ).targetPerm e)
            (v ((world θ).targetPerm e)) := by
      intro e v hv
      simpa only [laws, signedInterventionCDF] using
        (hcontinuousRankClauses order horder e).2.2.2.2 v hv
    exact exactRankCondIndepCharacterization s (world θ) hpos hminimal hmix hone
      laws hgraph.1 order horder hrank i A hA
  have hprune : ∀ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap (world θ).law) order →
      ∀ i, MinimalAdmissibleParentSet laws order i (environmentParentSet (world θ) i) ∧
        ∀ A, MinimalAdmissibleParentSet laws order i A →
          A = environmentParentSet (world θ) i := by
    have hp := exactParentPruning_of_condIndepCharacterization (world θ) laws
      (by simpa only [hlaws] using hgraph.2.2)
      (by simpa only [hlaws] using hiff)
    simpa only [hlaws] using hp
  have hselected : (populationDecoder laws).2.2.edge = permutedGraph G (world θ) :=
    selectedParentDAG_eq_permutedGraph_of_exactPruning (world θ) laws
      (hprune (selectedTopologicalOrder laws) hgraph.2.1)
  have hunique : ∀ (G' : DAG (Fin n)) (θ' : Mechanism n G')
      (W' : ObservedWorld G' θ'),
      PositiveNormalizedSmoothMechanisms G' θ' →
      CausalMinimality G' θ' →
      FixedOwnDerivativeSign G' s θ' →
      SharedDiffeomorphicMixing G' θ' W' →
      OnePerfectInterventionPerNode G' θ' W' →
      W'.law = (world θ).law → ComponentwiseC2Equivalent (world θ) W' := by
    intro G' θ' W' hpos' hminimal' hsign' hmix' hone' hlaw'
    let order : Fin n → ℕ := fun e ↦ G'.topoOrder (W'.targetPerm e)
    have hcommon := competitorTopologicalOrder_is_common_of_law_eq
      (s := s) (world θ) W' hpos' hmix' hone' hlaw' hgraph.1
    have horder : IsTopologicalOrdering
        (observedLawRatioGraph gaussianFeatureMap (world θ).law) order := hcommon.1
    have horder' : IsTopologicalOrdering
        (observedLawRatioGraph gaussianFeatureMap W'.law) order := by
      simpa only [hlaw'] using horder
    have hgraphOrder : PermutedGraphOrdered (world θ) order := hcommon.2.1
    have hgraphOrder' : PermutedGraphOrdered W' order := hcommon.2.2.1
    have hrank : ∀ e v, v ∈ latentCube n →
        (observedLawRankCoordinate laws order e ((world θ).mix v) : ℝ) =
          signedInterventionCDF s θ ((world θ).targetPerm e)
            (v ((world θ).targetPerm e)) := by
      intro e v hv
      simpa only [laws, signedInterventionCDF] using
        (exactRatioDecoder_continuousRankClauses_of_order s (world θ)
          hpos hmix hone hsign order horder hgraphOrder e).2.2.2.2 v hv
    have hrank' : ∀ e v, v ∈ latentCube n →
        (observedLawRankCoordinate laws order e (W'.mix v) : ℝ) =
          signedInterventionCDF s θ' (W'.targetPerm e) (v (W'.targetPerm e)) := by
      intro e v hv
      simpa only [laws, hlaw', signedInterventionCDF] using
        (exactRatioDecoder_continuousRankClauses_of_order s W'
          hpos' hmix' hone' hsign' order horder' hgraphOrder' e).2.2.2.2 v hv
    have hiff' := exactRankCondIndepCharacterization_of_order s W'
      hpos' hminimal' hmix' hone' laws order horder' hgraphOrder' hrank'
    have hprune' : ∀ i,
        MinimalAdmissibleParentSet laws order i (environmentParentSet W' i) ∧
          ∀ A, MinimalAdmissibleParentSet laws order i A →
            A = environmentParentSet W' i := by
      apply exactParentPruning_at_order W' laws order hcommon.2.2.2.2
      intro i A hA
      simpa only [hlaws, hlaw'] using hiff' i A hA
    have hpruneMain := hprune order horder
    have hparents : ∀ i, environmentParentSet W' i = environmentParentSet (world θ) i := by
      intro i
      exact (hpruneMain i).2 _ (hprune' i).1
    have hedge : ∀ j i,
        G'.edge (((world θ).targetPerm.symm.trans W'.targetPerm) j)
            (((world θ).targetPerm.symm.trans W'.targetPerm) i) ↔
          G.edge j i := by
      intro j i
      have hm := congrArg
        (fun A : Finset (Fin n) => (world θ).targetPerm.symm j ∈ A)
        (hparents ((world θ).targetPerm.symm i))
      simpa [environmentParentSet] using hm
    have hsupport := observedSupport_eq_of_observationalLaw_eq (world θ) W'
      hpos hmix hone hpos' hmix' hone' hlaw'
    exact componentwiseC2Equivalent_of_common_rank_and_aligned_edges
      (world θ) W' hpos hmix hpos' hmix' laws order hrank hrank' hsupport hedge
  refine ⟨hgraph.1, hgraph.2.1, hcontinuousRankClauses, hgraph.2.2,
    hiff, hprune, hcoherent, hselected, hunique, hbivariate, ?_⟩
  exact exactRatioDecoderComparisonClauses_of_mainConclusions s (world θ)
    hpos hmix hselected hunique hbivariate hgraph.2.2 hgraph.2.1
    (fun i => (hcontinuousRankClauses
      (selectedTopologicalOrder laws) hgraph.2.1 i).2.2.2.2)

/-- Faithful-overlap corollary; faithfulness is deliberately not a premise of the main theorem.  Given [the stated inputs and conditions](hyp:hpos,hminimal,hmix,hone,hsign,hfaith,hcover,world), [the stated conclusion](goal) follows. -/
-- keep: explicit faithful-overlap corollary stated in the paper's scope comparison
theorem exact_ratio_decoder_faithful
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (world : ∀ θ' : Mechanism n G, ObservedWorld G θ')
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hminimal : CausalMinimality G θ)
    (hmix : SharedDiffeomorphicMixing G θ (world θ))
    (hone : OnePerfectInterventionPerNode G θ (world θ))
    (hsign : FixedOwnDerivativeSign G s θ)
    (hfaith : Faithfulness G θ)
    (hcover : (⟨θ, ⟨hpos, hminimal, hsign⟩⟩ : StratumPoint G s) ∈
      coverSeparatedSet (s := s) gaussianFeatureMap (world θ).targetPerm) :
    ExactRatioDecoderConclusion s θ (world θ) := by
  exact exact_ratio_decoder s θ world hpos hminimal hmix hone hsign hcover

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
