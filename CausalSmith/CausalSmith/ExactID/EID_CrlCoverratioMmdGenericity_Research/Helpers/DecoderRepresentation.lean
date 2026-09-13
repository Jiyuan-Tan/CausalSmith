import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderPruning
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderCore
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderRankAssembly

/-!
# Compatible-representation bookkeeping

These lemmas isolate the law-support and graph-relabeling parts of the compatible-
representation argument.  The remaining analytic step is the componentwise coordinate
identification from the common law-selected ranks.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- The scalar rank chart selected by an intervention CDF and the prescribed ratio-score sign. -/
def signedInterventionCDF
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (i : Fin n) (z : ℝ) : ℝ :=
  if s.value i = 1 then interventionCDF θ i z else 1 - interventionCDF θ i z

-- @node: interventionCDF_strictMonoOn
/-- Strict positivity of the intervention density makes its CDF strictly increasing on the
latent interval.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma interventionCDF_strictMonoOn
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G)
    (hpos : PositiveNormalizedSmoothMechanisms G θ) (i : Fin n) :
    StrictMonoOn (interventionCDF θ i) (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hcont : ContinuousOn (θ.q i) (Set.Icc (0 : ℝ) 1) :=
    (hpos.2.2.2.1 i).continuousOn
  have hcont₀a : ContinuousOn (θ.q i) (Set.uIcc (0 : ℝ) a) := by
    apply hcont.mono
    rw [Set.uIcc_of_le ha.1]
    exact Set.Icc_subset_Icc le_rfl ha.2
  have hcontab : ContinuousOn (θ.q i) (Set.uIcc a b) := by
    apply hcont.mono
    rw [Set.uIcc_of_le hab.le]
    exact Set.Icc_subset_Icc ha.1 hb.2
  have hintpos : 0 < ∫ z in a..b, θ.q i z := by
    apply intervalIntegral.integral_pos hab
    · simpa only [Set.uIcc_of_le hab.le] using hcontab
    · intro z hz
      exact (hpos.2.1 i z ⟨ha.1.trans hz.1.le, hz.2.trans hb.2⟩).le
    · exact ⟨a, ⟨le_rfl, hab.le⟩, hpos.2.1 i a ha⟩
  have hadd : (∫ z in (0 : ℝ)..a, θ.q i z) + ∫ z in a..b, θ.q i z =
      ∫ z in (0 : ℝ)..b, θ.q i z :=
    intervalIntegral.integral_add_adjacent_intervals
      hcont₀a.intervalIntegrable hcontab.intervalIntegrable
  unfold interventionCDF
  linarith

-- @node: signedInterventionCDF_injOn
/-- Reflection for a negative score sign preserves injectivity of the scalar intervention-CDF
chart.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma signedInterventionCDF_injOn
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ) (i : Fin n) :
    Set.InjOn (signedInterventionCDF s θ i) (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb heq
  have hinj := (interventionCDF_strictMonoOn θ hpos i).injOn
  unfold signedInterventionCDF at heq
  split at heq
  · exact hinj ha hb heq
  · apply hinj ha hb
    linarith

-- @node: observedProbabilityLawFamily_eq_of_law_eq
/-- The probability-family packaging, selected order, and rank coordinates are literally shared
by representations whose supplied law families are equal.  Given [the stated inputs and conditions](hyp:hlaw), [the stated conclusion](goal) follows. -/
lemma observedProbabilityLawFamily_eq_of_law_eq
    {n : ℕ} {G₁ G₂ : Causalean.DAG (Fin n)}
    {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂)
    (hlaw : W₂.law = W₁.law) :
    observedProbabilityLawFamily W₂.law = observedProbabilityLawFamily W₁.law := by
  rw [hlaw]

-- @node: observedSupport_eq_of_observationalLaw_eq
/-- Compatible smooth observed worlds with the same observational law have the same observed
support.  Given [the stated inputs and conditions](hyp:hpos₁,hmix₁,hone₁,hpos₂,hmix₂,hone₂,hlaw), [the stated conclusion](goal) follows. -/
lemma observedSupport_eq_of_observationalLaw_eq
    {n : ℕ} {G₁ G₂ : Causalean.DAG (Fin n)}
    {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂)
    (hpos₁ : PositiveNormalizedSmoothMechanisms G₁ θ₁)
    (hmix₁ : SharedDiffeomorphicMixing G₁ θ₁ W₁)
    (hone₁ : OnePerfectInterventionPerNode G₁ θ₁ W₁)
    (hpos₂ : PositiveNormalizedSmoothMechanisms G₂ θ₂)
    (hmix₂ : SharedDiffeomorphicMixing G₂ θ₂ W₂)
    (hone₂ : OnePerfectInterventionPerNode G₂ θ₂ W₂)
    (hlaw : W₂.law = W₁.law) :
    observedSupport G₁ W₁ = observedSupport G₂ W₂ := by
  rw [← observedLaw_support_eq_observedSupport W₁ hpos₁ hmix₁ hone₁,
    ← observedLaw_support_eq_observedSupport W₂ hpos₂ hmix₂ hone₂,
    hlaw]

-- @node: aligned_edge_iff_of_permutedGraph_eq
/-- Equality of environment-label graphs gives graph isomorphism under the intervention-target
alignment permutation.  Given [the stated inputs and conditions](hyp:hgraph), [the stated conclusion](goal) follows. -/
lemma aligned_edge_iff_of_permutedGraph_eq
    {n : ℕ} {G₁ G₂ : Causalean.DAG (Fin n)}
    {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂)
    (hgraph : permutedGraph G₁ W₁ = permutedGraph G₂ W₂) :
    ∀ j i,
      G₂.edge ((W₁.targetPerm.symm.trans W₂.targetPerm) j)
          ((W₁.targetPerm.symm.trans W₂.targetPerm) i) ↔
        G₁.edge j i := by
  intro j i
  have h := congrFun (congrFun hgraph (W₁.targetPerm.symm j))
    (W₁.targetPerm.symm i)
  simpa [permutedGraph] using h.symm

-- @node: aligned_edge_iff_of_common_exactPruning
/-- If law-only exact pruning identifies both representations' parent relations, their latent
graphs align by the target permutation.  Given [the stated inputs and conditions](hyp:hprune₁,hprune₂), [the stated conclusion](goal) follows. -/
lemma aligned_edge_iff_of_common_exactPruning
    {n : ℕ} {G₁ G₂ : Causalean.DAG (Fin n)}
    {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂)
    (laws : ObservedProbabilityLawFamily n)
    (hprune₁ : ∀ i,
      MinimalAdmissibleParentSet laws (selectedTopologicalOrder laws) i
          (environmentParentSet W₁ i) ∧
        ∀ A, MinimalAdmissibleParentSet laws (selectedTopologicalOrder laws) i A →
          A = environmentParentSet W₁ i)
    (hprune₂ : ∀ i,
      MinimalAdmissibleParentSet laws (selectedTopologicalOrder laws) i
          (environmentParentSet W₂ i) ∧
        ∀ A, MinimalAdmissibleParentSet laws (selectedTopologicalOrder laws) i A →
          A = environmentParentSet W₂ i) :
    ∀ j i,
      G₂.edge ((W₁.targetPerm.symm.trans W₂.targetPerm) j)
          ((W₁.targetPerm.symm.trans W₂.targetPerm) i) ↔
        G₁.edge j i := by
  apply aligned_edge_iff_of_permutedGraph_eq W₁ W₂
  rw [← selectedParentDAG_eq_permutedGraph_of_exactPruning W₁ laws hprune₁,
    ← selectedParentDAG_eq_permutedGraph_of_exactPruning W₂ laws hprune₂]

-- @node: competitorTopologicalOrder_is_common_of_law_eq
/-- A topological order pulled back from a compatible competitor orders the common observable
ratio graph and, once the reference transitive closure is identified, the reference graph too.
No cover-separation premise is required for the competitor.  Given [the stated inputs and conditions](hyp:hpos₂,hmix₂,hone₂,hlaw,htc₁), [the stated conclusion](goal) follows. -/
lemma competitorTopologicalOrder_is_common_of_law_eq
    {n : ℕ} {G₁ G₂ : Causalean.DAG (Fin n)}
    {s : SignVector n} {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂)
    (hpos₂ : PositiveNormalizedSmoothMechanisms G₂ θ₂)
    (hmix₂ : SharedDiffeomorphicMixing G₂ θ₂ W₂)
    (hone₂ : OnePerfectInterventionPerNode G₂ θ₂ W₂)
    (hlaw : W₂.law = W₁.law)
    (htc₁ : Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W₁.law) =
      Relation.TransGen (permutedGraph G₁ W₁)) :
    let order : Fin n → ℕ := fun e ↦ G₂.topoOrder (W₂.targetPerm e)
    IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W₁.law) order ∧
      (∀ ⦃j i⦄, permutedGraph G₁ W₁ j i → order j < order i) ∧
      (∀ ⦃j i⦄, permutedGraph G₂ W₂ j i → order j < order i) ∧
      (∀ i, environmentParentSet W₁ i ⊆ predecessorSet order i) ∧
      (∀ i, environmentParentSet W₂ i ⊆ predecessorSet order i) := by
  let order : Fin n → ℕ := fun e ↦ G₂.topoOrder (W₂.targetPerm e)
  have hinj : Function.Injective order :=
    G₂.topoOrder_injective.comp W₂.targetPerm.injective
  have hratio : ∀ ⦃j i⦄,
      observedLawRatioGraph gaussianFeatureMap W₁.law j i → order j < order i := by
    intro j i hji
    have hji₂ : observedLawRatioGraph gaussianFeatureMap W₂.law j i := by
      simpa only [hlaw] using hji
    exact G₂.isAncestor_topoOrder_lt
      (observedLawRatioGraph_edge_isAncestor (s := s) W₂ hpos₂ hmix₂ hone₂ hji₂)
  have hpath : ∀ ⦃j i⦄,
      Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W₁.law) j i →
        order j < order i := by
    intro j i hji
    induction hji with
    | single h => exact hratio h
    | tail _ h ih => exact lt_trans ih (hratio h)
  have hedge₁ : ∀ ⦃j i⦄, permutedGraph G₁ W₁ j i → order j < order i := by
    intro j i hji
    apply hpath
    rw [htc₁]
    exact Relation.TransGen.single hji
  have hedge₂ : ∀ ⦃j i⦄, permutedGraph G₂ W₂ j i → order j < order i := by
    intro j i hji
    exact G₂.isAncestor_topoOrder_lt (Causalean.DAG.isAncestor.edge hji)
  refine ⟨⟨hinj, hratio⟩, hedge₁, hedge₂, ?_, ?_⟩
  · intro j i hji
    simpa [predecessorSet, order] using hedge₁ (by
      simpa [environmentParentSet, permutedGraph] using hji)
  · intro j i hji
    simpa [predecessorSet, order] using hedge₂ (by
      simpa [environmentParentSet, permutedGraph] using hji)

-- @node: signedInterventionCDF_eq_of_common_rank
/-- Two representations realizing the same law-only rank coordinate have equal signed scalar
intervention-CDF coordinates at every common support point.  Given [the stated inputs and conditions](hyp:hmix₁,hmix₂,hrank₁,hrank₂,hx₁,hx₂), [the stated conclusion](goal) follows. -/
lemma signedInterventionCDF_eq_of_common_rank
    {n : ℕ} {G₁ G₂ : Causalean.DAG (Fin n)}
    {s : SignVector n} {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂)
    (hmix₁ : SharedDiffeomorphicMixing G₁ θ₁ W₁)
    (hmix₂ : SharedDiffeomorphicMixing G₂ θ₂ W₂)
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ)
    (hrank₁ : ∀ e v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order e (W₁.mix v) : ℝ) =
        signedInterventionCDF s θ₁ (W₁.targetPerm e) (v (W₁.targetPerm e)))
    (hrank₂ : ∀ e v, v ∈ latentCube n →
      (observedLawRankCoordinate laws order e (W₂.mix v) : ℝ) =
        signedInterventionCDF s θ₂ (W₂.targetPerm e) (v (W₂.targetPerm e)))
    (x : LatentState n) (hx₁ : x ∈ observedSupport G₁ W₁)
    (hx₂ : x ∈ observedSupport G₂ W₂) (e : Fin n) :
    signedInterventionCDF s θ₁ (W₁.targetPerm e)
        (W₁.unmix x (W₁.targetPerm e)) =
      signedInterventionCDF s θ₂ (W₂.targetPerm e)
        (W₂.unmix x (W₂.targetPerm e)) := by
  have hv₁ : W₁.unmix x ∈ latentCube n := by
    rcases hx₁ with ⟨v, hv, rfl⟩
    simpa only [hmix₁.2.2.1 v hv] using hv
  have hv₂ : W₂.unmix x ∈ latentCube n := by
    rcases hx₂ with ⟨v, hv, rfl⟩
    simpa only [hmix₂.2.2.1 v hv] using hv
  have h₁ := hrank₁ e (W₁.unmix x) hv₁
  have h₂ := hrank₂ e (W₂.unmix x) hv₂
  rw [hmix₁.2.2.2 x hx₁] at h₁
  rw [hmix₂.2.2.2 x hx₂] at h₂
  exact h₁.symm.trans h₂

-- @node: alignedCoordinate_eq_of_common_rank
/-- Equality of an aligned source coordinate forces equality of the competitor coordinate once
both worlds realize the common law-only rank.  This is the componentwise-dependence leaf of the
representation argument.  Given [the stated inputs and conditions](hyp:hmix₁,hpos₂,hmix₂,hrank₁,hrank₂,hx₁,hx₂,hy₁,hy₂,hcoord), [the stated conclusion](goal) follows. -/
lemma alignedCoordinate_eq_of_common_rank
    {n : ℕ} {G₁ G₂ : Causalean.DAG (Fin n)}
    {s : SignVector n} {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂)
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
    (x y : LatentState n)
    (hx₁ : x ∈ observedSupport G₁ W₁) (hx₂ : x ∈ observedSupport G₂ W₂)
    (hy₁ : y ∈ observedSupport G₁ W₁) (hy₂ : y ∈ observedSupport G₂ W₂)
    (e : Fin n)
    (hcoord : W₁.unmix x (W₁.targetPerm e) =
      W₁.unmix y (W₁.targetPerm e)) :
    W₂.unmix x (W₂.targetPerm e) = W₂.unmix y (W₂.targetPerm e) := by
  have hsx := signedInterventionCDF_eq_of_common_rank W₁ W₂ hmix₁ hmix₂
    laws order hrank₁ hrank₂ x hx₁ hx₂ e
  have hsy := signedInterventionCDF_eq_of_common_rank W₁ W₂ hmix₁ hmix₂
    laws order hrank₁ hrank₂ y hy₁ hy₂ e
  apply signedInterventionCDF_injOn s θ₂ hpos₂ (W₂.targetPerm e)
  · rcases hx₂ with ⟨v, hv, rfl⟩
    simpa only [hmix₂.2.2.1 v hv] using hv (W₂.targetPerm e) (Set.mem_univ _)
  · rcases hy₂ with ⟨v, hv, rfl⟩
    simpa only [hmix₂.2.2.1 v hv] using hv (W₂.targetPerm e) (Set.mem_univ _)
  · calc
      signedInterventionCDF s θ₂ (W₂.targetPerm e)
          (W₂.unmix x (W₂.targetPerm e)) =
          signedInterventionCDF s θ₁ (W₁.targetPerm e)
            (W₁.unmix x (W₁.targetPerm e)) := hsx.symm
      _ = signedInterventionCDF s θ₁ (W₁.targetPerm e)
            (W₁.unmix y (W₁.targetPerm e)) := congrArg _ hcoord
      _ = signedInterventionCDF s θ₂ (W₂.targetPerm e)
            (W₂.unmix y (W₂.targetPerm e)) := hsy

-- @node: signedInterventionCDF_eq_of_common_law_and_transitiveClosures
/-- Once the common law-selected order is known to be topological for both latent transitive
closures, the assembled equation-(11)--(12) rank formula identifies their signed scalar CDF
coordinates pointwise on the common support.  Given [the stated inputs and conditions](hyp:hpos₁,hmix₁,hone₁,hsign₁,hpos₂,hmix₂,hone₂,hsign₂,hlaw,htc₁,htc₂,horder,hx₁,hx₂), [the stated conclusion](goal) follows. -/
lemma signedInterventionCDF_eq_of_common_law_and_transitiveClosures
    {n : ℕ} {G₁ G₂ : Causalean.DAG (Fin n)}
    (s : SignVector n) {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
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
    (htc₂ : Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W₂.law) =
      Relation.TransGen (permutedGraph G₂ W₂))
    (order : Fin n → ℕ)
    (horder : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W₁.law) order)
    (x : LatentState n) (hx₁ : x ∈ observedSupport G₁ W₁)
    (hx₂ : x ∈ observedSupport G₂ W₂) (e : Fin n) :
    signedInterventionCDF s θ₁ (W₁.targetPerm e)
        (W₁.unmix x (W₁.targetPerm e)) =
      signedInterventionCDF s θ₂ (W₂.targetPerm e)
        (W₂.unmix x (W₂.targetPerm e)) := by
  let laws := observedProbabilityLawFamily W₁.law
  have horder₂ : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W₂.law) order := by
    simpa only [hlaw] using horder
  apply signedInterventionCDF_eq_of_common_rank W₁ W₂ hmix₁ hmix₂ laws order
      (fun e v hv ↦ ?_) (fun e v hv ↦ ?_) x hx₁ hx₂ e
  · simpa only [laws, signedInterventionCDF] using
      (exactRatioDecoder_continuousRankClauses s W₁ hpos₁ hmix₁ hone₁ hsign₁
        htc₁ order horder e).2.2.2.2 v hv
  · simpa only [laws, hlaw, signedInterventionCDF] using
      (exactRatioDecoder_continuousRankClauses s W₂ hpos₂ hmix₂ hone₂ hsign₂
        htc₂ order horder₂ e).2.2.2.2 v hv

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
