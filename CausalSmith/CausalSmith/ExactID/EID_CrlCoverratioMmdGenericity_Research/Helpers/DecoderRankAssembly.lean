import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderContinuousVersion
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderSupport

/-!
# Continuous conditional-rank assembly

This file assembles the support, continuous-version, explicit equation-(11),
and signed-rank facts into the complete conditional-rank clause consumed by
the exact population decoder theorem.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: exactRatioDecoder_continuousRankClauses_of_order
/-- A ratio-graph order that also respects the latent edges has the law-selected continuous
conditional CDF, its equation-(11) realization, and the signed intervention-CDF rank.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma exactRatioDecoder_continuousRankClauses_of_order
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    (order : Fin n → ℕ)
    (horder : IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) :
      ∀ i,
        let laws := observedProbabilityLawFamily W.law
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
            else 1 - interventionCDF θ (W.targetPerm i) (v (W.targetPerm i)) := by
  intro i
  let laws := observedProbabilityLawFamily W.law
  have hprob : ∀ e, IsProbabilityMeasure (W.law e) :=
    observedWorld_laws_isProbabilityMeasure W hpos hmix hone
  have hlaws : laws.1 = W.law := by
    simp [laws, observedProbabilityLawFamily, hprob]
  let C := equationElevenAmbientCDF s W hpos hmix hone hsign horder hgraphOrder i
  have hC : IsContinuousConditionalRatioCDFVersion laws order i C := by
    exact equationElevenAmbientCDF_isContinuousVersion
      s W hpos hmix hone hsign horder hgraphOrder i
  have hex : ∃ D, IsContinuousConditionalRatioCDFVersion laws order i D := ⟨C, hC⟩
  have hselected : IsContinuousConditionalRatioCDFVersion laws order i
      (observedConditionalRatioCDF laws order i) :=
    observedConditionalRatioCDF_isContinuousVersion laws order i hex
  have hC_apply : ∀ t v, v ∈ latentCube n →
      (C t (familyProjection (observedLawLogRatio W.law)
          (predecessorSet order i) (W.mix v)) : ℝ) =
        equationElevenConditionalRatioCDF θ (W.targetPerm i) t v := by
    intro t v hv
    exact equationElevenAmbientCDF_apply_of_latentState
      s W hpos hmix hone hsign horder hgraphOrder i t v hv
  have hselected_apply : ∀ t v, v ∈ latentCube n →
      (observedConditionalRatioCDF laws order i t
          (familyProjection (observedLawLogRatio W.law)
            (predecessorSet order i) (W.mix v)) : ℝ) =
        equationElevenConditionalRatioCDF θ (W.targetPerm i) t v := by
    intro t v hv
    let ell := familyProjection (observedLawLogRatio W.law)
      (predecessorSet order i) (W.mix v)
    have hz : (t, ell) ∈ observedConditionalRatioSupport laws.1 order i := by
      rw [hlaws]
      exact ⟨Set.mem_univ t,
        observedPredecessorLogRatio_mem_support W hpos hmix hone i v hv⟩
    have heq := observedConditionalRatioCDF_eq_on_support laws order i hex C hC
      (t, ell) hz
    calc
      (observedConditionalRatioCDF laws order i t ell : ℝ) = (C t ell : ℝ) :=
        congrArg Subtype.val heq.symm
      _ = equationElevenConditionalRatioCDF θ (W.targetPerm i) t v := hC_apply t v hv
  refine ⟨hselected, ⟨C, hC, hC_apply⟩, ?_, hselected_apply, ?_⟩
  · intro D hD
    simpa only [hlaws] using
      (observedConditionalRatioCDF_eq_on_support laws order i hex D hD)
  · have hselected_apply' : ∀ t v, v ∈ latentCube n →
        (observedConditionalRatioCDF laws order i t
            (familyProjection (observedLawLogRatio laws.1)
              (predecessorSet order i) (W.mix v)) : ℝ) =
          equationElevenConditionalRatioCDF θ (W.targetPerm i) t v := by
      simpa only [hlaws] using hselected_apply
    have hratio' : ∀ v, v ∈ latentCube n →
        observedLawLogRatio laws.1 i (W.mix v) =
          Real.log (θ.q (W.targetPerm i) (v (W.targetPerm i)) /
            θ.p (W.targetPerm i) v) := by
      simpa only [hlaws] using
        (observedLawLogRatio_comp_mix_eq W hpos hmix hone i)
    exact observedLawRankCoordinate_eq_of_equationEleven
      s θ W laws order hpos hsign i hselected_apply' hratio'

-- @node: exactRatioDecoder_continuousRankClauses
/-- Transitive-closure recovery supplies latent-edge compatibility for every valid ratio order.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,htc), [the stated conclusion](goal) follows. -/
lemma exactRatioDecoder_continuousRankClauses
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    (htc : Relation.TransGen (observedLawRatioGraph gaussianFeatureMap W.law) =
      Relation.TransGen (permutedGraph G W)) :
    ∀ order, IsTopologicalOrdering
        (observedLawRatioGraph gaussianFeatureMap W.law) order →
      ∀ i,
        let laws := observedProbabilityLawFamily W.law
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
            else 1 - interventionCDF θ (W.targetPerm i) (v (W.targetPerm i)) := by
  intro order horder
  exact exactRatioDecoder_continuousRankClauses_of_order s W hpos hmix hone hsign
    order horder (permutedGraphOrdered_of_transitiveClosure W order horder htc)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
