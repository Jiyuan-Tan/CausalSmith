import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderCore
import CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.Recovery

/-!
# Gaussian recovery bridge

This file connects the paper's duplicated explicit Gaussian feature expansion
and its canonical ratio laws to the neutral bounded-support recovery theorem.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

open Causalean.Graph.FiniteDensity

private lemma factorization_interventionMeasure_eq_withDensity_targetRatio
    {n : ℕ} {G : Causalean.DAG (Fin n)}
    (B : UnitCubeFactorization (Fin n) G) (i : Fin n)
    (q : InterventionDensity i (fun _ : Fin n => ℝ)
      (fun _ : Fin n => unitIntervalReference))
    (hzero : ∀ v, B.factor i v ≠ 0) (htop : ∀ v, B.factor i v ≠ ∞) :
    B.interventionMeasure i q = B.observationalMeasure.withDensity
      (fun v => q.density (v i) / B.factor i v) := by
  letI : SigmaFinite unitIntervalReference := by
    unfold unitIntervalReference
    infer_instance
  rw [Factorization.interventionMeasure, Factorization.observationalMeasure,
    ← withDensity_mul]
  · congr 1
    funext v
    unfold Factorization.interventionDensity Factorization.observationalDensity
      Factorization.partialDensity
    change q.density (v i) * (∏ x ∈ Finset.univ.erase i, B.factor x v) =
      (∏ x ∈ Finset.univ, B.factor x v) * (q.density (v i) / B.factor i v)
    conv_rhs =>
      rw [Finset.prod_eq_mul_prod_sdiff_singleton i _ (by simp)]
    simp only [Finset.sdiff_singleton_eq_erase]
    calc
      q.density (v i) * (∏ x ∈ Finset.univ.erase i, B.factor x v) =
          (B.factor i v * (q.density (v i) / B.factor i v)) *
            (∏ x ∈ Finset.univ.erase i, B.factor x v) := by
        rw [ENNReal.mul_div_cancel (hzero v) (htop v)]
      _ = (B.factor i v * (∏ x ∈ Finset.univ.erase i, B.factor x v)) *
          (q.density (v i) / B.factor i v) := by ac_rfl
  · exact B.measurable_observationalDensity
  · exact (q.measurable_density.comp (measurable_pi_apply i)).div
      (B.measurable_factor i)

/-- The identity-mixing canonical world satisfies the paper's perfect-intervention contract.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma canonicalObservedWorld_onePerfectInterventionPerNode
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) (π : Equiv.Perm (Fin n)) :
    OnePerfectInterventionPerNode G θ (canonicalObservedWorld G θ π) := by
  let W := canonicalObservedWorld G θ π
  let B := mechanismUnitCubeFactorization hpos
  constructor
  · simp [canonicalObservedWorld]
  constructor
  · intro e
    simp [canonicalObservedWorld]
  constructor
  · intro e
    let q := mechanismInterventionDensity W hpos e
    let r := fun v : LatentState n =>
      q.density (v (W.targetPerm e)) / B.factor (W.targetPerm e) v
    have hfactor_zero : ∀ v, B.factor (W.targetPerm e) v ≠ 0 := by
      intro v
      change ENNReal.ofReal (θ.p (W.targetPerm e) (clampCube (Fin n) v)) ≠ 0
      exact (ENNReal.ofReal_pos.mpr (hpos.1 _ _ (by
        simpa only [latentCube, unitCube] using clampCube_mem (Fin n) v))).ne'
    have hfactor_top : ∀ v, B.factor (W.targetPerm e) v ≠ ∞ := by
      intro v
      change ENNReal.ofReal (θ.p (W.targetPerm e) (clampCube (Fin n) v)) ≠ ∞
      exact ENNReal.ofReal_ne_top
    have hmeasure : interventionalLaw θ (W.targetPerm e) =
        (observationalLaw θ).withDensity r := by
      rw [← mechanismUnitCubeFactorization_interventionMeasure W hpos e,
        ← mechanismUnitCubeFactorization_observationalMeasure hpos]
      exact factorization_interventionMeasure_eq_withDensity_targetRatio B
        (W.targetPerm e) q hfactor_zero hfactor_top
    have hrn :
        (interventionalLaw θ (W.targetPerm e)).rnDeriv (observationalLaw θ) =ᵐ[
          observationalLaw θ] r := by
      letI : IsProbabilityMeasure (observationalLaw θ) :=
        observationalLaw_isProbabilityMeasure hpos
      rw [hmeasure]
      exact Measure.rnDeriv_withDensity _
        ((q.measurable_density.comp (measurable_pi_apply (W.targetPerm e))).div
          (B.measurable_factor (W.targetPerm e)))
    filter_upwards [hrn, observationalLaw_ae_mem_latentCube hpos] with v hrv hv
    change ENNReal.ofReal
        (θ.q (π e) (v (π e)) / θ.p (π e) v) =
      (interventionalLaw θ (π e)).rnDeriv (observationalLaw θ) v
    have hrtop : r v ≠ ∞ :=
      ENNReal.div_ne_top (by
        dsimp only [r, q, mechanismInterventionDensity, mechanismRatioNumerator]
        exact ENNReal.ofReal_ne_top) (hfactor_zero v)
    have hratio : (r v).toReal =
        θ.q (π e) (v (π e)) / θ.p (π e) v := by
      simpa only [r, q, B, W, mechanismRatioNumerator, canonicalObservedWorld] using
        mechanismTargetRatio_toReal_eq W hpos e hv
    calc
      ENNReal.ofReal (θ.q (π e) (v (π e)) / θ.p (π e) v) =
          ENNReal.ofReal (r v).toReal := by
        rw [hratio]
      _ = r v := ENNReal.ofReal_toReal hrtop
      _ = _ := hrv.symm
  · intro e v hv
    rfl

/-- The paper and neutral Gaussian feature vectors are the same explicit `ℓ²` vector.  [the stated conclusion](goal) follows. -/
lemma gaussianFeature_eq_recovery (r : ℝ) :
    gaussianFeature r =
      CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.gaussianFeature r := by
  apply Subtype.ext
  funext m
  rfl

/-- The paper's Gaussian mean embedding agrees with the neutral recovery embedding.  [the stated conclusion](goal) follows. -/
lemma meanEmbedding_gaussianFeatureMap_eq_recovery (μ : Measure ℝ) :
    meanEmbedding gaussianFeatureMap μ =
      CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.meanEmbedding
        CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.gaussianFeatureMap μ := by
  unfold meanEmbedding
    CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.meanEmbedding
  apply integral_congr_ae
  filter_upwards with r
  exact gaussianFeature_eq_recovery r

set_option maxHeartbeats 800000 in
-- Canonical pushforward and finite-density reductions create a large elaboration term.
/-- A nonzero canonical raw second-moment contrast forces positive paper-local Gaussian MMD.  Given [the stated inputs and conditions](hyp:hpos,hmom), [the stated conclusion](goal) follows. -/
lemma canonical_populationDiscrepancy_pos_of_secondMomentContrast_ne
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) (π : Equiv.Perm (Fin n))
    (j i : Fin n)
    (hmom : secondMomentContrast (canonicalObservedWorld G θ π) j i ≠ 0) :
    0 < populationDiscrepancy gaussianFeatureMap
      (canonicalObservedWorld G θ π) j i := by
  let W := canonicalObservedWorld G θ π
  let μ := observationalRatioLaw W i
  let ν := interventionalRatioLaw W j i
  let ratio := fun v : LatentState n =>
    θ.q (π i) (v (π i)) / θ.p (π i) v
  have hone := canonicalObservedWorld_onePerfectInterventionPerNode hpos π
  have hobsCube : ∀ᵐ v ∂observationalLaw θ, v ∈ latentCube n :=
    observationalLaw_ae_mem_latentCube hpos
  have hac : interventionalLaw θ (π j) ≪ observationalLaw θ := by
    simpa only [W, canonicalObservedWorld] using
      interventionalLaw_absolutelyContinuous_observational W hpos j
  have hintCube : ∀ᵐ v ∂interventionalLaw θ (π j), v ∈ latentCube n :=
    hac.ae_le hobsCube
  have hratioObs : observedLawRatio W.law i =ᵐ[observationalLaw θ] ratio := by
    filter_upwards [hone.2.2.1 i, hobsCube] with v hrv hv
    change ((interventionalLaw θ (π i)).rnDeriv (observationalLaw θ) v).toReal =
      θ.q (π i) (v (π i)) / θ.p (π i) v
    calc
      _ = (ENNReal.ofReal (W.ratio i v)).toReal := congrArg ENNReal.toReal hrv.symm
      _ = W.ratio i v := ENNReal.toReal_ofReal
        (div_nonneg (hpos.2.1 _ _ (hv (π i) (Set.mem_univ _))).le
          (hpos.1 _ _ hv).le)
      _ = _ := by rfl
  have hratioInt : observedLawRatio W.law i =ᵐ[interventionalLaw θ (π j)] ratio := by
    exact hac.ae_eq hratioObs
  have hratioCont : ContinuousOn ratio (latentCube n) := by
    apply ((hpos.2.2.2.1 (π i)).continuousOn.comp
      ((continuous_apply (π i)).continuousOn)
      (fun (v : LatentState n) (hv : v ∈ latentCube n) =>
        hv (π i) (Set.mem_univ _))).div
      ((hpos.2.2.1 (π i)).continuousOn)
    intro v hv
    exact ne_of_gt (hpos.1 _ _ hv)
  have hcubeCompact : IsCompact (latentCube n) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨R, hR⟩ :=
    (hcubeCompact.image_of_continuousOn hratioCont).isBounded.subset_closedBall (0 : ℝ)
  let B := max R 0
  have hB : 0 ≤ B := le_max_right _ _
  have hratioBound : ∀ v ∈ latentCube n, ratio v ∈ Set.Icc (-B) B := by
    intro v hv
    have hvball : ratio v ∈ Metric.closedBall (0 : ℝ) R :=
      hR (Set.mem_image_of_mem ratio hv)
    have habsR : |ratio v| ≤ R := by
      simpa [Real.dist_eq] using hvball
    exact (abs_le.mp (habsR.trans (le_max_left _ _)))
  have hμsupport : μ (Set.Icc (-B) B)ᶜ = 0 := by
    dsimp only [μ]
    rw [observationalRatioLaw,
      Measure.map_apply (measurable_observedLawRatio W.law i) measurableSet_Icc.compl]
    apply ae_iff.mp
    filter_upwards [hratioObs, hobsCube] with v hratio hv
    rw [hratio]
    exact hratioBound v hv
  have hνsupport : ν (Set.Icc (-B) B)ᶜ = 0 := by
    dsimp only [ν]
    rw [interventionalRatioLaw, show W.law j.succ = interventionalLaw θ (π j) by rfl,
      Measure.map_apply (measurable_observedLawRatio W.law i) measurableSet_Icc.compl]
    apply ae_iff.mp
    filter_upwards [hratioInt, hintCube] with v hratio hv
    rw [hratio]
    exact hratioBound v hv
  have hμmoment : (∫ r, r ^ 2 ∂μ) = ∫ v, (ratio v) ^ 2 ∂observationalLaw θ := by
    dsimp only [μ]
    rw [observationalRatioLaw,
      MeasureTheory.integral_map (measurable_observedLawRatio W.law i).aemeasurable
        (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [hratioObs] with v hv
    rw [hv]
  have hνmoment : (∫ r, r ^ 2 ∂ν) =
      ∫ v, (ratio v) ^ 2 ∂interventionalLaw θ (π j) := by
    dsimp only [ν]
    rw [interventionalRatioLaw, show W.law j.succ = interventionalLaw θ (π j) by rfl,
      MeasureTheory.integral_map (measurable_observedLawRatio W.law i).aemeasurable
        (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [hratioInt] with v hv
    rw [hv]
  letI : IsProbabilityMeasure (observationalLaw θ) :=
    observationalLaw_isProbabilityMeasure hpos
  letI : IsProbabilityMeasure (interventionalLaw θ (π j)) := by
    simpa only [W, canonicalObservedWorld] using
      interventionalLaw_isProbabilityMeasure W hpos j
  letI : IsFiniteMeasure (W.law 0) := by
    change IsFiniteMeasure (observationalLaw θ)
    infer_instance
  letI : IsFiniteMeasure (W.law j.succ) := by
    change IsFiniteMeasure (interventionalLaw θ (π j))
    infer_instance
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, observationalRatioLaw]
    exact Measure.isFiniteMeasure_map (W.law 0) (observedLawRatio W.law i)
  letI : IsFiniteMeasure ν := by
    dsimp only [ν, interventionalRatioLaw]
    exact Measure.isFiniteMeasure_map (W.law j.succ) (observedLawRatio W.law i)
  have hraw : (∫ r, r ^ 2 ∂μ) ≠ ∫ r, r ^ 2 ∂ν := by
    intro heq
    apply hmom
    unfold secondMomentContrast
    change (∫ v, (ratio v) ^ 2 ∂interventionalLaw θ (π j)) -
      (∫ v, (ratio v) ^ 2 ∂observationalLaw θ) = 0
    rw [← hνmoment, ← hμmoment, ← heq, sub_self]
  have hrecover :=
    CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.norm_meanEmbedding_sub_pos_of_secondMoment_ne_of_boundedSupport
      μ ν B hB hμsupport hνsupport hraw
  rw [← meanEmbedding_gaussianFeatureMap_eq_recovery μ,
    ← meanEmbedding_gaussianFeatureMap_eq_recovery ν] at hrecover
  simpa only [populationDiscrepancy, μ, ν, W] using hrecover

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
