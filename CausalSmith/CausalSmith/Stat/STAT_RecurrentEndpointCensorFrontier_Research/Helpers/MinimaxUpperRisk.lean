module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestExtinctionRates

/-! # Uniform contrast risk and minimax upper bound

The arm envelopes and bandwidth comparisons bound the observable contrast.
Its measurable, integrable loss supplies an admissible estimator for the
extended-valued all-estimator minimax problem.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Bounded projected arm losses are integrable under the sample law. -/
-- @node: integrable_muHatAt_sq_loss
lemma integrable_muHatAt_sq_loss (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) (band : ℝ) :
    Integrable (fun s : Fin n → ObsHistory =>
      (muHatAt c band a s - armMean P a) ^ 2) (sampleLaw P n) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hm : Measurable (fun s : Fin n → ObsHistory =>
      (muHatAt c band a s - armMean P a) ^ 2) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (c.lambdaMax ^ 2)
  apply Filter.Eventually.of_forall
  intro s
  have hs := projectArm_mem_range c (muTildeAt c band a s)
  change 0 ≤ muHatAt c band a s ∧ muHatAt c band a s ≤ c.lambdaMax at hs
  have ht := armMean_mem_projectionRange c P hP a
  have ha : |muHatAt c band a s - armMean P a| ≤ c.lambdaMax := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)).2 ha

/-- The contrast risk is bounded by twice the sum of the two arm risks;
no covariance or independence between the estimates is needed. -/
-- @node: observableEstimator_sqRisk_le_arm_risks
lemma observableEstimator_sqRisk_le_arm_risks (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (n : ℕ) :
    Causalean.Stat.sqRisk (sampleLaw P n) (observableEstimator c) (causalTarget P) ≤
      2 * Causalean.Stat.sqRisk (sampleLaw P n)
        (muHatAt c (bandwidth c n) true) (armMean P true) +
      2 * Causalean.Stat.sqRisk (sampleLaw P n)
        (muHatAt c (bandwidth c n) false) (armMean P false) := by
  have h1 := integrable_muHatAt_sq_loss c P hP true n (bandwidth c n)
  have h0 := integrable_muHatAt_sq_loss c P hP false n (bandwidth c n)
  have hi := integral_mono (integrable_observableEstimator_sq_loss c P hP n)
    ((h1.const_mul 2).add (h0.const_mul 2)) (fun s => by
      rw [causalTarget_eq_armMean_contrast c P hP]
      unfold observableEstimator
      dsimp only [Pi.add_apply]
      nlinarith [sq_nonneg ((muHatAt c (bandwidth c n) true s - armMean P true) +
        (muHatAt c (bandwidth c n) false s - armMean P false))])
  simp only [Pi.add_apply, integral_add (h1.const_mul 2) (h0.const_mul 2),
    integral_const_mul] at hi
  exact hi

/-- Substituting the bandwidth comparisons in the explicit arm envelope
supplies the computable uniform arm-risk coefficient. This assembly retains
the existing dependency on the explicit Taylor-bias bound. -/
-- @node: muHat_bandwidth_sqRisk_le_envelope
lemma muHat_bandwidth_sqRisk_le_envelope (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) (hn : 3 ≤ n) :
    Causalean.Stat.sqRisk (sampleLaw P n) (muHatAt c (bandwidth c n) a)
      (armMean P a) ≤
      (explicitBiasRisk c + explicitVarianceRisk c * varianceRateEnvelope c +
        explicitExtinctionRisk c *
          max (extinctionPreEnvelope c) (extinctionTailEnvelope c)) * riskScale c n := by
  have hb := bandwidth_biasPower_le_riskScale c hn
  have hv := bandwidth_varianceRate_le_riskScale c hn
  have he := bandwidth_extinction_le_envelope_mul_riskScale c hn
  have hband := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hr := upper_risk_explicit c P hP a n hn (bandwidth c n) hband
  have hB : 0 ≤ explicitBiasRisk c := by unfold explicitBiasRisk; positivity
  have hV := (explicitVarianceRisk_pos c).le
  have hE := (explicitExtinctionRisk_pos c).le
  have hb' := mul_le_mul_of_nonneg_left hb hB
  have hv' := mul_le_mul_of_nonneg_left hv hV
  have he' := mul_le_mul_of_nonneg_left he hE
  calc
    _ ≤ explicitBiasRisk c * (bandwidth c n) ^ (2 * c.beta + 2) +
        explicitVarianceRisk c * (n : ℝ)⁻¹ * varianceFactor c (bandwidth c n) +
        explicitExtinctionRisk c *
          Real.exp (-(extinctionExponent c * n * (bandwidth c n) ^ c.kappa)) := hr
    _ ≤ _ := by nlinarith only [hb', hv', he']

/-- The elementary two-arm inequality gives the declared calibration
coefficient after the three bandwidth comparisons. -/
-- @node: observableEstimator_sqRisk_le_honestConstant
lemma observableEstimator_sqRisk_le_honestConstant (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (n : ℕ) (hn : 3 ≤ n)
    (alpha : ℝ) (ha : 0 < alpha) :
    Causalean.Stat.sqRisk (sampleLaw P n) (observableEstimator c) (causalTarget P) ≤
      alpha * (honestConstant c alpha * riskScale c n) := by
  have hr := observableEstimator_sqRisk_le_arm_risks c P hP n
  have h1 := muHat_bandwidth_sqRisk_le_envelope c P hP true n hn
  have h0 := muHat_bandwidth_sqRisk_le_envelope c P hP false n hn
  unfold honestConstant
  field_simp
  nlinarith only [hr, h1, h0]

/-- The extended risk of the projected contrast agrees with the finite
Bochner risk; boundedness prevents the nonintegrable-loss convention. -/
-- @node: observableEstimator_sqRiskLIntegral_eq
lemma observableEstimator_sqRiskLIntegral_eq (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (n : ℕ) :
    Causalean.Stat.sqRiskLIntegral (sampleLaw P n) (observableEstimator c)
      (causalTarget P) = ENNReal.ofReal
        (Causalean.Stat.sqRisk (sampleLaw P n) (observableEstimator c)
          (causalTarget P)) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_observableEstimator_sq_loss c P hP n)
    (Filter.Eventually.of_forall fun s => sq_nonneg _)).symm

/-- Taking the supremum over models and infimum over measurable estimators
preserves the explicit finite contrast-risk bound. -/
-- @node: minimaxRisk_le_honestConstant
lemma minimaxRisk_le_honestConstant (c : ClassConstants) (n : ℕ) (hn : 3 ≤ n)
    (alpha : ℝ) (ha : 0 < alpha) :
    minimaxRisk c n ≤ alpha * (honestConstant c alpha * riskScale c n) := by
  let risk := fun (f : {f : (Fin n → ObsHistory) → ℝ // Measurable f})
    (P : {P : SubjectLaw // ModelClass c P}) =>
      Causalean.Stat.sqRiskLIntegral (sampleLaw P.1 n) f.1 (causalTarget P.1)
  let est : {f : (Fin n → ObsHistory) → ℝ // Measurable f} :=
    ⟨observableEstimator c, measurable_observableEstimator c n⟩
  have hbound : Causalean.Stat.minimaxValueENNReal risk ≤
      ENNReal.ofReal (alpha * (honestConstant c alpha * riskScale c n)) := by
    apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk est).trans
    apply Causalean.Stat.worstCaseRiskENNReal_le
    intro P
    change Causalean.Stat.sqRiskLIntegral _ (observableEstimator c) _ ≤ _
    rw [observableEstimator_sqRiskLIntegral_eq c P.1 P.2 n]
    exact ENNReal.ofReal_le_ofReal
      (observableEstimator_sqRisk_le_honestConstant c P.1 P.2 n hn alpha ha)
  have hnonneg : 0 ≤ alpha * (honestConstant c alpha * riskScale c n) :=
    mul_nonneg ha.le (mul_nonneg (honestConstant_pos c ha).le (riskScale_pos c hn).le)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hnonneg)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
