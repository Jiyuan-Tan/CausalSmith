module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalIntervalLength
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceVariationFirstMoment

/-!
# Mean critical optional variation

Roadmap (33): conditional Poisson compensation identifies mean optional
variation with the recurrence error energy. The existing reciprocal-binomial
and endpoint-retention bounds then give the logarithmic mean-variation rate.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The squared recurrence coefficient at the actual estimation bandwidth. -/
-- @node: criticalRecurrenceVariationWeight
noncomputable def criticalRecurrenceVariationWeight (c : ClassConstants) (a : Arm)
    {n : ℕ} (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) : ℝ :=
  if t ≤ 1 - bandwidth c n then
    recurrenceSubjectWeight c (bandwidth c n) a
      (fun j => recurrenceExposureHistory (e j)) i t ^ 2 else 0

/-- Exposure-dependent squared weights are jointly measurable. -/
-- @node: measurable_criticalRecurrenceVariationWeight
@[fun_prop]
lemma measurable_criticalRecurrenceVariationWeight (c : ClassConstants) (a : Arm)
    (n : ℕ) (i : Fin n) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      criticalRecurrenceVariationWeight c a p.1 i p.2) := by
  unfold criticalRecurrenceVariationWeight
  apply Measurable.ite (measurableSet_le measurable_snd measurable_const)
    (by fun_prop) measurable_const

/-- Bounded continuation weights suffice for conditional compensation. -/
-- @node: criticalRecurrenceVariationWeight_abs_le
lemma criticalRecurrenceVariationWeight_abs_le (c : ClassConstants) (a : Arm)
    {n : ℕ} (hn : 0 < n) (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) :
    |criticalRecurrenceVariationWeight c a e i t| ≤ weightEnvelope c ^ 2 := by
  unfold criticalRecurrenceVariationWeight
  split_ifs
  · rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (recurrenceSubjectWeight_abs_le c (bandwidth_pos_and_le_cap c hn).1 a _ i t) 2
  · simp only [abs_zero]; positivity

/-- The actual optional variation minus its intensity energy is exactly a
conditionally centered Poisson score, retaining empirical coefficient dependence. -/
-- @node: armCriticalVariance_sub_energy_eq_latent_score
lemma armCriticalVariance_sub_energy_eq_latent_score (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    (z : Fin n → LatentSubject) :
    armCriticalVariance c a (fun j => observe (z j)) -
      (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
        recurrenceSubjectWeight c (bandwidth c n) a (fun j => observe (z j)) i t ^ 2 *
          P.lam a t) =
    recurrenceJointExposureScore P a n (criticalRecurrenceVariationWeight c a)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) := by
  classical
  have hh := bandwidth_pos_and_le_cap c hn
  have hh1 : bandwidth c n ≤ 1 := by linarith [hh.2, c.x0_le]
  unfold armCriticalVariance recurrenceJointExposureScore criticalRecurrenceVariationWeight
  simp_rw [← recurrenceSubjectWeight_eq_exposureHistory]
  simp_rw [recurrenceIntensity_integral_truncated P hP.poissonRecurrence a _
    (by linarith : 0 ≤ 1 - bandwidth c n) (by linarith : 1 - bandwidth c n ≤ 1)]
  rw [Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (z i).treatment = a
  · simp only [observe, hi, ↓reduceIte]
    rw [recurrence_stopped_weighted_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [recurrenceSubjectWeight, hi, true_and]
    by_cases hx : (((z i).recur a).2 k).1 ≤ min ((z i).death a) (censorHorizon (z i) a)
    <;> by_cases ht : (((z i).recur a).2 k).1 ≤ 1 - bandwidth c n
    <;> simp [hx, ht, mul_pow]
  · simp [recurrenceSubjectWeight, observe, hi]

/-- Conditional centering equates the mean actual studentizer contribution
with the already proved recurrence-martingale second moment. -/
-- @node: armCriticalVariance_integral_eq_recurrenceError_secondMoment
lemma armCriticalVariance_integral_eq_recurrenceError_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory, armCriticalVariance c a s ∂sampleLaw P n) =
      ∫ s : Fin n → ObsHistory, recurrenceError c P a s (bandwidth c n) ^ 2
        ∂sampleLaw P n := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hh := bandwidth_pos_and_le_cap c hn
  have hh1 : bandwidth c n ≤ 1 := by linarith [hh.2, c.x0_le]
  let energy := fun s : Fin n → ObsHistory => ∑ i : Fin n,
    ∫ t in (0 : ℝ)..(1 - bandwidth c n),
      recurrenceSubjectWeight c (bandwidth c n) a s i t ^ 2 * P.lam a t
  have hm : Measurable energy := Finset.measurable_sum _ (fun i _ =>
    measurable_recurrenceWeightIntegral c P hP.poissonRecurrence a i hh.1.le hh1 2)
  have he : Integrable energy (sampleLaw P n) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (n * (weightEnvelope c ^ 2 * c.lambdaMax))
    exact Eventually.of_forall (fun s => by
      simpa only [Real.norm_eq_abs] using recurrence_integrated_energy_abs_le c P hP a s hh.1 hh1)
  obtain ⟨_, hz⟩ := recurrenceJointExposureScore_latent_mean_zero c P hP a n
    (criticalRecurrenceVariationWeight c a)
    (measurable_criticalRecurrenceVariationWeight c a n)
    (recurrenceJointExposure_bounded_energy_integrable P hP.poissonRecurrence a n _
      (measurable_criticalRecurrenceVariationWeight c a n) (weightEnvelope c ^ 2)
      (criticalRecurrenceVariationWeight_abs_le c a hn))
  have hv := integrable_armCriticalVariance c P hP a hn
  have hzero : (∫ s : Fin n → ObsHistory, armCriticalVariance c a s - energy s
      ∂sampleLaw P n) = 0 := by
    rw [recurrence_sampleLaw_eq_latent_map,
      integral_map (show Measurable (fun z : Fin n → LatentSubject =>
        fun i => observe (z i)) by fun_prop).aemeasurable
        ((show Measurable (fun s : Fin n → ObsHistory =>
          armCriticalVariance c a s - energy s) from (by fun_prop)).aestronglyMeasurable)]
    simp_rw [show ∀ z : Fin n → LatentSubject,
      armCriticalVariance c a (fun j => observe (z j)) - energy (fun j => observe (z j)) =
      recurrenceJointExposureScore P a n (criticalRecurrenceVariationWeight c a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) from armCriticalVariance_sub_energy_eq_latent_score c P hP a hn]
    exact hz
  rw [integral_sub hv he] at hzero
  rw [recurrenceError_secondMoment_eq_subject_energy c P hP a n hh.1 hh1]
  exact sub_eq_zero.mp hzero

/-- Roadmap (33)'s finite-sample mean bound follows from the genuine
conditional energy identity and the reciprocal-binomial risk calculation. -/
-- @node: armCriticalVariance_mean_le_explicit
lemma armCriticalVariance_mean_le_explicit
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) :
    (∫ s : Fin n → ObsHistory, armCriticalVariance c a s ∂sampleLaw P n) ≤
      2 * reciprocalRetentionEnvelope c * weightEnvelope c ^ 2 / c.pMin *
        c.lambdaMax * Real.exp c.dMax * (n : ℝ)⁻¹ *
          varianceFactor c (bandwidth c n) := by
  rw [armCriticalVariance_integral_eq_recurrenceError_secondMoment c P hP a hn]
  exact recurrenceError_secondMoment_le_explicit c P hP a hn
    (bandwidth_pos_and_le_cap c hn).1
    ((bandwidth_pos_and_le_cap c hn).2.trans (by linarith [c.x0_pos]))

/-- The logarithmic mean-variation bound is uniform in the model law and
holds also for the finite sample sizes where the bandwidth cap is active. -/
-- @node: criticalVarianceEstimator_mean_le_log_rate
lemma criticalVarianceEstimator_mean_le_log_rate
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    {n : ℕ} (hn : 3 ≤ n) :
    (∫ s : Fin n → ObsHistory, criticalVarianceEstimator c s ∂sampleLaw P n) ≤
      (4 * reciprocalRetentionEnvelope c * weightEnvelope c ^ 2 / c.pMin *
        c.lambdaMax * Real.exp c.dMax * varianceRateEnvelope c) * (Real.log n / n) := by
  have hn0 : 0 < n := by omega
  let K := 2 * reciprocalRetentionEnvelope c * weightEnvelope c ^ 2 / c.pMin *
    c.lambdaMax * Real.exp c.dMax
  have hK : 0 ≤ K := by
    dsimp [K]
    have hR := reciprocalRetentionEnvelope_pos c
    have hl := c.lambdaMin_pos.trans c.lambdaMin_lt
    have hp := c.pMin_pos
    positivity
  have ha (a : Arm) :
      (∫ s : Fin n → ObsHistory, armCriticalVariance c a s ∂sampleLaw P n) ≤
        K * (varianceRateEnvelope c * (Real.log n / n)) := by
    calc
      _ ≤ K * ((n : ℝ)⁻¹ * varianceFactor c (bandwidth c n)) := by
        simpa only [K, mul_assoc] using armCriticalVariance_mean_le_explicit c P hP a hn0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        simpa only [riskScale, if_neg (by linarith : ¬ c.kappa < 1), if_pos hk] using
          critical_varianceRate_le c hn hk) hK
  unfold criticalVarianceEstimator
  rw [integral_add (integrable_armCriticalVariance c P hP false hn0)
    (integrable_armCriticalVariance c P hP true hn0)]
  calc
    _ ≤ K * (varianceRateEnvelope c * (Real.log n / n)) +
        K * (varianceRateEnvelope c * (Real.log n / n)) := add_le_add (ha false) (ha true)
    _ = _ := by dsimp [K]; ring

/-- Jensen and the proved logarithmic mean rate reduce the entire expected
length claim to its remaining fallback probability bound. -/
-- @node: criticalInterval_expected_length_le_log_rate_fallback
lemma criticalInterval_expected_length_le_log_rate_fallback
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1 / 2) {n : ℕ} (hn : 3 ≤ n) :
    (∫ s, volume.real (criticalInterval c alpha s) ∂sampleLaw P n) ≤
      2 * normalQuantile alpha * Real.sqrt
        ((4 * reciprocalRetentionEnvelope c * weightEnvelope c ^ 2 / c.pMin *
          c.lambdaMax * Real.exp c.dMax * varianceRateEnvelope c) * (Real.log n / n)) +
        2 * c.lambdaMax * (sampleLaw P n).real {s | ¬ nonFallback c s} := by
  apply (criticalInterval_expected_length_le_model_mean_variance_fallback
    c P hP alpha ha0 ha1 (show 0 < n by omega)).trans
  apply add_le_add _ (le_refl _)
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (criticalVarianceEstimator_mean_le_log_rate c hk P hP hn))
    (by have hz := (normalQuantile_pos ha0 ha1).le; positivity)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
