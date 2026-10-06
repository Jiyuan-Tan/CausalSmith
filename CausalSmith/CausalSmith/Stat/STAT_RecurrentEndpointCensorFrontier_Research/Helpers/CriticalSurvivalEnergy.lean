module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalExtinction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessExplicitRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleIntegratedEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.HonestBandwidthRates

/-!
# Death KM energy on the shrinking critical horizon

The reciprocal-binomial calculation and endpoint retention give the logarithmic
second-moment energy bound underlying roadmap (8). The actual dependent KM
integrand is retained. Maximal survival control and the recurrence CLT remain
separate obligations.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The genuine death KM oracle action has a reciprocal-retention second-moment
bound on each positive-bandwidth horizon, without freezing retention at its
smallest value. -/
-- @node: kmOracle_aggregate_secondMoment_le_retention_integral
lemma kmOracle_aggregate_secondMoment_le_retention_integral
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a (1 - h)) (1 - h) x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      ((Real.exp c.dMax) ^ 2 * c.dMax * 2 /
        ((n : ℝ) * c.pMin * Real.exp (-c.dMax))) *
          ∫ t in Icc (0 : ℝ) (1 - h), (retention P a t)⁻¹ := by
  have hT : 0 ≤ 1 - h := by linarith
  have hT1 : 1 - h < 1 := by linarith
  let K := (Real.exp c.dMax) ^ 2 * c.dMax * 2 /
    ((n : ℝ) * c.pMin * Real.exp (-c.dMax))
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpMin := c.pMin_pos
  have hdMax := c.dMin_pos.trans c.dMin_lt
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hi := (inv_retention_integrableOn c P hP a hT hT1).const_mul K
  calc
    _ ≤ ∫ t in Icc (0 : ℝ) (1 - h),
        (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t *
          (∫ x : Sample n,
            Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
            ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
              (armDeathFailureLaw P a) (referenceDeathLaw P a)) :=
      kmOracle_aggregate_secondMoment_le_expectedInverseRisk c P hP a n hT hT1.le
    _ ≤ ∫ t in Icc (0 : ℝ) (1 - h), K * (retention P a t)⁻¹ := by
      refine integral_mono_of_nonneg ?_ hi ?_
      · filter_upwards [] with t
        exact mul_nonneg (mul_nonneg (sq_nonneg _)
          (referenceDeathHazard_nonneg hP a t))
          (integral_nonneg (fun x => (pairInverseRisk_mem_Icc t x).1))
      · filter_upwards [ae_restrict_mem measurableSet_Icc,
          (volume.restrict (Icc (0 : ℝ) (1 - h))).ae_ne (0 : ℝ)] with t ht htne
        have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
        have ht1 : t < 1 := ht.2.trans_lt hT1
        have hg := retention_pos_of_modelClass c P hP a t ht.1 ht1
        have hp := c.pMin_pos.trans_le (hP.treatmentOverlap a)
        have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a
          ⟨ht.1, ht1.le⟩).1
        have hprod : c.pMin * retention P a t * Real.exp (-c.dMax) ≤
            P.p a * retention P a t * survival P a t := by
          gcongr
          exact hP.treatmentOverlap a
        have hr := (integral_inverseRisk_le_arm_tail c P hP a hn ht0 ht1).trans
          (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
            (by positivity : 0 < (n : ℝ) *
              (c.pMin * retention P a t * Real.exp (-c.dMax)))
            (mul_le_mul_of_nonneg_left hprod hnR.le))
        have hd : referenceDeathHazard P a t ≤ c.dMax := by
          rw [referenceDeathHazard_eq P a ⟨ht.1, ht1.le⟩]
          exact (hP.deathBounds a t ⟨ht.1, ht1.le⟩).2
        calc
          _ ≤ (Real.exp c.dMax) ^ 2 * c.dMax *
              (2 / ((n : ℝ) *
                (c.pMin * retention P a t * Real.exp (-c.dMax)))) := by
            apply mul_le_mul
              (mul_le_mul_of_nonneg_left hd (sq_nonneg _)) hr
              (integral_nonneg (fun x => (pairInverseRisk_mem_Icc t x).1))
              (by positivity)
          _ = K * (retention P a t)⁻¹ := by dsimp [K]; ring
    _ = _ := by rw [integral_const_mul]

/-- Integrating the model's inverse-retention envelope gives a uniform KM
energy bound at every bandwidth in the endpoint region. -/
-- @node: kmOracle_aggregate_secondMoment_le_varianceFactor
lemma kmOracle_aggregate_secondMoment_le_varianceFactor
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (hhx : h ≤ c.x0) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a (1 - h)) (1 - h) x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      ((Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
        (c.pMin * Real.exp (-c.dMax))) * ((n : ℝ)⁻¹ * varianceFactor c h) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpMin := c.pMin_pos
  have hdMax := c.dMin_pos.trans c.dMin_lt
  have hb := kmOracle_aggregate_secondMoment_le_retention_integral c P hP a hn hh
    (hhx.trans (c.x0_le.trans (by norm_num)))
  apply hb.trans
  calc
    _ ≤ ((Real.exp c.dMax) ^ 2 * c.dMax * 2 /
        ((n : ℝ) * c.pMin * Real.exp (-c.dMax))) *
          (reciprocalRetentionEnvelope c * varianceFactor c h) :=
      mul_le_mul_of_nonneg_left (reciprocal_retention_integral_le c P hP a hh hhx)
        (by positivity)
    _ = _ := by ring

/-- At exponent one, the energy is bounded by log n over n uniformly in the
law, including finite sample sizes at which the bandwidth cap is active. -/
-- @node: critical_kmOracle_aggregate_secondMoment_le_log_rate
lemma critical_kmOracle_aggregate_secondMoment_le_log_rate
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (hn : 3 ≤ n) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a (1 - bandwidth c n))
        (1 - bandwidth c n) x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      ((Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
        (c.pMin * Real.exp (-c.dMax)) * varianceRateEnvelope c) *
          (Real.log n / n) := by
  have hn0 : 0 < n := by omega
  have hh := bandwidth_pos_and_le_cap c hn0
  apply (kmOracle_aggregate_secondMoment_le_varianceFactor c P hP a hn0 hh.1
    (hh.2.trans (by linarith [c.x0_pos]))).trans
  have hrate : (n : ℝ)⁻¹ * varianceFactor c (bandwidth c n) ≤
      varianceRateEnvelope c * (Real.log n / n) := by
    simpa only [riskScale, if_neg (by linarith : ¬ c.kappa < 1), if_pos hk] using
      critical_varianceRate_le c hn hk
  have hR := reciprocalRetentionEnvelope_pos c
  have hpMin := c.pMin_pos
  have hdMax := c.dMin_pos.trans c.dMin_lt
  exact (mul_le_mul_of_nonneg_left hrate (by positivity)).trans_eq (by ring)

/-- The observed left-limit survival error at the shrinking critical cutoff
has the logarithmic energy envelope plus the exponentially small extinction
contribution. The dependent KM factor is transported through its true law. -/
-- @node: critical_deathKMLeft_cutoff_secondMoment_le_log_add_exp
lemma critical_deathKMLeft_cutoff_secondMoment_le_log_add_exp
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (hn : 3 ≤ n) :
    (∫ s : Fin n → ObsHistory,
      (deathKMLeft a s (1 - bandwidth c n) -
        survival P a (1 - bandwidth c n)) ^ 2 ∂sampleLaw P n) ≤
      ((Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
        (c.pMin * Real.exp (-c.dMax)) * varianceRateEnvelope c) *
          (Real.log n / n) +
      Real.exp (-((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) *
        n * bandwidth c n)) := by
  have hn0 : 0 < n := by omega
  have hh := bandwidth_pos_and_le_cap c hn0
  have hT : 0 ≤ 1 - bandwidth c n := by linarith [hh.2, c.x0_le]
  have hT1 : 1 - bandwidth c n ≤ 1 := by linarith [hh.1]
  rw [integral_congr_ae (by
    filter_upwards [deathKMLeft_eq_deathKM_ae_fixed P hP.deathHazard a n
      (1 - bandwidth c n)] with s hs
    rw [hs])]
  apply (deathKM_secondMoment_le_oracleAggregate_add_emptyRisk c P hP a n hT hT1).trans
  apply add_le_add
  · rw [observedDeathSample_oracleAggregate_secondMoment_eq_reference c P hP a n hT hT1]
    exact critical_kmOracle_aggregate_secondMoment_le_log_rate c hk P hP a hn
  · exact critical_endpointRiskZero_probability_le_exp c hk P hP a hn0

/-- The actual left-limit KM error at the moving cutoff tends to zero in
second mean along arbitrary triangular critical model laws. -/
-- @node: critical_deathKMLeft_cutoff_secondMoment_triangular_tendsto_zero
lemma critical_deathKMLeft_cutoff_secondMoment_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (deathKMLeft a s (1 - bandwidth c n) -
        survival (Pseq n) a (1 - bandwidth c n)) ^ 2 ∂sampleLaw (Pseq n) n)
      atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / n) atTop (nhds 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := (hlog.const_mul
    ((Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
      (c.pMin * Real.exp (-c.dMax)) * varianceRateEnvelope c)).add
    (critical_extinction_exp_tendsto_zero c hk)
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _)))
    _ (by simpa only [mul_zero, add_zero] using hb)
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact critical_deathKMLeft_cutoff_secondMoment_le_log_add_exp c hk (Pseq n) (hP n) a hn

/-- Markov's inequality transfers the proved shrinking-horizon KM second
moment to convergence in probability, with no extra regularity premise. -/
-- @node: critical_deathKMLeft_cutoff_probability_triangular_tendsto_zero
lemma critical_deathKMLeft_cutoff_probability_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |deathKMLeft a s (1 - bandwidth c n) -
        survival (Pseq n) a (1 - bandwidth c n)|}) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [zero_div] using
      (critical_deathKMLeft_cutoff_secondMoment_triangular_tendsto_zero c hk Pseq hP a).div_const (ε ^ 2))
  filter_upwards [eventually_ge_atTop 1] with n hn
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have ht : 1 - bandwidth c n ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hh.2, c.x0_le, hh.1]
  have hm : Measurable (fun s : Fin n → ObsHistory =>
      deathKMLeft a s (1 - bandwidth c n) - survival (Pseq n) a (1 - bandwidth c n)) := by
    fun_prop
  have hi : Integrable (fun s : Fin n → ObsHistory =>
      (deathKMLeft a s (1 - bandwidth c n) - survival (Pseq n) a (1 - bandwidth c n)) ^ 2)
      (sampleLaw (Pseq n) n) := by
    apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := deathKMLeft_mem_Icc a s (1 - bandwidth c n)
    have hs := survival_bounds_of_deathBounds c (Pseq n) (hP n).deathBounds a ht
    nlinarith [hb.1, hb.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory => sq_nonneg
      (deathKMLeft a s (1 - bandwidth c n) - survival (Pseq n) a (1 - bandwidth c n))))
    hi (ε ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  rw [mul_comm]
  apply (mul_le_mul_of_nonneg_left (measureReal_mono (show
      {s : Fin n → ObsHistory | ε < |deathKMLeft a s (1 - bandwidth c n) -
        survival (Pseq n) a (1 - bandwidth c n)|} ⊆
      {s | ε ^ 2 ≤ (deathKMLeft a s (1 - bandwidth c n) -
        survival (Pseq n) a (1 - bandwidth c n)) ^ 2} from ?_) (by finiteness))
      (sq_nonneg ε)).trans
  · simpa only [mul_comm] using hmarkov
  · intro s hs
    change ε < |_ - _| at hs
    change ε ^ 2 ≤ (_ - _) ^ 2
    nlinarith [sq_abs (deathKMLeft a s (1 - bandwidth c n) -
      survival (Pseq n) a (1 - bandwidth c n))]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
