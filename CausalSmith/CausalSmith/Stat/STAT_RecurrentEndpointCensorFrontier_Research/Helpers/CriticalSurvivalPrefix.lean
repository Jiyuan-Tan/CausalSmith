module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalSurvivalEnergy

/-!
# Prefix energy on the critical horizon

Roadmap (8) controls the true KM oracle energy at every deterministic prefix
of the shrinking horizon, with the same logarithmic envelope. The observed
left-limit KM inherits this bound plus the horizon extinction probability.
These prefix estimates do not assert the still-open maximal inequality (9).
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- Every deterministic prefix of the critical horizon has the same uniform
logarithmic oracle energy envelope, even while the bandwidth cap is active. -/
-- @node: critical_kmOracle_prefix_secondMoment_le_log_rate
lemma critical_kmOracle_prefix_secondMoment_le_log_rate
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (hn : 3 ≤ n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1 - bandwidth c n)) :
    (∫ x : Sample n,
      (Causalean.Stat.RecurrentEvent.CountingProcess.aggregateIntegral
        (referenceDeathHazard P a) (kmOracleIntegrand P a t) t x) ^ 2
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
      ((Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
        (c.pMin * Real.exp (-c.dMax)) * varianceRateEnvelope c) *
          (Real.log n / n) := by
  have hn0 : 0 < n := by omega
  have hh := bandwidth_pos_and_le_cap c hn0
  have ht1 : t < 1 := by linarith [ht.2, hh.1]
  have hT0 : 0 ≤ 1 - bandwidth c n := ht.1.trans ht.2
  have hT1 : 1 - bandwidth c n < 1 := by linarith [hh.1]
  have hb := kmOracle_aggregate_secondMoment_le_retention_integral
    c P hP a hn0 (show 0 < 1 - t by linarith) (show 1 - t ≤ 1 by linarith [ht.1])
  simp only [sub_sub_cancel] at hb
  have hi := inv_retention_integrableOn c P hP a hT0 hT1
  have hprefix : (∫ u in Icc (0 : ℝ) t, (retention P a u)⁻¹) ≤
      ∫ u in Icc (0 : ℝ) (1 - bandwidth c n), (retention P a u)⁻¹ := by
    apply setIntegral_mono_set hi
    · filter_upwards [] with u
      unfold retention
      positivity
    · exact Eventually.of_forall (fun u hu => ⟨hu.1, hu.2.trans ht.2⟩)
  have hpMin := c.pMin_pos
  have hdMax := c.dMin_pos.trans c.dMin_lt
  have hR := reciprocalRetentionEnvelope_pos c
  have hrate : (n : ℝ)⁻¹ * varianceFactor c (bandwidth c n) ≤
      varianceRateEnvelope c * (Real.log n / n) := by
    simpa only [riskScale, if_neg (by linarith : ¬ c.kappa < 1), if_pos hk] using
      critical_varianceRate_le c hn hk
  calc
    _ ≤ ((Real.exp c.dMax) ^ 2 * c.dMax * 2 /
        ((n : ℝ) * c.pMin * Real.exp (-c.dMax))) *
          ∫ u in Icc (0 : ℝ) (1 - bandwidth c n), (retention P a u)⁻¹ :=
      hb.trans (mul_le_mul_of_nonneg_left hprefix (by positivity))
    _ ≤ ((Real.exp c.dMax) ^ 2 * c.dMax * 2 /
        ((n : ℝ) * c.pMin * Real.exp (-c.dMax))) *
          (reciprocalRetentionEnvelope c * varianceFactor c (bandwidth c n)) :=
      mul_le_mul_of_nonneg_left (reciprocal_retention_integral_le c P hP a hh.1
        (hh.2.trans (by linarith [c.x0_pos]))) (by positivity)
    _ = ((Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
        (c.pMin * Real.exp (-c.dMax))) *
          ((n : ℝ)⁻¹ * varianceFactor c (bandwidth c n)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hrate (by positivity)).trans_eq (by ring)

/-- The observed strict-left survival error at every prefix is bounded by the
oracle energy and the exponentially small extinction probability at the full
critical horizon. No independence of KM and risk is used. -/
-- @node: critical_deathKMLeft_prefix_secondMoment_le_log_add_exp
lemma critical_deathKMLeft_prefix_secondMoment_le_log_add_exp
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (hn : 3 ≤ n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1 - bandwidth c n)) :
    (∫ s : Fin n → ObsHistory,
      (deathKMLeft a s t - survival P a t) ^ 2 ∂sampleLaw P n) ≤
      ((Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
        (c.pMin * Real.exp (-c.dMax)) * varianceRateEnvelope c) *
          (Real.log n / n) +
      Real.exp (-((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) *
        n * bandwidth c n)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hn0 : 0 < n := by omega
  have hh := bandwidth_pos_and_le_cap c hn0
  have ht1 : t ≤ 1 := by linarith [ht.2, hh.1]
  rw [integral_congr_ae (by
    filter_upwards [deathKMLeft_eq_deathKM_ae_fixed P hP.deathHazard a n t]
      with s hs
    rw [hs])]
  apply (deathKM_secondMoment_le_oracleAggregate_add_emptyRisk c P hP a n ht.1 ht1).trans
  apply add_le_add
  · rw [observedDeathSample_oracleAggregate_secondMoment_eq_reference c P hP a n ht.1 ht1]
    exact critical_kmOracle_prefix_secondMoment_le_log_rate c hk P hP a hn ht
  · apply (measureReal_mono (show {s : Fin n → ObsHistory | riskSet a s t = 0} ⊆
        {s | riskSet a s (1 - bandwidth c n) = 0} from ?_) (by finiteness)).trans
      (critical_endpointRiskZero_probability_le_exp c hk P hP a hn0)
    intro s hs
    have hm : riskSet a s (1 - bandwidth c n) ≤ riskSet a s t := by
      unfold riskSet
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hi.1, ht.2.trans hi.2⟩
    exact Nat.eq_zero_of_le_zero (hs ▸ hm)

/-- Along arbitrary triangular laws and deterministic evaluation times in the
shrinking horizon, the genuine observed survival error vanishes in second mean. -/
-- @node: critical_deathKMLeft_prefix_secondMoment_triangular_tendsto_zero
lemma critical_deathKMLeft_prefix_secondMoment_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) (tseq : ℕ → ℝ)
    (ht : ∀ᶠ n in atTop, tseq n ∈ Icc (0 : ℝ) (1 - bandwidth c n)) :
    Tendsto (fun n : ℕ => ∫ s : Fin n → ObsHistory,
      (deathKMLeft a s (tseq n) - survival (Pseq n) a (tseq n)) ^ 2
        ∂sampleLaw (Pseq n) n) atTop (nhds 0) := by
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
  filter_upwards [eventually_ge_atTop 3, ht] with n hn htn
  exact critical_deathKMLeft_prefix_secondMoment_le_log_add_exp c hk (Pseq n) (hP n) a hn htn

/-- Markov's inequality transfers the proved prefix KM second
moment to convergence in probability, with no extra regularity premise. -/
-- @node: critical_deathKMLeft_prefix_probability_triangular_tendsto_zero
lemma critical_deathKMLeft_prefix_probability_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) (tseq : ℕ → ℝ)
    (ht : ∀ᶠ n in atTop, tseq n ∈ Icc (0 : ℝ) (1 - bandwidth c n))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |deathKMLeft a s (tseq n) -
        survival (Pseq n) a (tseq n)|}) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [zero_div] using
      (critical_deathKMLeft_prefix_secondMoment_triangular_tendsto_zero c hk Pseq hP a tseq ht).div_const (ε ^ 2))
  filter_upwards [eventually_ge_atTop 1, ht] with n hn htn
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have ht : tseq n ∈ Icc (0 : ℝ) 1 :=
    ⟨htn.1, by linarith [htn.2, hh.1]⟩
  have hm : Measurable (fun s : Fin n → ObsHistory =>
      deathKMLeft a s (tseq n) - survival (Pseq n) a (tseq n)) := by
    fun_prop
  have hi : Integrable (fun s : Fin n → ObsHistory =>
      (deathKMLeft a s (tseq n) - survival (Pseq n) a (tseq n)) ^ 2)
      (sampleLaw (Pseq n) n) := by
    apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := deathKMLeft_mem_Icc a s (tseq n)
    have hs := survival_bounds_of_deathBounds c (Pseq n) (hP n).deathBounds a ht
    nlinarith [hb.1, hb.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory => sq_nonneg
      (deathKMLeft a s (tseq n) - survival (Pseq n) a (tseq n))))
    hi (ε ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  rw [mul_comm]
  apply (mul_le_mul_of_nonneg_left (measureReal_mono (show
      {s : Fin n → ObsHistory | ε < |deathKMLeft a s (tseq n) -
        survival (Pseq n) a (tseq n)|} ⊆
      {s | ε ^ 2 ≤ (deathKMLeft a s (tseq n) -
        survival (Pseq n) a (tseq n)) ^ 2} from ?_) (by finiteness))
      (sq_nonneg ε)).trans
  · simpa only [mul_comm] using hmarkov
  · intro s hs
    change ε < |_ - _| at hs
    change ε ^ 2 ≤ (_ - _) ^ 2
    nlinarith [sq_abs (deathKMLeft a s (tseq n) -
      survival (Pseq n) a (tseq n))]

/-- The model's survival floor converts prefix consistency to consistency of
the relative survival ratio used under the predictable-variation integral. -/
-- @node: critical_relativeDeathKMLeft_prefix_probability_triangular_tendsto_zero
lemma critical_relativeDeathKMLeft_prefix_probability_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) (tseq : ℕ → ℝ)
    (ht : ∀ᶠ n in atTop, tseq n ∈ Icc (0 : ℝ) (1 - bandwidth c n))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |deathKMLeft a s (tseq n) / survival (Pseq n) a (tseq n) - 1|})
      atTop (nhds 0) := by
  have hεS : 0 < ε * Real.exp (-c.dMax) := mul_pos hε (Real.exp_pos _)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (critical_deathKMLeft_prefix_probability_triangular_tendsto_zero
      c hk Pseq hP a tseq ht hεS)
  filter_upwards [eventually_ge_atTop 1, ht] with n hn htn
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply measureReal_mono ?_ (by finiteness)
  intro s hs
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have htime : tseq n ∈ Icc (0 : ℝ) 1 :=
    ⟨htn.1, by linarith [htn.2, hh.1]⟩
  have hfloor := (survival_bounds_of_deathBounds c (Pseq n) (hP n).deathBounds a htime).1
  have hsurv : 0 < survival (Pseq n) a (tseq n) := (Real.exp_pos _).trans_le hfloor
  change ε < |deathKMLeft a s (tseq n) / survival (Pseq n) a (tseq n) - 1| at hs
  change ε * Real.exp (-c.dMax) < |deathKMLeft a s (tseq n) - survival (Pseq n) a (tseq n)|
  have heq : deathKMLeft a s (tseq n) / survival (Pseq n) a (tseq n) - 1 =
      (deathKMLeft a s (tseq n) - survival (Pseq n) a (tseq n)) /
        survival (Pseq n) a (tseq n) := by field_simp
  rw [heq, abs_div, abs_of_pos hsurv] at hs
  exact (mul_le_mul_of_nonneg_left hfloor hε.le).trans_lt
    ((lt_div_iff₀ hsurv).mp hs)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
