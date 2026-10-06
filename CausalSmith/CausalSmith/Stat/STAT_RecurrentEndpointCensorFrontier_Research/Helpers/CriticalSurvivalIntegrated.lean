module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalSurvivalPrefix

/-!
# Integrated critical survival error

The prefix energy bound from roadmap (8) is integrated against the actual
inverse-retention weight. Fubini preserves the dependence of the KM estimator
on the observed sample. The normalized weighted second mean tends to zero,
providing the survival-error control needed under the integral in (14)--(15).
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- The squared observed KM error is jointly integrable against inverse
retention on every strict horizon; all regularity follows from the model. -/
-- @node: critical_survival_weighted_error_integrable_prod
lemma critical_survival_weighted_error_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) {T : ℝ} (hT : 0 ≤ T) (hT1 : T < 1) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      (retention P a p.2)⁻¹ * (deathKMLeft a p.1 p.2 - survival P a p.2) ^ 2)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) T))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let g := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hg : Measurable g := (modelClass_survival_continuousOn c P hP a).measurable_piecewise
    continuousOn_const measurableSet_Icc
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      (deathKMLeft a p.1 p.2 - g p.2) ^ 2) :=
    ((measurable_recurrenceDeathKMLeft_joint a).sub (hg.comp measurable_snd)).pow_const 2
  have hi : Integrable (fun p : (Fin n → ObsHistory) × ℝ => (retention P a p.2)⁻¹)
      ((sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) T))) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) (μ := sampleLaw P n)).mul_prod
        (inv_retention_integrableOn c P hP a hT hT1)
  have htprod : ∀ᵐ p : (Fin n → ObsHistory) × ℝ ∂
      (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) T)), p.2 ∈ Icc (0 : ℝ) T :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).2
      (Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Icc))
  have hb : ∀ᵐ p : (Fin n → ObsHistory) × ℝ ∂
      (sampleLaw P n).prod (volume.restrict (Icc (0 : ℝ) T)),
      ‖(deathKMLeft a p.1 p.2 - g p.2) ^ 2‖ ≤ 1 := by
    filter_upwards [htprod] with p hp
    have ht : p.2 ∈ Icc (0 : ℝ) 1 := ⟨hp.1, hp.2.trans hT1.le⟩
    simp only [g, Set.piecewise, if_pos ht, Real.norm_eq_abs, abs_pow, sq_abs]
    have hk := deathKMLeft_mem_Icc a p.1 p.2
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht
    nlinarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]
  apply (hi.bdd_mul hm.aestronglyMeasurable hb).congr
  filter_upwards [htprod] with p hp
  have ht : p.2 ∈ Icc (0 : ℝ) 1 := ⟨hp.1, hp.2.trans hT1.le⟩
  simp [g, ht, mul_comm]

/-- Fubini and the uniform prefix second moment control the actual integrated
survival error with its inverse-retention weight on the shrinking horizon. -/
-- @node: critical_survival_weighted_secondMean_le
lemma critical_survival_weighted_secondMean_le
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (hn : 3 ≤ n) :
    (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) (1 - bandwidth c n),
      (retention P a t)⁻¹ * (deathKMLeft a s t - survival P a t) ^ 2)
      ∂sampleLaw P n) ≤
    (((Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
      (c.pMin * Real.exp (-c.dMax)) * varianceRateEnvelope c) * (Real.log n / n) +
      Real.exp (-((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) * n * bandwidth c n))) *
        (∫ t in Icc (0 : ℝ) (1 - bandwidth c n), (retention P a t)⁻¹) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hT : 0 ≤ 1 - bandwidth c n := by linarith [hh.2, c.x0_le]
  have hT1 : 1 - bandwidth c n < 1 := by linarith [hh.1]
  have hi := critical_survival_weighted_error_integrable_prod c P hP a n hT hT1
  rw [integral_integral_swap hi]
  let B := ((Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
      (c.pMin * Real.exp (-c.dMax)) * varianceRateEnvelope c) * (Real.log n / n) +
      Real.exp (-((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) * n * bandwidth c n))
  have hir := (inv_retention_integrableOn c P hP a hT hT1).const_mul B
  calc
    _ ≤ ∫ t in Icc (0 : ℝ) (1 - bandwidth c n), B * (retention P a t)⁻¹ := by
      apply integral_mono_ae hi.integral_prod_right hir
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left
        (critical_deathKMLeft_prefix_secondMoment_le_log_add_exp c hk P hP a hn ht)
        (by unfold retention; positivity)).trans_eq (mul_comm _ _)
    _ = _ := by rw [integral_const_mul]

/-- The normalized inverse-retention mass is uniformly bounded, including
sample sizes at which the bandwidth cap is active. -/
-- @node: critical_retention_integral_div_log_le
lemma critical_retention_integral_div_log_le
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (hn : 3 ≤ n) :
    (∫ t in Icc (0 : ℝ) (1 - bandwidth c n), (retention P a t)⁻¹) / Real.log n ≤
      reciprocalRetentionEnvelope c * varianceRateEnvelope c := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hl : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num)
    (one_le_log_sampleSize hn)
  have hh := bandwidth_pos_and_le_cap c hn0
  have hb := reciprocal_retention_integral_le c P hP a hh.1
    (hh.2.trans (by linarith [c.x0_pos]))
  have hrate : (n : ℝ)⁻¹ * varianceFactor c (bandwidth c n) ≤
      varianceRateEnvelope c * (Real.log n / n) := by
    simpa only [riskScale, if_neg (by linarith : ¬ c.kappa < 1), if_pos hk] using
      critical_varianceRate_le c hn hk
  have hv := mul_le_mul_of_nonneg_left hrate hnR.le
  have he1 : (n : ℝ) * ((n : ℝ)⁻¹ * varianceFactor c (bandwidth c n)) =
      varianceFactor c (bandwidth c n) := by field_simp
  have he2 : (n : ℝ) * (varianceRateEnvelope c * (Real.log n / n)) =
      varianceRateEnvelope c * Real.log n := by field_simp
  rw [he1, he2] at hv
  apply (div_le_iff₀ hl).2
  exact hb.trans ((mul_le_mul_of_nonneg_left hv (reciprocalRetentionEnvelope_pos c).le).trans_eq (by ring))

/-- Integrating the uniform prefix energy gives vanishing normalized weighted
second mean along arbitrary triangular laws. This controls survival error
under the singular oracle weight without claiming a maximal probability rate. -/
-- @node: critical_survival_weighted_secondMean_div_log_triangular_tendsto_zero
lemma critical_survival_weighted_secondMean_div_log_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) :
    Tendsto (fun n : ℕ =>
      (∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) (1 - bandwidth c n),
        (retention (Pseq n) a t)⁻¹ *
          (deathKMLeft a s t - survival (Pseq n) a t) ^ 2)
        ∂sampleLaw (Pseq n) n) / Real.log n) atTop (nhds 0) := by
  let K := (Real.exp c.dMax) ^ 2 * c.dMax * 2 * reciprocalRetentionEnvelope c /
    (c.pMin * Real.exp (-c.dMax)) * varianceRateEnvelope c
  let B := fun n : ℕ => K * (Real.log n / n) +
    Real.exp (-((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) * n * bandwidth c n))
  have hlog : Tendsto (fun n : ℕ => Real.log n / n) atTop (nhds 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hB : Tendsto B atTop (nhds 0) := by
    simpa only [B, mul_zero, add_zero] using
      (hlog.const_mul K).add (critical_extinction_exp_tendsto_zero c hk)
  apply squeeze_zero' ?_ ?_ (show Tendsto (fun n =>
      B n * (reciprocalRetentionEnvelope c * varianceRateEnvelope c)) atTop (nhds 0) by
    simpa only [zero_mul] using hB.mul_const _)
  · filter_upwards [eventually_ge_atTop 3] with n hn
    exact div_nonneg (integral_nonneg (fun s => integral_nonneg (fun t =>
      mul_nonneg (by unfold retention; positivity) (sq_nonneg _))))
      (lt_of_lt_of_le (by norm_num) (one_le_log_sampleSize hn)).le
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hl : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num)
      (one_le_log_sampleSize hn)
    have hnonneg : 0 ≤ B n := by
      have hR := (reciprocalRetentionEnvelope_pos c).le
      have hV := (varianceRateEnvelope_pos c).le
      have hd := c.dMin_pos.trans c.dMin_lt
      have hp := c.pMin_pos
      dsimp [B, K]
      positivity
    calc
      _ ≤ B n *
          ((∫ t in Icc (0 : ℝ) (1 - bandwidth c n), (retention (Pseq n) a t)⁻¹) /
            Real.log n) := by
        simpa only [B, K, mul_div_assoc] using div_le_div_of_nonneg_right
          (critical_survival_weighted_secondMean_le c hk (Pseq n) (hP n) a hn) hl.le
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (critical_retention_integral_div_log_le c hk (Pseq n) (hP n) a hn) hnonneg

/-- Markov transfers the weighted second-mean limit to the actual sample
probability. No independence or extra measurability hypothesis is imposed. -/
-- @node: critical_survival_weighted_error_probability_triangular_tendsto_zero
lemma critical_survival_weighted_error_probability_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < (∫ t in Icc (0 : ℝ) (1 - bandwidth c n),
        (retention (Pseq n) a t)⁻¹ *
          (deathKMLeft a s t - survival (Pseq n) a t) ^ 2) / Real.log n})
      atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [zero_div] using
      (critical_survival_weighted_secondMean_div_log_triangular_tendsto_zero
        c hk Pseq hP a).div_const ε)
  filter_upwards [eventually_ge_atTop 3] with n hn
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  have hl : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num)
    (one_le_log_sampleSize hn)
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  let X := fun s : Fin n → ObsHistory =>
    ∫ t in Icc (0 : ℝ) (1 - bandwidth c n), (retention (Pseq n) a t)⁻¹ *
      (deathKMLeft a s t - survival (Pseq n) a t) ^ 2
  have hX (s : Fin n → ObsHistory) : 0 ≤ X s :=
    integral_nonneg (fun t => mul_nonneg (by unfold retention; positivity) (sq_nonneg _))
  have hi : Integrable X (sampleLaw (Pseq n) n) :=
    (critical_survival_weighted_error_integrable_prod c (Pseq n) (hP n) a n
      (by linarith [hh.2, c.x0_le]) (by linarith [hh.1])).integral_prod_left
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall hX) hi (ε * Real.log n)
  have hsub : {s : Fin n → ObsHistory | ε < X s / Real.log n} ⊆
      {s | ε * Real.log n ≤ X s} := by
    intro s hs
    exact ((lt_div_iff₀ hl).mp hs).le
  have hb := (mul_le_mul_of_nonneg_left (measureReal_mono hsub (by finiteness))
    (mul_pos hε hl).le).trans hm
  change (sampleLaw (Pseq n) n).real {s | ε < X s / Real.log n} ≤
    (∫ s, X s ∂sampleLaw (Pseq n) n) / Real.log n / ε
  calc
    _ ≤ (∫ s, X s ∂sampleLaw (Pseq n) n) / (ε * Real.log n) :=
      (le_div_iff₀ (mul_pos hε hl)).2 (by simpa only [mul_comm] using hb)
    _ = _ := by ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
