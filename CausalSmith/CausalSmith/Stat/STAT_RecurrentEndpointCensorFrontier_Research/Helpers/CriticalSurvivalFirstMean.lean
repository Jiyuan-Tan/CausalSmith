module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalSurvivalIntegrated

/-!
# First-mean critical survival control

The integrated squared survival error from roadmap (8) controls the absolute
survival error under the singular inverse-retention weight in (14). A Young
inequality with an arbitrary positive tolerance avoids any independence claim
about the KM estimator and risk sets. The resulting normalized absolute error
vanishes in probability along every triangular model-law sequence.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- Every absolute power of the sample's KM error is integrable against
inverse retention on a strict horizon, by the unit-range survival bounds. -/
-- @node: critical_survival_weighted_abs_pow_integrableOn
lemma critical_survival_weighted_abs_pow_integrableOn
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) (k : ℕ)
    {T : ℝ} (hT : 0 ≤ T) (hT1 : T < 1) :
    IntegrableOn (fun t => (retention P a t)⁻¹ *
      |deathKMLeft a s t - survival P a t| ^ k) (Icc (0 : ℝ) T) := by
  let g := (Icc (0 : ℝ) 1).piecewise (survival P a) (fun _ => 0)
  have hg : Measurable g := (modelClass_survival_continuousOn c P hP a).measurable_piecewise
    continuousOn_const measurableSet_Icc
  have hm : Measurable (fun t => |deathKMLeft a s t - g t| ^ k) :=
    (((measurable_recurrenceDeathKMLeft_joint a).comp
      (measurable_const.prodMk measurable_id)).sub hg).abs.pow_const k
  have hb : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      ‖|deathKMLeft a s t - g t| ^ k‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hT1.le⟩
    have hk := deathKMLeft_mem_Icc a s t
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht'
    have he : |deathKMLeft a s t - survival P a t| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)],
        by linarith [hk.1, hk.2, hs.1, hs.2, Real.exp_pos (-c.dMax)]⟩
    simp only [g, Set.piecewise, if_pos ht', Real.norm_eq_abs, abs_pow, abs_abs]
    exact pow_le_one₀ (abs_nonneg _) he
  apply ((inv_retention_integrableOn c P hP a hT hT1).bdd_mul
    hm.aestronglyMeasurable hb).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hT1.le⟩
  simp [g, ht', mul_comm]

/-- A pathwise weighted Young inequality transfers squared survival error
to absolute survival error with any positive tolerance. -/
-- @node: critical_survival_weighted_absolute_error_le
lemma critical_survival_weighted_absolute_error_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) {T η : ℝ}
    (hT : 0 ≤ T) (hT1 : T < 1) (hη : 0 < η) :
    (∫ t in Icc (0 : ℝ) T, (retention P a t)⁻¹ *
      |deathKMLeft a s t - survival P a t|) ≤
    η * (∫ t in Icc (0 : ℝ) T, (retention P a t)⁻¹) +
      (∫ t in Icc (0 : ℝ) T, (retention P a t)⁻¹ *
        (deathKMLeft a s t - survival P a t) ^ 2) / η := by
  have hi := inv_retention_integrableOn c P hP a hT hT1
  have hi1 := critical_survival_weighted_abs_pow_integrableOn c P hP a s 1 hT hT1
  have hi2 := critical_survival_weighted_abs_pow_integrableOn c P hP a s 2 hT hT1
  simp only [pow_one] at hi1
  simp only [sq_abs] at hi2
  calc
    _ ≤ ∫ t in Icc (0 : ℝ) T, η * (retention P a t)⁻¹ +
        ((retention P a t)⁻¹ * (deathKMLeft a s t - survival P a t) ^ 2) / η := by
      apply integral_mono hi1 ((hi.const_mul η).add (hi2.div_const η))
      intro t
      have hy : |deathKMLeft a s t - survival P a t| ≤
          η + (deathKMLeft a s t - survival P a t) ^ 2 / η := by
        rw [← sub_le_iff_le_add', le_div_iff₀ hη]
        have hsq := sq_nonneg (|deathKMLeft a s t - survival P a t| - η)
        simp only [sub_sq, sq_abs] at hsq
        nlinarith [mul_nonneg hη.le (abs_nonneg
          (deathKMLeft a s t - survival P a t))]
      have hb := mul_le_mul_of_nonneg_left hy
        (show 0 ≤ (retention P a t)⁻¹ by unfold retention; positivity)
      convert hb using 1 <;> dsimp only [Pi.add_apply] <;> ring
    _ = _ := by rw [integral_add (hi.const_mul η) (hi2.div_const η),
      integral_const_mul, integral_div]

/-- The inverse-retention-weighted absolute survival error, normalized by
log sample size, vanishes in probability uniformly along triangular laws.
This supplies first-order survival control under the oracle variance integral. -/
-- @node: critical_survival_weighted_absolute_probability_triangular_tendsto_zero
lemma critical_survival_weighted_absolute_probability_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < (∫ t in Icc (0 : ℝ) (1 - bandwidth c n),
        (retention (Pseq n) a t)⁻¹ *
          |deathKMLeft a s t - survival (Pseq n) a t|) / Real.log n})
      atTop (nhds 0) := by
  let M := reciprocalRetentionEnvelope c * varianceRateEnvelope c
  have hM : 0 < M := mul_pos (reciprocalRetentionEnvelope_pos c)
    (varianceRateEnvelope_pos c)
  let η := ε / (2 * (M + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηM : η * M ≤ ε / 2 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (M + 1))).2
    nlinarith [hε.le]
  have ht := critical_survival_weighted_error_probability_triangular_tendsto_zero
    c hk Pseq hP a (mul_pos hη (half_pos hε))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop 3] with n hn
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply measureReal_mono _ (by finiteness)
  intro s hs
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hl : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num)
    (one_le_log_sampleSize hn)
  have hb := div_le_div_of_nonneg_right
    (critical_survival_weighted_absolute_error_le c (Pseq n) (hP n) a s
      (T := 1 - bandwidth c n) (η := η)
      (by linarith [hh.2, c.x0_le]) (by linarith [hh.1]) hη) hl.le
  have hm := mul_le_mul_of_nonneg_left
    (critical_retention_integral_div_log_le c hk (Pseq n) (hP n) a hn) hη.le
  have hm' : η * (∫ t in Icc (0 : ℝ) (1 - bandwidth c n),
      (retention (Pseq n) a t)⁻¹) / Real.log n ≤ ε / 2 := by
    simpa only [mul_div_assoc] using hm.trans hηM
  change ε < _ / Real.log n at hs
  change η * (ε / 2) < _ / Real.log n
  rw [add_div, div_right_comm] at hb
  rw [mul_comm η, ← lt_div_iff₀ hη]
  linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
