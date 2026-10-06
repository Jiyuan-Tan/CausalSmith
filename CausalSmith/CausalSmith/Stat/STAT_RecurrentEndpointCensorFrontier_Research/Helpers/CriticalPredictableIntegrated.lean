module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalEmpiricalRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalPredictableComparison
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalSurvivalFirstMean

/-!
# Integrated predictable-variation comparison

Roadmap (14) only needs survival consistency under the oracle integral.
The KM unit-range bound gives a bounded survival ratio without requiring
uniform survival consistency. Relative risk control then bounds the actual
predictable-energy error by the inverse-retention-weighted absolute survival
error and the relative risk tolerance. All integrability is model-derived.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A bounded nonnegative survival ratio allows an arbitrary survival error;
only the risk ratio needs the half-unit localization. -/
-- @node: critical_bounded_squared_ratio_error_le
lemma critical_bounded_squared_ratio_error_le {x y B ε : ℝ}
    (hx : 0 ≤ x) (hxB : x ≤ B) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hye : |y - 1| ≤ ε) :
    |x ^ 2 / y - 1| ≤ 2 * (B + 1) * |x - 1| + 2 * ε := by
  have hB : 0 ≤ B := hx.trans hxB
  have hyb := abs_le.mp hye
  have hy : 0 < y := by linarith
  have hx2 : |x ^ 2 - 1| ≤ (B + 1) * |x - 1| := by
    rw [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring,
      abs_mul, abs_of_nonneg (by linarith : 0 ≤ x + 1)]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have he : |x ^ 2 - y| ≤ (B + 1) * |x - 1| + ε := by
    calc
      _ = |(x ^ 2 - 1) - (y - 1)| := by congr 1; ring
      _ ≤ |x ^ 2 - 1| + |y - 1| := abs_sub _ _
      _ ≤ _ := add_le_add hx2 hye
  rw [show x ^ 2 / y - 1 = (x ^ 2 - y) / y by field_simp,
    abs_div, abs_of_pos hy]
  apply (div_le_iff₀ hy).2
  have hb := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ y by linarith)
    (show 0 ≤ 2 * (B + 1) * |x - 1| + 2 * ε by positivity)
  nlinarith

/-- The genuine empirical recurrence density is controlled using absolute
survival error, with a law-independent coefficient and singular retention
weight. There is no survival-supremum hypothesis. -/
-- @node: critical_recurrence_energy_density_absolute_error_le
lemma critical_recurrence_energy_density_absolute_error_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory) {h t ε : ℝ}
    (hh : 0 < h) (ht : t ∈ Icc (0 : ℝ) 1) (ht1 : t < 1)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hRisk : |(riskSet a s t : ℝ) /
      ((n : ℝ) * (P.p a * survival P a t * retention P a t)) - 1| ≤ ε) :
    |(n : ℝ) * ((∑ i : Fin n, recurrenceSubjectWeight c h a s i t ^ 2) * P.lam a t) -
      continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t /
        (P.p a * retention P a t)| ≤
      (2 * (Real.exp c.dMax + 1) * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin) *
        ((retention P a t)⁻¹ * |deathKMLeft a s t - survival P a t| +
          ε * (retention P a t)⁻¹) := by
  have hs : 0 < survival P a t := Real.exp_pos _
  have hsB := survival_bounds_of_deathBounds c P hP.deathBounds a ht
  have hg := retention_pos_of_modelClass c P hP a t ht.1 ht1
  have hp := c.pMin_pos.trans_le (hP.treatmentOverlap a)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq : 0 < (n : ℝ) * (P.p a * survival P a t * retention P a t) := by positivity
  have hy : 0 < (riskSet a s t : ℝ) := by
    have hb := (abs_le.mp hRisk).1
    have : 0 < (riskSet a s t : ℝ) /
        ((n : ℝ) * (P.p a * survival P a t * retention P a t)) := by linarith
    exact (div_pos_iff.mp this).resolve_right (by
      intro hneg
      exact (not_lt_of_ge hq.le) hneg.2) |>.1
  have hz : riskSet a s t ≠ 0 := by exact_mod_cast hy.ne'
  have hxB : deathKMLeft a s t / survival P a t ≤ Real.exp c.dMax := by
    apply (div_le_iff₀ hs).2
    have hb := mul_le_mul_of_nonneg_left hsB.1 (Real.exp_pos c.dMax).le
    have he : Real.exp c.dMax * Real.exp (-c.dMax) = 1 := by
      rw [← Real.exp_add]; simp
    rw [he] at hb
    exact (deathKMLeft_mem_Icc a s t).2.trans hb
  have hr := critical_bounded_squared_ratio_error_le
    (div_nonneg (deathKMLeft_mem_Icc a s t).1 hs.le) hxB hε hε2 hRisk
  let W := continuationWeight (holderOrder c) h t ^ 2 * P.lam a t /
    (P.p a * retention P a t)
  have hlMax : 0 < c.lambdaMax := c.lambdaMin_pos.trans c.lambdaMin_lt
  have hl0 : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hratio : survival P a t * |deathKMLeft a s t / survival P a t - 1| =
      |deathKMLeft a s t - survival P a t| := by
    rw [show deathKMLeft a s t / survival P a t - 1 =
      (deathKMLeft a s t - survival P a t) / survival P a t by field_simp,
      abs_div, abs_of_pos hs]
    field_simp
  rw [recurrenceSubjectWeight_sum_sq, invRisk, if_neg hz]
  have he : (n : ℝ) *
      (continuationWeight (holderOrder c) h t ^ 2 * deathKMLeft a s t ^ 2 *
        (riskSet a s t : ℝ)⁻¹ * P.lam a t) - W * survival P a t =
    (W * survival P a t) * ((deathKMLeft a s t / survival P a t) ^ 2 /
      ((riskSet a s t : ℝ) /
        ((n : ℝ) * (P.p a * survival P a t * retention P a t))) - 1) := by
    dsimp [W]; field_simp
  have hw : |continuationWeight (holderOrder c) h t| ≤ weightEnvelope c :=
    continuationWeight_abs_le_coeffSum (holderOrder c) hh
  have hw0 : 0 ≤ weightEnvelope c := by unfold weightEnvelope continuationNorm; positivity
  have hw2 : continuationWeight (holderOrder c) h t ^ 2 ≤ weightEnvelope c ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hw 2
  have hWb : W ≤ (weightEnvelope c ^ 2 * c.lambdaMax / c.pMin) * (retention P a t)⁻¹ := by
    dsimp [W]
    calc
      _ ≤ (weightEnvelope c ^ 2 * c.lambdaMax) / (P.p a * retention P a t) := by
        gcongr
        exact (hP.recurrenceBounds a t ht).2
      _ ≤ (weightEnvelope c ^ 2 * c.lambdaMax) / (c.pMin * retention P a t) := by
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos c.pMin_pos hg)
        exact mul_le_mul_of_nonneg_right (hP.treatmentOverlap a) hg.le
      _ = _ := by ring
  rw [show continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t /
      (P.p a * retention P a t) = W * survival P a t by dsimp [W]; ring]
  rw [he, abs_mul, abs_of_nonneg (mul_nonneg hW hs.le)]
  calc
    _ ≤ (W * survival P a t) *
        (2 * (Real.exp c.dMax + 1) *
          |deathKMLeft a s t / survival P a t - 1| + 2 * ε) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg hW hs.le)
    _ = W * (2 * (Real.exp c.dMax + 1) *
        |deathKMLeft a s t - survival P a t| + 2 * ε * survival P a t) := by
      rw [mul_add, show W * survival P a t *
          (2 * (Real.exp c.dMax + 1) *
            |deathKMLeft a s t / survival P a t - 1|) =
          W * (2 * (Real.exp c.dMax + 1)) *
            (survival P a t * |deathKMLeft a s t / survival P a t - 1|) by ring,
        hratio]; ring
    _ ≤ W * (2 * (Real.exp c.dMax + 1) *
        (|deathKMLeft a s t - survival P a t| + ε)) := by
      apply mul_le_mul_of_nonneg_left _ hW
      have hb := mul_le_mul_of_nonneg_left hsB.2 (show 0 ≤ 2 * ε by positivity)
      nlinarith [mul_nonneg (Real.exp_pos c.dMax).le hε]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_right hWb
        (show 0 ≤ 2 * (Real.exp c.dMax + 1) *
          (|deathKMLeft a s t - survival P a t| + ε) by positivity)
      convert hb using 1 <;> first | rfl | ring

/-- Integrating the empirical density bound retains the actual predictable
energy and its oracle, while replacing maximal survival control by the
inverse-retention-weighted first mean. -/
-- @node: critical_predictable_energy_absolute_error_le
lemma critical_predictable_energy_absolute_error_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory) {h ε : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hRisk : ∀ t ∈ Icc (0 : ℝ) (1 - h), |(riskSet a s t : ℝ) /
      ((n : ℝ) * (P.p a * survival P a t * retention P a t)) - 1| ≤ ε) :
    |(n : ℝ) * (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) -
      (∫ t in (0 : ℝ)..(1 - h), continuationWeight (holderOrder c) h t ^ 2 *
        survival P a t * P.lam a t / (P.p a * retention P a t))| ≤
      (2 * (Real.exp c.dMax + 1) * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin) *
        ((∫ t in Icc (0 : ℝ) (1 - h), (retention P a t)⁻¹ *
          |deathKMLeft a s t - survival P a t|) +
          ε * (∫ t in Icc (0 : ℝ) (1 - h), (retention P a t)⁻¹)) := by
  have hT : 0 ≤ 1 - h := by linarith
  let f := fun t => (n : ℝ) * ∑ i : Fin n,
    recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t
  let g := fun t => continuationWeight (holderOrder c) h t ^ 2 * survival P a t *
    P.lam a t / (P.p a * retention P a t)
  let K := 2 * (Real.exp c.dMax + 1) * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin
  have hf : IntervalIntegrable f volume 0 (1 - h) := by
    simpa only [f, Finset.sum_apply] using (IntervalIntegrable.sum Finset.univ (fun i _ =>
      recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable c P hP a s i hh hh1 2)).const_mul n
  have hg : IntervalIntegrable g volume 0 (1 - h) :=
    critical_oracle_density_intervalIntegrable c P hP a hh hh1
  have hi := inv_retention_integrableOn c P hP a hT (by linarith : 1 - h < 1)
  have ha := DeathCP.critical_survival_weighted_abs_pow_integrableOn c P hP a s 1
    hT (by linarith : 1 - h < 1)
  simp only [pow_one] at ha
  have he : (n : ℝ) * (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) =
      ∫ t in (0 : ℝ)..(1 - h), f t := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    intro i _
    exact recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable c P hP a s i hh hh1 2
  rw [he, ← intervalIntegral.integral_sub hf hg]
  calc
    _ ≤ ∫ t in (0 : ℝ)..(1 - h), |f t - g t| :=
      intervalIntegral.abs_integral_le_integral_abs hT
    _ = ∫ t in Icc (0 : ℝ) (1 - h), |f t - g t| := by
      rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]
    _ ≤ ∫ t in Icc (0 : ℝ) (1 - h), K *
        ((retention P a t)⁻¹ * |deathKMLeft a s t - survival P a t| +
          ε * (retention P a t)⁻¹) := by
      apply integral_mono_ae
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 (hf.sub hg).abs)
        ((ha.add (hi.const_mul ε)).const_mul K)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      dsimp [f, g, K]
      rw [← Finset.sum_mul]
      exact critical_recurrence_energy_density_absolute_error_le c P hP a hn s hh
        ⟨ht.1, by linarith [ht.2]⟩ (by linarith [ht.2]) hε hε2 (hRisk t ht)
    _ = _ := by
      rw [integral_const_mul, integral_add ha (hi.const_mul ε), integral_const_mul]

/-- Relative-risk control and the proved weighted absolute survival limit
close the stochastic comparison in roadmap (14), arm by arm. -/
-- @node: critical_predictable_arm_oracle_error_triangular_tendsto_zero
lemma critical_predictable_arm_oracle_error_triangular_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real {s |
      ε < |((n : ℝ) * (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - bandwidth c n),
        recurrenceSubjectWeight c (bandwidth c n) a s i t ^ 2 * (Pseq n).lam a t) -
        (∫ t in (0 : ℝ)..(1 - bandwidth c n),
          continuationWeight (holderOrder c) (bandwidth c n) t ^ 2 *
            survival (Pseq n) a t * (Pseq n).lam a t /
              ((Pseq n).p a * retention (Pseq n) a t))) / Real.log n|})
      atTop (nhds 0) := by
  let K := 2 * (Real.exp c.dMax + 1) * weightEnvelope c ^ 2 * c.lambdaMax / c.pMin
  let M := reciprocalRetentionEnvelope c * varianceRateEnvelope c
  have hW : 0 < weightEnvelope c := by unfold weightEnvelope continuationNorm; positivity
  have hK : 0 < K := by
    have hl := c.lambdaMin_pos.trans c.lambdaMin_lt
    have hp := c.pMin_pos
    dsimp [K]
    positivity
  have hM : 0 < M := mul_pos (reciprocalRetentionEnvelope_pos c)
    (varianceRateEnvelope_pos c)
  let δ := min (1 / 2 : ℝ) (ε / (2 * K * (M + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδM : K * (δ * M) ≤ ε / 2 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 2 * K * (M + 1))).mp
      (min_le_right (1 / 2 : ℝ) (ε / (2 * K * (M + 1))))
    change δ * (2 * K * (M + 1)) ≤ ε at hb
    nlinarith [mul_nonneg hK.le hδ.le]
  have hr := critical_relative_risk_triangular_tendsto c hk Pseq hP a hδ
  have ha := DeathCP.critical_survival_weighted_absolute_probability_triangular_tendsto_zero
    c hk Pseq hP a (ε := ε / (2 * K)) (div_pos hε (mul_pos (by norm_num) hK))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hr.add ha)
  filter_upwards [eventually_ge_atTop 3] with n hn
  letI : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply le_trans (measureReal_mono ?_ (by finiteness)) (measureReal_union_le _ _)
  intro s hs
  by_contra hne
  have hb := not_or.mp hne
  simp only [Set.mem_setOf_eq] at hb
  have hRisk : ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n), |(riskSet a s t : ℝ) /
      ((n : ℝ) * ((Pseq n).p a * survival (Pseq n) a t * retention (Pseq n) a t)) - 1| ≤ δ := by
    intro t ht
    exact le_of_not_gt (fun he => hb.1 ⟨t, ht, he⟩)
  have hAbs := le_of_not_gt hb.2
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hl : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num)
    (one_le_log_sampleSize hn)
  have he := div_le_div_of_nonneg_right
    (critical_predictable_energy_absolute_error_le c (Pseq n) (hP n) a
      (show 0 < n by omega) s hh.1 (by linarith [hh.2, c.x0_le]) hδ.le hδ2 hRisk) hl.le
  have hMass := mul_le_mul_of_nonneg_left
    (DeathCP.critical_retention_integral_div_log_le c hk (Pseq n) (hP n) a hn) hδ.le
  change δ * (_ / Real.log n) ≤ δ * M at hMass
  change _ ≤ K * (_ + _) / Real.log n at he
  rw [mul_div_assoc K, add_div, mul_div_assoc δ] at he
  have hBound := mul_le_mul_of_nonneg_left (add_le_add hAbs hMass) hK.le
  change _ ≤ K * (_ + _) at he
  have hSmall : K * (ε / (2 * K) + δ * M) ≤ ε := by
    have heq : K * (ε / (2 * K)) = ε / 2 := by field_simp
    rw [mul_add, heq]
    linarith
  have hFinal := he.trans (hBound.trans hSmall)
  change ε < |_ / Real.log n| at hs
  rw [abs_div, abs_of_pos hl] at hs
  exact (not_lt_of_ge hFinal) hs

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
