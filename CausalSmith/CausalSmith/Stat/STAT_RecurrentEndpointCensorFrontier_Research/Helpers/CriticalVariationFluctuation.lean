module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalAsymptotics
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVariationMean
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Localized critical optional-variation fluctuations

Roadmap (27)--(29): retain the time-dependent linear risk floor when localizing
squared recurrence coefficients. Conditional Poisson isometry then controls
the optional-minus-predictable variation without independence of KM and risk.
The relative-risk event and predictable-variation limit remain separate steps.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Summing fourth powers removes one inverse-risk factor, including at zero risk. -/
-- @node: recurrenceSubjectWeight_sum_fourth
lemma recurrenceSubjectWeight_sum_fourth (c : ClassConstants) (h : ℝ)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (t : ℝ) :
    (∑ i : Fin n, recurrenceSubjectWeight c h a s i t ^ 4) =
      continuationWeight (holderOrder c) h t ^ 4 * deathKMLeft a s t ^ 4 *
        invRisk a s t ^ 3 := by
  classical
  simp only [recurrenceSubjectWeight, ite_pow, zero_pow (by decide : 4 ≠ 0)]
  rw [recurrence_atRisk_sum]
  by_cases hz : riskSet a s t = 0
  · simp [invRisk, hz]
  · have hc : (riskSet a s t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz
    simp only [invRisk, hz, ↓reduceIte]
    field_simp

/-- The terminal inverse-cube energy has only an inverse-square bandwidth cost. -/
-- @node: critical_terminal_inverse_cube_integral
lemma critical_terminal_inverse_cube_integral {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫ t in (0 : ℝ)..(1 - h), ((1 - t) ^ 3)⁻¹) = (h⁻¹ ^ 2 - 1) / 2 := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => (x ^ 3)⁻¹) 1]
  simp only [sub_sub_cancel, sub_zero]
  have hz : (0 : ℝ) ∉ Set.uIcc h 1 := by
    rw [Set.uIcc_of_le hh1]
    simp only [Set.mem_Icc, not_and]
    intro he
    linarith
  have he := integral_rpow (a := h) (b := 1) (r := (-3 : ℝ))
    (Or.inr ⟨by norm_num, hz⟩)
  have hp (x : ℝ) : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
    norm_num [Real.rpow_neg_eq_inv_rpow, inv_pow]
  simp_rw [hp] at he
  rw [he]
  norm_num
  ring

/-- The localization keeps precisely the squared actual recurrence coefficient
where the empirical risk exceeds a sample-size times terminal-distance floor. -/
-- @node: criticalLocalizedVariationWeight
noncomputable def criticalLocalizedVariationWeight (c : ClassConstants) (a : Arm)
    {n : ℕ} (r : ℝ) (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) : ℝ :=
  if (n : ℝ) * r * (1 - t) ≤
      riskSet a (fun j => recurrenceExposureHistory (e j)) t then
    criticalRecurrenceVariationWeight c a e i t else 0

/-- Localization by exposure risk preserves joint measurability. -/
-- @node: measurable_criticalLocalizedVariationWeight
@[fun_prop]
lemma measurable_criticalLocalizedVariationWeight (c : ClassConstants) (a : Arm)
    {n : ℕ} (r : ℝ) (i : Fin n) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      criticalLocalizedVariationWeight c a r p.1 i p.2) := by
  unfold criticalLocalizedVariationWeight
  apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop))
    (by fun_prop) measurable_const

/-- The localized weights remain bounded, supplying the isometry's integrability. -/
-- @node: criticalLocalizedVariationWeight_abs_le
lemma criticalLocalizedVariationWeight_abs_le (c : ClassConstants) (a : Arm)
    {n : ℕ} (hn : 0 < n) (r : ℝ) (e : Fin n → Arm × (ℝ × ENNReal))
    (i : Fin n) (t : ℝ) :
    |criticalLocalizedVariationWeight c a r e i t| ≤ weightEnvelope c ^ 2 := by
  unfold criticalLocalizedVariationWeight
  split_ifs
  · exact criticalRecurrenceVariationWeight_abs_le c a hn e i t
  · simp only [abs_zero]; positivity

/-- Localized fourth-power energy retains the inverse cube of terminal distance,
rather than replacing the whole time interval by its endpoint risk. -/
-- @node: criticalLocalizedVariationWeight_energy_density_le
lemma criticalLocalizedVariationWeight_energy_density_le (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (e : Fin n → Arm × (ℝ × ENNReal)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1 - bandwidth c n)) :
    (∑ i : Fin n, criticalLocalizedVariationWeight c a r e i t ^ 2) * P.lam a t ≤
      (weightEnvelope c ^ 4 * c.lambdaMax / ((n : ℝ) ^ 3 * r ^ 3)) *
        ((1 - t) ^ 3)⁻¹ := by
  let s := fun j => recurrenceExposureHistory (e j)
  have hh := bandwidth_pos_and_le_cap c hn
  have hx : 0 < 1 - t := by linarith [ht.2, hh.1]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hR : 0 < (n : ℝ) * r * (1 - t) := by positivity
  have hl := hP.recurrenceBounds a t ⟨ht.1, by linarith [ht.2, hh.1]⟩
  have hl0 : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans hl.1
  by_cases hc : (n : ℝ) * r * (1 - t) ≤ riskSet a s t
  · have hRisk : riskSet a s t ≠ 0 := by
      exact_mod_cast (hR.trans_le hc).ne'
    have hi : invRisk a s t ≤ ((n : ℝ) * r * (1 - t))⁻¹ := by
      simp only [invRisk, if_neg hRisk]
      exact inv_anti₀ hR hc
    have hi0 := (recurrence_invRisk_mem_Icc a s t).1
    have hw := continuationWeight_abs_le_coeffSum (holderOrder c) hh.1 (t := t)
    change |continuationWeight (holderOrder c) (bandwidth c n) t| ≤ weightEnvelope c at hw
    have hW : 0 ≤ weightEnvelope c := by unfold weightEnvelope continuationNorm; positivity
    have hw4 : continuationWeight (holderOrder c) (bandwidth c n) t ^ 4 ≤
        weightEnvelope c ^ 4 := by
      simpa only [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) hw 4
    have hk := deathKMLeft_mem_Icc a s t
    have hk4 : deathKMLeft a s t ^ 4 ≤ 1 := by
      simpa using pow_le_pow_left₀ hk.1 hk.2 4
    have heq : (∑ i : Fin n, criticalLocalizedVariationWeight c a r e i t ^ 2) =
        continuationWeight (holderOrder c) (bandwidth c n) t ^ 4 *
          deathKMLeft a s t ^ 4 * invRisk a s t ^ 3 := by
      change (n : ℝ) * r * (1 - t) ≤ riskSet a (fun j => recurrenceExposureHistory (e j)) t at hc
      simp only [criticalLocalizedVariationWeight, hc, if_true,
        criticalRecurrenceVariationWeight, if_pos ht.2, ← pow_mul]
      simp only [show (2 : ℕ) * 2 = 4 by norm_num]
      exact recurrenceSubjectWeight_sum_fourth c _ a s t
    rw [heq]
    calc
      _ ≤ weightEnvelope c ^ 4 * 1 *
          (((n : ℝ) * r * (1 - t))⁻¹) ^ 3 * c.lambdaMax := by
        gcongr
        exact hl.2
      _ = _ := by simp only [mul_pow, mul_inv_rev, inv_pow]; ring
  · change ¬ (n : ℝ) * r * (1 - t) ≤ riskSet a (fun j => recurrenceExposureHistory (e j)) t at hc
    simp only [criticalLocalizedVariationWeight, hc, if_false, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, zero_mul]
    have hL := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
    positivity

/-- Each exposure array's localized conditional energy satisfies roadmap (28)'s
inverse-cubic sample and inverse-square bandwidth bound. -/
-- @node: criticalLocalizedVariationWeight_integrated_energy_le
lemma criticalLocalizedVariationWeight_integrated_energy_le (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (e : Fin n → Arm × (ℝ × ENNReal)) :
    (∑ i : Fin n, ∫ t, criticalLocalizedVariationWeight c a r e i t ^ 2
      ∂recurrenceIntensity P a) ≤
      weightEnvelope c ^ 4 * c.lambdaMax /
        ((n : ℝ) ^ 3 * r ^ 3 * bandwidth c n ^ 2) := by
  let : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  have hh := bandwidth_pos_and_le_cap c hn
  have hh1 : bandwidth c n ≤ 1 := hh.2.trans (by linarith [c.x0_le])
  let f := fun t => ∑ i : Fin n, criticalLocalizedVariationWeight c a r e i t ^ 2
  have hi (i : Fin n) : Integrable (fun t => criticalLocalizedVariationWeight c a r e i t ^ 2)
      (recurrenceIntensity P a) := by
    apply Integrable.of_bound
      (((measurable_criticalLocalizedVariationWeight c a r i).comp
        (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
      ((weightEnvelope c ^ 2) ^ 2)
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [Function.comp_def, id_eq, sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (criticalLocalizedVariationWeight_abs_le c a hn r e i t) 2
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  have htrunc : (∫ t, f t ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..(1 - bandwidth c n), f t * P.lam a t := by
    have heq : (fun t => if t ≤ 1 - bandwidth c n then f t else 0) = f := by
      funext t
      by_cases ht : t ≤ 1 - bandwidth c n
      · simp [ht]
      · simp [f, criticalLocalizedVariationWeight, criticalRecurrenceVariationWeight, ht]
    calc
      _ = ∫ t, (if t ≤ 1 - bandwidth c n then f t else 0) ∂recurrenceIntensity P a := by rw [heq]
      _ = _ := recurrenceIntensity_integral_truncated P hP.poissonRecurrence a f
        (by linarith) (by linarith)
  change (∫ t, f t ∂recurrenceIntensity P a) ≤ _
  rw [htrunc]
  let K := weightEnvelope c ^ 4 * c.lambdaMax / ((n : ℝ) ^ 3 * r ^ 3)
  have hL : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hc : ContinuousOn (fun t : ℝ => ((1 - t) ^ 3)⁻¹)
      (Icc (0 : ℝ) (1 - bandwidth c n)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    exact pow_ne_zero 3 (by linarith [ht.2, hh.1])
  have hg : IntervalIntegrable (fun t : ℝ => K * ((1 - t) ^ 3)⁻¹)
      volume 0 (1 - bandwidth c n) := by
    apply (hc.const_mul K).intervalIntegrable_of_Icc
    linarith
  have hfi : IntervalIntegrable (fun t => f t * P.lam a t)
      volume 0 (1 - bandwidth c n) := by
    have hlam : IntervalIntegrable (P.lam a) volume 0 (1 - bandwidth c n) :=
      (poissonRecurrence_intervalIntegrable P hP.poissonRecurrence a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 1 - bandwidth c n)]
      exact Set.Icc_subset_Icc le_rfl (by linarith))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at hlam ⊢
    have hm : Measurable f := by
      dsimp [f]
      exact Finset.measurable_sum _ (fun i _ =>
        ((measurable_criticalLocalizedVariationWeight c a r i).comp
          (measurable_const.prodMk measurable_id)).pow_const 2)
    apply hlam.bdd_mul (c := (n : ℝ) * (weightEnvelope c ^ 2) ^ 2)
      hm.aestronglyMeasurable.restrict
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    calc
      _ ≤ ∑ _i : Fin n, (weightEnvelope c ^ 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (criticalLocalizedVariationWeight_abs_le c a hn r e i t) 2
      _ = _ := by simp
  have hb := intervalIntegral.integral_mono_on (by linarith : (0 : ℝ) ≤ 1 - bandwidth c n)
    hfi hg (fun t ht => criticalLocalizedVariationWeight_energy_density_le c P hP a hn hr e ht)
  calc
    _ ≤ ∫ t in (0 : ℝ)..(1 - bandwidth c n), K * ((1 - t) ^ 3)⁻¹ := hb
    _ = K * ((bandwidth c n)⁻¹ ^ 2 - 1) / 2 := by
      rw [intervalIntegral.integral_const_mul, critical_terminal_inverse_cube_integral hh.1 hh1]
      ring
    _ ≤ K * (bandwidth c n)⁻¹ ^ 2 := by
      nlinarith [mul_nonneg hK (sq_nonneg (bandwidth c n)⁻¹)]
    _ = _ := by dsimp [K]; simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]; ring

/-- Conditional Poisson isometry proves the localized optional-variation second
moment bound (28) uniformly over all model laws. -/
-- @node: criticalLocalizedVariationScore_secondMoment_le
lemma criticalLocalizedVariationScore_secondMoment_le (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun z : Fin n → LatentSubject => recurrenceJointExposureScore P a n
      (criticalLocalizedVariationWeight c a r)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2) (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject, recurrenceJointExposureScore P a n
      (criticalLocalizedVariationWeight c a r)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) ≤
      weightEnvelope c ^ 4 * c.lambdaMax /
        ((n : ℝ) ^ 3 * r ^ 3 * bandwidth c n ^ 2) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  have hp := recurrenceJointExposure_bounded_energy_integrable P hP.poissonRecurrence a n
    (criticalLocalizedVariationWeight c a r) (measurable_criticalLocalizedVariationWeight c a r)
    (weightEnvelope c ^ 2) (criticalLocalizedVariationWeight_abs_le c a hn r)
  obtain ⟨hi, he⟩ := recurrenceJointExposureScore_latent_secondMoment c P hP a n
    (criticalLocalizedVariationWeight c a r)
    (measurable_criticalLocalizedVariationWeight c a r) hp
  refine ⟨hi, ?_⟩
  rw [he]
  have henergy := (recurrenceJointExposure_energy_conditions P a n
    (criticalLocalizedVariationWeight c a r)
    (measurable_criticalLocalizedVariationWeight c a r) hp).2
  calc
    _ ≤ ∫ _e : Fin n → Arm × (ℝ × ENNReal),
        weightEnvelope c ^ 4 * c.lambdaMax /
          ((n : ℝ) ^ 3 * r ^ 3 * bandwidth c n ^ 2)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
      integral_mono henergy (integrable_const _)
        (criticalLocalizedVariationWeight_integrated_energy_le c P hP a hn hr)
    _ = _ := by simp

/-- The deterministic normalized second-moment scale in (29) vanishes. -/
-- @node: critical_variation_fluctuation_scale_tendsto_zero
lemma critical_variation_fluctuation_scale_tendsto_zero (c : ClassConstants)
    (hk : c.kappa = 1) :
    Tendsto (fun n : ℕ =>
      1 / ((n : ℝ) * bandwidth c n ^ 2 * (Real.log n) ^ 2)) atTop (nhds 0) := by
  have hi := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  have ht := (critical_log_div_sample_bandwidth_square_tendsto_zero c hk).mul (hi.pow 3)
  apply (show Tendsto (fun n : ℕ => Real.log n / ((n : ℝ) * bandwidth c n ^ 2) *
      (Real.log n)⁻¹ ^ 3) atTop (nhds 0) by simpa using ht).congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hh := (bandwidth_pos_and_le_cap c (show 0 < n by omega)).1
  have hl : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) (one_le_log_sampleSize hn)
  field_simp

/-- Chebyshev and the critical bandwidth rate close the localized form of (29)
for arbitrary triangular laws, without a new premise on those laws. -/
-- @node: criticalLocalizedVariationScore_triangular_probability_tendsto_zero
lemma criticalLocalizedVariationScore_triangular_probability_tendsto_zero
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => (Pseq n).latent)).real {z |
      ε < |((n : ℝ) / Real.log n) * recurrenceJointExposureScore (Pseq n) a n
        (criticalLocalizedVariationWeight c a r)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|}) atTop (nhds 0) := by
  let C := weightEnvelope c ^ 4 * c.lambdaMax / (r ^ 3 * ε ^ 2)
  have ht := (critical_variation_fluctuation_scale_tendsto_zero c hk).const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [mul_zero] using ht)
  filter_upwards [eventually_ge_atTop 3] with n hn
  let P := Pseq n
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let F := fun z : Fin n → LatentSubject => recurrenceJointExposureScore P a n
    (criticalLocalizedVariationWeight c a r)
    (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
    (fun j => (z j).recur a)
  let q := (n : ℝ) / Real.log n
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hh := (bandwidth_pos_and_le_cap c hn0).1
  have hl : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) (one_le_log_sampleSize hn)
  obtain ⟨hi, hb⟩ := criticalLocalizedVariationScore_secondMoment_le c P (hP n) a hn0 hr
  have hm := mul_meas_ge_le_integral_of_nonneg
    (f := fun z => q ^ 2 * F z ^ 2)
    (Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    (hi.const_mul (q ^ 2)) (ε ^ 2)
  have hsub : {z | ε < |q * F z|} ⊆ {z | ε ^ 2 ≤ q ^ 2 * F z ^ 2} := by
    intro z hz
    change ε < |q * F z| at hz
    change ε ^ 2 ≤ q ^ 2 * F z ^ 2
    have he := sq_abs (q * F z)
    rw [mul_pow] at he
    nlinarith [abs_nonneg (q * F z)]
  have hmono : (Measure.pi (fun _ : Fin n => P.latent)).real {z | ε < |q * F z|} ≤
      (Measure.pi (fun _ : Fin n => P.latent)).real {z | ε ^ 2 ≤ q ^ 2 * F z ^ 2} :=
    measureReal_mono hsub (by finiteness)
  have hb' : (Measure.pi (fun _ : Fin n => P.latent)).real {z | ε < |q * F z|} * ε ^ 2 ≤
      q ^ 2 * (weightEnvelope c ^ 4 * c.lambdaMax /
        ((n : ℝ) ^ 3 * r ^ 3 * bandwidth c n ^ 2)) := by
    calc
      _ ≤ ∫ z, q ^ 2 * F z ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent) :=
        (mul_le_mul_of_nonneg_right hmono (sq_nonneg ε)).trans
          (by simpa only [mul_comm] using hm)
      _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hb (sq_nonneg q)
  change (Measure.pi (fun _ : Fin n => P.latent)).real {z | ε < |q * F z|} ≤ _
  apply le_of_mul_le_mul_right ?_ (sq_pos_of_pos hε)
  calc
    _ ≤ q ^ 2 * (weightEnvelope c ^ 4 * c.lambdaMax /
        ((n : ℝ) ^ 3 * r ^ 3 * bandwidth c n ^ 2)) := hb'
    _ = (C * (1 / ((n : ℝ) * bandwidth c n ^ 2 * Real.log n ^ 2))) * ε ^ 2 := by
      dsimp [q, C]
      field_simp

/-- On the estimation interval, a linear empirical risk floor makes the
localized squared recurrence coefficient identical to the original coefficient. -/
-- @node: criticalLocalizedVariationWeight_eq_original
lemma criticalLocalizedVariationWeight_eq_original (c : ClassConstants) (a : Arm)
    {n : ℕ} (r : ℝ) (e : Fin n → Arm × (ℝ × ENNReal))
    (hfloor : ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n), (n : ℝ) * r * (1 - t) ≤
      riskSet a (fun j => recurrenceExposureHistory (e j)) t)
    (i : Fin n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 - bandwidth c n)) :
    criticalLocalizedVariationWeight c a r e i t = criticalRecurrenceVariationWeight c a e i t := by
  exact if_pos (hfloor t ht)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
