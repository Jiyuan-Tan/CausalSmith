module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessExplicitRisk
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Critical predictable variation comparison

Roadmap (14): relative risk and survival errors control the actual diagonal
recurrence energy relative to its deterministic oracle density. These are
pathwise estimates; the probabilities of the localization events and the
logarithmic asymptotics of the oracle integral remain separate obligations.
Roadmap (12) is proved directly from endpoint retention; its reciprocal
correction is integrable at zero and has a law-independent integral bound,
supplying the rho-term in the oracle expansion (13).
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Squaring the survival ratio and inverting the risk ratio preserves small
relative errors on the half-relative-risk event. -/
-- @node: critical_squared_ratio_error_le
lemma critical_squared_ratio_error_le {x y δ ε : ℝ}
    (hx : 0 ≤ x) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hxe : |x - 1| ≤ δ) (hye : |y - 1| ≤ ε) :
    |x ^ 2 / y - 1| ≤ 6 * δ + 2 * ε := by
  have hxb := abs_le.mp hxe
  have hyb := abs_le.mp hye
  have hy : 0 < y := by linarith
  have hx2 : |x ^ 2 - 1| ≤ 3 * δ := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr (show x ≤ 2 by linarith)) hδ]
    · nlinarith [mul_nonneg (sub_nonneg.mpr (show x ≤ 2 by linarith))
        (sub_nonneg.mpr (show x - 1 ≤ δ by linarith))]
  have he : |x ^ 2 - y| ≤ 3 * δ + ε := by
    calc
      _ = |(x ^ 2 - 1) - (y - 1)| := by congr 1; ring
      _ ≤ |x ^ 2 - 1| + |y - 1| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (x ^ 2 - 1) 0 (y - 1)
      _ ≤ _ := add_le_add hx2 hye
  rw [show x ^ 2 / y - 1 = (x ^ 2 - y) / y by field_simp, abs_div,
    abs_of_pos hy]
  apply (div_le_iff₀ hy).mpr
  have hb := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ y by linarith)
    (show 0 ≤ 6 * δ + 2 * ε by positivity)
  nlinarith

/-- The critical endpoint relative-retention error has the paper's half-unit
bound, uniformly down to the endpoint. -/
-- @node: critical_endpoint_retention_relative_error_le
lemma critical_endpoint_retention_relative_error_le (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {x : ℝ} (hx : 0 < x) (hx0 : x ≤ c.x0) :
    |retention P a (1 - x) / (P.g a * x) - 1| ≤ c.LG * x ^ c.rho ∧
      c.LG * x ^ c.rho ≤ 1 / 2 := by
  constructor
  · simpa only [hk, Real.rpow_one] using hP.endpointRetention a x hx hx0
  · exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx.le hx0 c.rho_pos.le) c.LG_pos.le).trans
        hP.tailEnvelopeSmall

/-- Inverting the actual relative-retention ratio gives exactly the
second-order reciprocal error used in roadmap (12). -/
-- @node: critical_endpoint_inverse_relative_error_le
lemma critical_endpoint_inverse_relative_error_le (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {x : ℝ} (hx : 0 < x) (hx0 : x ≤ c.x0) :
    |P.g a * x / retention P a (1 - x) - 1| ≤ 2 * c.LG * x ^ c.rho := by
  obtain ⟨he, hs⟩ := critical_endpoint_retention_relative_error_le c hk P hP a hx hx0
  have hr := critical_squared_ratio_error_le (x := 1) (δ := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (mul_nonneg c.LG_pos.le (Real.rpow_nonneg hx.le _)) hs (by norm_num) he
  simpa only [one_pow, one_div_div, mul_zero, zero_add, mul_assoc] using hr

/-- Subtracting the principal inverse-linear singularity leaves a power
with integrable exponent rho minus one, as required in roadmap (13). -/
-- @node: critical_endpoint_inverse_retention_remainder_le
lemma critical_endpoint_inverse_retention_remainder_le (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {x : ℝ} (hx : 0 < x) (hx0 : x ≤ c.x0) :
    |1 / retention P a (1 - x) - 1 / (P.g a * x)| ≤
      (2 * c.LG / P.g a) * x ^ (c.rho - 1) := by
  have hg : 0 < P.g a := c.gMin_pos.trans_le (hP.endpointCoefficientBounds a).1
  have hd : 0 < P.g a * x := mul_pos hg hx
  have he := critical_endpoint_inverse_relative_error_le c hk P hP a hx hx0
  have hid : 1 / retention P a (1 - x) - 1 / (P.g a * x) =
      (P.g a * x / retention P a (1 - x) - 1) / (P.g a * x) := by
    field_simp
  rw [hid, abs_div, abs_of_pos hd]
  calc
    _ ≤ (2 * c.LG * x ^ c.rho) / (P.g a * x) :=
      div_le_div_of_nonneg_right he hd.le
    _ = (2 * c.LG / P.g a) * x ^ (c.rho - 1) := by
      rw [Real.rpow_sub hx, Real.rpow_one]
      ring

/-- The reciprocal-tail remainder has a law-independent integrable envelope. -/
-- @node: critical_endpoint_inverse_retention_remainder_uniform_le
lemma critical_endpoint_inverse_retention_remainder_uniform_le (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {x : ℝ} (hx : 0 < x) (hx0 : x ≤ c.x0) :
    |1 / retention P a (1 - x) - 1 / (P.g a * x)| ≤
      (2 * c.LG / c.gMin) * x ^ (c.rho - 1) := by
  apply (critical_endpoint_inverse_retention_remainder_le c hk P hP a hx hx0).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) c.LG_pos.le) c.gMin_pos
    (hP.endpointCoefficientBounds a).1

/-- The endpoint reciprocal remainder is integrable all the way to zero;
no extra inverse-retention integrability premise is required. -/
-- @node: critical_endpoint_inverse_retention_remainder_intervalIntegrable
lemma critical_endpoint_inverse_retention_remainder_intervalIntegrable
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    IntervalIntegrable (fun x => 1 / retention P a (1 - x) - 1 / (P.g a * x))
      volume 0 c.x0 := by
  have henvelope := (intervalIntegral.intervalIntegrable_rpow'
    (r := c.rho - 1) (by linarith [c.rho_pos]) (a := 0) (b := c.x0)).const_mul
      (2 * c.LG / c.gMin)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le c.x0_pos.le] at henvelope ⊢
  apply henvelope.mono' (by
    have hm := (measurable_retention P a).comp (show Measurable (fun x : ℝ => 1 - x) by fun_prop)
    exact ((measurable_const.div hm).sub
      (measurable_const.div (measurable_const.mul measurable_id))).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa only [Real.norm_eq_abs] using
    critical_endpoint_inverse_retention_remainder_uniform_le c hk P hP a hx.1 hx.2

/-- The reciprocal-retention correction contributes a uniformly bounded
integral on every truncated endpoint region, the rho-term in roadmap (13). -/
-- @node: critical_endpoint_inverse_retention_remainder_integral_le
lemma critical_endpoint_inverse_retention_remainder_integral_le
    (c : ClassConstants) (hk : c.kappa = 1) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {h : ℝ} (hh : 0 ≤ h) (hh0 : h ≤ c.x0) :
    |∫ x in h..c.x0, 1 / retention P a (1 - x) - 1 / (P.g a * x)| ≤
      (2 * c.LG / c.gMin) * (c.x0 ^ c.rho / c.rho) := by
  have hf := (critical_endpoint_inverse_retention_remainder_intervalIntegrable c hk P hP a).mono_set
    (show uIcc h c.x0 ⊆ uIcc 0 c.x0 by
      rw [uIcc_of_le hh0, uIcc_of_le c.x0_pos.le]
      exact Icc_subset_Icc hh le_rfl)
  have hg := (intervalIntegral.intervalIntegrable_rpow' (r := c.rho - 1)
    (by linarith [c.rho_pos]) (a := h) (b := c.x0)).const_mul (2 * c.LG / c.gMin)
  calc
    _ ≤ ∫ x in h..c.x0, |1 / retention P a (1 - x) - 1 / (P.g a * x)| :=
      intervalIntegral.abs_integral_le_integral_abs hh0
    _ ≤ ∫ x in h..c.x0, (2 * c.LG / c.gMin) * x ^ (c.rho - 1) := by
      apply intervalIntegral.integral_mono_ae_restrict hh0 hf.abs hg
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (volume.restrict (Icc h c.x0)).ae_ne (0 : ℝ)] with x hx hxne
      exact critical_endpoint_inverse_retention_remainder_uniform_le c hk P hP a
        (lt_of_le_of_ne (hh.trans hx.1) (Ne.symm hxne)) hx.2
    _ = (2 * c.LG / c.gMin) * ((c.x0 ^ c.rho - h ^ c.rho) / c.rho) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith [c.rho_pos]))]
      simp only [sub_add_cancel]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _
        (div_nonneg (mul_nonneg (by norm_num) c.LG_pos.le) c.gMin_pos.le)
      apply div_le_div_of_nonneg_right _ c.rho_pos.le
      linarith [Real.rpow_nonneg hh c.rho]

/-- Roadmap (14), at the actual empirical density, including the signed
continuation weight through its square. -/
-- @node: critical_recurrence_energy_density_relative_error_le
lemma critical_recurrence_energy_density_relative_error_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory) {h t δ ε : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (ht1 : t < 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hKM : |deathKMLeft a s t / survival P a t - 1| ≤ δ)
    (hRisk : |(riskSet a s t : ℝ) /
      ((n : ℝ) * (P.p a * survival P a t * retention P a t)) - 1| ≤ ε) :
    |(n : ℝ) * ((∑ i : Fin n, recurrenceSubjectWeight c h a s i t ^ 2) * P.lam a t) -
      continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t /
        (P.p a * retention P a t)| ≤
      (6 * δ + 2 * ε) *
        (continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t /
          (P.p a * retention P a t)) := by
  have hs : 0 < survival P a t := Real.exp_pos _
  have hg := retention_pos_of_modelClass c P hP a t ht.1 ht1
  have hp := c.pMin_pos.trans_le (hP.treatmentOverlap a)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq : 0 < (n : ℝ) * (P.p a * survival P a t * retention P a t) := by positivity
  have hb := (abs_le.mp hRisk).1
  have hy : 0 < (riskSet a s t : ℝ) := by
    have : 0 < (riskSet a s t : ℝ) /
      ((n : ℝ) * (P.p a * survival P a t * retention P a t)) := by linarith
    exact (div_pos_iff.mp this).resolve_right (by
      intro hneg
      exact (not_lt_of_ge hq.le) hneg.2) |>.1
  have hz : riskSet a s t ≠ 0 := by exact_mod_cast hy.ne'
  have hratio := critical_squared_ratio_error_le
    (div_nonneg (deathKMLeft_mem_Icc a s t).1 hs.le) hδ hδ1 hε hε2 hKM hRisk
  let B := continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t /
    (P.p a * retention P a t)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hs.le)
      (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)) (by positivity)
  rw [recurrenceSubjectWeight_sum_sq, invRisk, if_neg hz]
  have he : (n : ℝ) *
      (continuationWeight (holderOrder c) h t ^ 2 * deathKMLeft a s t ^ 2 *
        (riskSet a s t : ℝ)⁻¹ * P.lam a t) - B =
    B * ((deathKMLeft a s t / survival P a t) ^ 2 /
      ((riskSet a s t : ℝ) /
        ((n : ℝ) * (P.p a * survival P a t * retention P a t))) - 1) := by
    dsimp [B]
    field_simp
  change |_ - B| ≤ (6 * δ + 2 * ε) * B
  rw [he, abs_mul, abs_of_nonneg hB]
  exact (mul_le_mul_of_nonneg_left hratio hB).trans_eq (mul_comm _ _)

/-- The oracle integral is finite at every positive bandwidth. Inverse
retention integrability is derived on the strict estimation horizon. -/
-- @node: critical_oracle_density_intervalIntegrable
lemma critical_oracle_density_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) :
    IntervalIntegrable (fun t => continuationWeight (holderOrder c) h t ^ 2 *
      survival P a t * P.lam a t / (P.p a * retention P a t)) volume 0 (1 - h) := by
  have hT : 0 ≤ 1 - h := by linarith
  have hi := inv_retention_integrableOn c P hP a hT (by linarith : 1 - h < 1)
  have hcont := (modelClass_survival_continuousOn c P hP a).mul
    (hP.recurrenceHolder a).1.continuousOn
  have hm := (measurable_recurrenceContinuationWeight c h).pow_const 2
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  have hmeas : AEStronglyMeasurable (fun t =>
      continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t / P.p a)
      (volume.restrict (Icc 0 (1 - h))) := by
    have hm' : AEStronglyMeasurable (fun t => continuationWeight (holderOrder c) h t ^ 2)
        (volume.restrict (Icc 0 (1 - h))) := hm.aestronglyMeasurable
    have hc : AEStronglyMeasurable (survival P a * P.lam a)
        (volume.restrict (Icc (0 : ℝ) 1)) :=
      hcont.aestronglyMeasurable measurableSet_Icc
    have hc' := hc.mono_measure (Measure.restrict_mono
      (Icc_subset_Icc le_rfl (by linarith : 1 - h ≤ 1)) le_rfl)
    simpa only [Pi.mul_apply, div_eq_mul_inv, mul_assoc] using (hm'.mul hc').mul_const (P.p a)⁻¹
  have hp := c.pMin_pos.trans_le (hP.treatmentOverlap a)
  have hb : ∀ᵐ t ∂volume.restrict (Icc 0 (1 - h)),
      ‖continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t /
        P.p a‖ ≤ weightEnvelope c ^ 2 * c.lambdaMax / P.p a := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
    have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht'
    have hl := hP.recurrenceBounds a t ht'
    have hw : |continuationWeight (holderOrder c) h t| ≤ weightEnvelope c :=
      continuationWeight_abs_le_coeffSum (holderOrder c) hh
    have hW : 0 ≤ weightEnvelope c := by unfold weightEnvelope continuationNorm; positivity
    have hw2 : continuationWeight (holderOrder c) h t ^ 2 ≤ weightEnvelope c ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hw 2
    have hl0 : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans hl.1
    have hs0 : 0 ≤ survival P a t := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤
      continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t / P.p a)]
    apply div_le_div_of_nonneg_right _ hp.le
    calc
      _ ≤ weightEnvelope c ^ 2 * 1 * c.lambdaMax := by
        gcongr
        · exact hs.2
        · exact hl.2
      _ = _ := by ring
  change Integrable _ (volume.restrict (Icc 0 (1 - h)))
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hi.bdd_mul hmeas hb

/-- Integrating (14) compares the genuine subject predictable variation to
its oracle without discarding support or inverse-risk dependence. -/
-- @node: critical_predictable_energy_relative_error_le
lemma critical_predictable_energy_relative_error_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory) {h δ ε : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hKM : ∀ t ∈ Icc (0 : ℝ) (1 - h),
      |deathKMLeft a s t / survival P a t - 1| ≤ δ)
    (hRisk : ∀ t ∈ Icc (0 : ℝ) (1 - h), |(riskSet a s t : ℝ) /
      ((n : ℝ) * (P.p a * survival P a t * retention P a t)) - 1| ≤ ε) :
    |(n : ℝ) * (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) -
      (∫ t in (0 : ℝ)..(1 - h), continuationWeight (holderOrder c) h t ^ 2 *
        survival P a t * P.lam a t / (P.p a * retention P a t))| ≤
      (6 * δ + 2 * ε) * (∫ t in (0 : ℝ)..(1 - h),
        continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t /
          (P.p a * retention P a t)) := by
  have hT : 0 ≤ 1 - h := by linarith
  let f := fun t => (n : ℝ) * ∑ i : Fin n,
    recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t
  let g := fun t => continuationWeight (holderOrder c) h t ^ 2 * survival P a t *
    P.lam a t / (P.p a * retention P a t)
  have hf : IntervalIntegrable f volume 0 (1 - h) := by
    simpa only [f, Finset.sum_apply] using (IntervalIntegrable.sum Finset.univ (fun i _ =>
      recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable c P hP a s i hh hh1 2)).const_mul n
  have hg : IntervalIntegrable g volume 0 (1 - h) :=
    critical_oracle_density_intervalIntegrable c P hP a hh hh1
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
    _ ≤ ∫ t in (0 : ℝ)..(1 - h), (6 * δ + 2 * ε) * g t := by
      apply intervalIntegral.integral_mono_on hT (hf.sub hg).abs (hg.const_mul _)
      intro t ht
      dsimp [f, g]
      rw [← Finset.sum_mul]
      exact critical_recurrence_energy_density_relative_error_le c P hP a hn s
        ⟨ht.1, by linarith [ht.2]⟩ (by linarith [ht.2]) hδ hδ1 hε hε2
        (hKM t ht) (hRisk t ht)
    _ = _ := intervalIntegral.integral_const_mul _ _

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
