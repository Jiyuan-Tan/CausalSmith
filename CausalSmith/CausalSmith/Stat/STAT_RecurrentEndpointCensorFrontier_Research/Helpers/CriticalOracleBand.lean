module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalDeathRemainder
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalNumerator
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRecurrenceWitness

/-!
# Bounded critical continuation-band correction

Roadmap (13): the continuation weight changes the terminal logarithmic
oracle integral by a uniformly bounded amount. The band has width h and
inverse retention is bounded by a constant divided by h there. Every
integrability assertion is derived from the model and positive bandwidth.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The terminal oracle density is integrable on every positive truncation,
by its already proved integrable remainder and inverse-linear principal term. -/
-- @node: critical_terminal_density_intervalIntegrable
lemma critical_terminal_density_intervalIntegrable (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {h : ℝ} (hh : 0 < h) (hh0 : h ≤ c.x0) :
    IntervalIntegrable (fun x => survival P a (1 - x) * P.lam a (1 - x) /
      retention P a (1 - x)) volume h c.x0 := by
  obtain ⟨C, hC, hb⟩ := critical_oracle_terminal_remainder_integral_uniform c hk
  have hr := (hb P hP a).1.mono_set (show uIcc h c.x0 ⊆ uIcc 0 c.x0 by
    rw [uIcc_of_le hh0, uIcc_of_le c.x0_pos.le]
    exact Icc_subset_Icc hh.le le_rfl)
  have hi : IntervalIntegrable (fun x : ℝ => x⁻¹) volume h c.x0 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hh0
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    exact (hh.trans_le hx.1).ne'
  have hp := hi.const_mul (survival P a 1 * P.lam a 1 / P.g a)
  convert hr.add hp using 1
  ext x
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual squared-weight correction has a constant over h envelope
throughout the continuation band, uniformly over the model class. -/
-- @node: critical_oracle_band_correction_density_le
lemma critical_oracle_band_correction_density_le (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {h x : ℝ} (hh : 0 < h) (hx : x ∈ Icc h (2 * h)) (hx1 : x ≤ 1) :
    |(continuationWeight (holderOrder c) h (1 - x) ^ 2 - 1) *
      (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x))| ≤
      ((weightEnvelope c ^ 2 + 1) * c.lambdaMax /
        min c.Gint (c.gMin / 2)) / h := by
  let r := min c.Gint (c.gMin / 2)
  have hr : 0 < r := lt_min c.Gint_pos (half_pos c.gMin_pos)
  have hxpos := hh.trans_le hx.1
  have ht : 1 - x ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hG := critical_retention_ge_linear c hk P hP a
    (show 1 - x ∈ Ico (0 : ℝ) 1 from ⟨ht.1, by linarith⟩)
  simp only [sub_sub_cancel] at hG
  have hrh : r * h ≤ retention P a (1 - x) :=
    (mul_le_mul_of_nonneg_left hx.1 hr.le).trans hG
  have hGp : 0 < retention P a (1 - x) := (mul_pos hr hh).trans_le hrh
  have hW : 0 ≤ weightEnvelope c := by unfold weightEnvelope continuationNorm; positivity
  have hw : |continuationWeight (holderOrder c) h (1 - x)| ≤ weightEnvelope c :=
    continuationWeight_abs_le_coeffSum (holderOrder c) hh
  have hw2 : continuationWeight (holderOrder c) h (1 - x) ^ 2 ≤ weightEnvelope c ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hw 2
  have hc : |continuationWeight (holderOrder c) h (1 - x) ^ 2 - 1| ≤
      weightEnvelope c ^ 2 + 1 := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (sq_nonneg (continuationWeight (holderOrder c) h (1 - x))), abs_one]
    exact add_le_add hw2 le_rfl
  have hl0 := c.lambdaMin_pos.le.trans (hP.recurrenceBounds a (1 - x) ht).1
  have hnum : 0 ≤ survival P a (1 - x) * P.lam a (1 - x) :=
    mul_nonneg (Real.exp_pos _).le hl0
  have hn : survival P a (1 - x) * P.lam a (1 - x) ≤ c.lambdaMax := by
    calc
      _ ≤ 1 * c.lambdaMax := mul_le_mul
        (survival_bounds_of_deathBounds c P hP.deathBounds a ht).2
        (hP.recurrenceBounds a (1 - x) ht).2 hl0 (by norm_num)
      _ = _ := one_mul _
  rw [abs_mul, abs_of_nonneg (div_nonneg hnum hGp.le)]
  calc
    _ ≤ (weightEnvelope c ^ 2 + 1) * (c.lambdaMax / (r * h)) := by
      exact mul_le_mul hc (div_le_div₀ (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
        hn (mul_pos hr hh) hrh) (div_nonneg hnum hGp.le) (by positivity)
    _ = _ := by dsimp [r]; ring

/-- The continuation-band correction has a bounded integral independent of
bandwidth and law. Outside the band the correction is zero almost everywhere. -/
-- @node: critical_oracle_band_correction_integral_uniform
lemma critical_oracle_band_correction_integral_uniform (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {h : ℝ} (hh : 0 < h) (hh0 : 2 * h ≤ c.x0) :
    |∫ x in h..c.x0,
      (continuationWeight (holderOrder c) h (1 - x) ^ 2 - 1) *
        (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x))| ≤
      (weightEnvelope c ^ 2 + 1) * c.lambdaMax / min c.Gint (c.gMin / 2) := by
  let f := fun x => (continuationWeight (holderOrder c) h (1 - x) ^ 2 - 1) *
    (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x))
  let C := (weightEnvelope c ^ 2 + 1) * c.lambdaMax / min c.Gint (c.gMin / 2)
  have hhx : h ≤ c.x0 := by linarith
  have hi := critical_terminal_density_intervalIntegrable c hk P hP a hh hhx
  have hfi : IntervalIntegrable f volume h c.x0 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hhx] at hi ⊢
    have hm : Measurable (fun x : ℝ => continuationWeight (holderOrder c) h (1 - x) ^ 2 - 1) := by
      first | fun_prop | exact ((measurable_recurrenceContinuationWeight c h).comp
        (show Measurable (fun x : ℝ => 1 - x) by fun_prop)).pow_const 2 |>.sub measurable_const
    have hb : ∀ᵐ x ∂volume.restrict (Icc h c.x0),
        ‖continuationWeight (holderOrder c) h (1 - x) ^ 2 - 1‖ ≤ weightEnvelope c ^ 2 + 1 := by
      apply Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs]
      apply (abs_sub _ _).trans
      have hw : |continuationWeight (holderOrder c) h (1 - x)| ≤ weightEnvelope c :=
        continuationWeight_abs_le_coeffSum (holderOrder c) hh
      simpa only [abs_of_nonneg (sq_nonneg (continuationWeight (holderOrder c) h (1 - x))), abs_one, sq_abs] using
        add_le_add (pow_le_pow_left₀ (abs_nonneg _) hw 2) (le_rfl : (1 : ℝ) ≤ 1)
    exact hi.bdd_mul hm.aestronglyMeasurable.restrict hb
  have hib := hfi.mono_set (show uIcc h (2 * h) ⊆ uIcc h c.x0 by
    rw [uIcc_of_le (by linarith : h ≤ 2 * h), uIcc_of_le hhx]
    exact Icc_subset_Icc le_rfl hh0)
  have hit := hfi.mono_set (show uIcc (2 * h) c.x0 ⊆ uIcc h c.x0 by
    rw [uIcc_of_le hh0, uIcc_of_le hhx]
    exact Icc_subset_Icc (by linarith) le_rfl)
  have hz : (∫ x in (2 * h)..c.x0, f x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Eventually.of_forall
    intro x hx
    rw [uIoc_of_le hh0] at hx
    dsimp [f]
    rw [continuationWeight_eq_one_before_band (holderOrder c) hh.le (by linarith [hx.1])]
    ring
  have he := intervalIntegral.integral_add_adjacent_intervals hib hit
  rw [hz, add_zero] at he
  change |∫ x in h..c.x0, f x| ≤ C
  rw [← he]
  have hb : ∀ x ∈ uIoc h (2 * h), ‖f x‖ ≤ C / h := by
    intro x hx
    rw [uIoc_of_le (by linarith : h ≤ 2 * h)] at hx
    simpa only [Real.norm_eq_abs, f, C] using
      critical_oracle_band_correction_density_le c hk P hP a hh ⟨hx.1.le, hx.2⟩
        (by linarith [hx.2, c.x0_le])
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, show 2 * h - h = h by ring, abs_of_pos hh] at hb'
  simpa only [div_mul_cancel₀ _ hh.ne'] using hb'

/-- Squared continuation weighting preserves integrability of the terminal
oracle density, because the construction supplies a bounded measurable weight. -/
-- @node: critical_weighted_terminal_density_intervalIntegrable
lemma critical_weighted_terminal_density_intervalIntegrable (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {h : ℝ} (hh : 0 < h) (hh0 : h ≤ c.x0) :
    IntervalIntegrable (fun x => continuationWeight (holderOrder c) h (1 - x) ^ 2 *
      (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x)))
      volume h c.x0 := by
  have hi := critical_terminal_density_intervalIntegrable c hk P hP a hh hh0
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hh0] at hi ⊢
  have hm : Measurable (fun x : ℝ => continuationWeight (holderOrder c) h (1 - x) ^ 2) := by
    first | fun_prop | exact ((measurable_recurrenceContinuationWeight c h).comp
      (show Measurable (fun x : ℝ => 1 - x) by fun_prop)).pow_const 2
  apply hi.bdd_mul hm.aestronglyMeasurable.restrict
  apply Eventually.of_forall
  intro x
  have hw : |continuationWeight (holderOrder c) h (1 - x)| ≤ weightEnvelope c :=
    continuationWeight_abs_le_coeffSum (holderOrder c) hh
  simpa only [norm_pow, Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) hw 2

/-- The genuine weighted terminal oracle integral has the same logarithmic
coefficient as the unweighted integral; the band changes only a bounded remainder. -/
-- @node: critical_weighted_terminal_log_expansion_uniform
lemma critical_weighted_terminal_log_expansion_uniform (c : ClassConstants)
    (hk : c.kappa = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : SubjectLaw, ModelClass c P → ∀ a : Arm,
      ∀ h : ℝ, 0 < h → 2 * h ≤ c.x0 →
        |(∫ x in h..c.x0, continuationWeight (holderOrder c) h (1 - x) ^ 2 *
          (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x))) -
            (survival P a 1 * P.lam a 1 / P.g a) * Real.log (c.x0 / h)| ≤ C := by
  obtain ⟨B, hB, hb⟩ := critical_oracle_terminal_log_expansion_uniform c hk
  let D := (weightEnvelope c ^ 2 + 1) * c.lambdaMax / min c.Gint (c.gMin / 2)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg (mul_nonneg (by positivity)
      (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le))
      (le_min c.Gint_pos.le (half_pos c.gMin_pos).le)
  refine ⟨D + B, add_nonneg hD hB, ?_⟩
  intro P hP a h hh hh0
  have hhx : h ≤ c.x0 := by linarith
  have hi := critical_terminal_density_intervalIntegrable c hk P hP a hh hhx
  have hw := critical_weighted_terminal_density_intervalIntegrable c hk P hP a hh hhx
  have hd := critical_oracle_band_correction_integral_uniform c hk P hP a hh hh0
  have he : (∫ x in h..c.x0, continuationWeight (holderOrder c) h (1 - x) ^ 2 *
      (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x))) -
      (∫ x in h..c.x0, survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x)) =
      ∫ x in h..c.x0, (continuationWeight (holderOrder c) h (1 - x) ^ 2 - 1) *
        (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x)) := by
    rw [← intervalIntegral.integral_sub hw hi]
    congr 1
    ext x
    ring
  calc
    _ ≤ |(∫ x in h..c.x0, continuationWeight (holderOrder c) h (1 - x) ^ 2 *
          (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x))) -
        (∫ x in h..c.x0, survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x))| +
      |(∫ x in h..c.x0, survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x)) -
        (survival P a 1 * P.lam a 1 / P.g a) * Real.log (c.x0 / h)| := abs_sub_le _ _ _
    _ ≤ D + B := add_le_add (by rw [he]; exact hd) (hb P hP a h hh hhx)

/-- The bounded interior contributes no diverging term to the oracle integral. -/
-- @node: critical_oracle_interior_integral_uniform_le
lemma critical_oracle_interior_integral_uniform_le (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {h : ℝ} (hh : 0 < h) :
    |∫ t in (0 : ℝ)..(1 - c.x0), continuationWeight (holderOrder c) h t ^ 2 *
      survival P a t * P.lam a t / retention P a t| ≤
      weightEnvelope c ^ 2 * c.lambdaMax / c.Gint := by
  have hb : ∀ t ∈ uIoc (0 : ℝ) (1 - c.x0),
      ‖continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t /
        retention P a t‖ ≤ weightEnvelope c ^ 2 * c.lambdaMax / c.Gint := by
    intro t ht
    rw [uIoc_of_le (by linarith [c.x0_le] : (0 : ℝ) ≤ 1 - c.x0)] at ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, by linarith [ht.2, c.x0_pos]⟩
    have hG := hP.interiorRetention a t ⟨ht.1.le, ht.2⟩
    have hGp := c.Gint_pos.trans_le hG
    have hs0 : 0 ≤ survival P a t := (Real.exp_pos _).le
    have hl0 := c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht01).1
    have hw : |continuationWeight (holderOrder c) h t| ≤ weightEnvelope c :=
      continuationWeight_abs_le_coeffSum (holderOrder c) hh
    have hw2 : continuationWeight (holderOrder c) h t ^ 2 ≤ weightEnvelope c ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hw 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤
      continuationWeight (holderOrder c) h t ^ 2 * survival P a t * P.lam a t / retention P a t)]
    apply div_le_div₀ (mul_nonneg (sq_nonneg _) (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le))
      _ c.Gint_pos hG
    calc
      _ ≤ weightEnvelope c ^ 2 * 1 * c.lambdaMax := by
        gcongr
        · exact (survival_bounds_of_deathBounds c P hP.deathBounds a ht01).2
        · exact (hP.recurrenceBounds a t ht01).2
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (by linarith [c.x0_le] : 0 ≤ 1 - c.x0)] at hi
  apply hi.trans
  apply mul_le_of_le_one_right
  · exact div_nonneg (mul_nonneg (sq_nonneg _) (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)) c.Gint_pos.le
  · linarith [c.x0_pos]

/-- Roadmap (13) for the full, genuinely weighted oracle integral: the
interior and continuation band contribute only a uniform bounded remainder. -/
-- @node: critical_oracle_log_expansion_uniform
lemma critical_oracle_log_expansion_uniform (c : ClassConstants)
    (hk : c.kappa = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : SubjectLaw, ModelClass c P → ∀ a : Arm,
      ∀ h : ℝ, 0 < h → 2 * h ≤ c.x0 →
        |(∫ t in (0 : ℝ)..(1 - h), continuationWeight (holderOrder c) h t ^ 2 *
          survival P a t * P.lam a t / retention P a t) -
            (survival P a 1 * P.lam a 1 / P.g a) * Real.log (1 / h)| ≤ C := by
  obtain ⟨B, hB, hb⟩ := critical_weighted_terminal_log_expansion_uniform c hk
  let I := weightEnvelope c ^ 2 * c.lambdaMax / c.Gint
  let E := c.lambdaMax / c.gMin * |Real.log c.x0|
  have hL : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hI : 0 ≤ I := div_nonneg (mul_nonneg (sq_nonneg _) hL) c.Gint_pos.le
  have hE : 0 ≤ E := mul_nonneg (div_nonneg hL c.gMin_pos.le) (abs_nonneg _)
  refine ⟨I + B + E, add_nonneg (add_nonneg hI hB) hE, ?_⟩
  intro P hP a h hh hh0
  have hh1 : h ≤ 1 := by linarith [c.x0_le]
  have hp := c.pMin_pos.trans_le (hP.treatmentOverlap a)
  let f := fun t => continuationWeight (holderOrder c) h t ^ 2 *
    survival P a t * P.lam a t / retention P a t
  let A := survival P a 1 * P.lam a 1 / P.g a
  have hi : IntervalIntegrable f volume 0 (1 - h) := by
    convert (critical_oracle_density_intervalIntegrable c P hP a hh hh1).const_mul (P.p a) using 1
    ext t
    dsimp [f]
    field_simp
  have hii := hi.mono_set (show uIcc (0 : ℝ) (1 - c.x0) ⊆ uIcc 0 (1 - h) by
    rw [uIcc_of_le (by linarith [c.x0_le] : (0 : ℝ) ≤ 1 - c.x0),
      uIcc_of_le (by linarith : (0 : ℝ) ≤ 1 - h)]
    exact Icc_subset_Icc le_rfl (by linarith))
  have hit := hi.mono_set (show uIcc (1 - c.x0) (1 - h) ⊆ uIcc 0 (1 - h) by
    rw [uIcc_of_le (by linarith : 1 - c.x0 ≤ 1 - h),
      uIcc_of_le (by linarith : (0 : ℝ) ≤ 1 - h)]
    exact Icc_subset_Icc (by linarith [c.x0_le]) le_rfl)
  have he := intervalIntegral.integral_add_adjacent_intervals hii hit
  have hterminal : (∫ t in (1 - c.x0)..(1 - h), f t) =
      ∫ x in h..c.x0, continuationWeight (holderOrder c) h (1 - x) ^ 2 *
        (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x)) := by
    simpa only [sub_sub_cancel, f, mul_div_assoc, mul_assoc] using
      (intervalIntegral.integral_comp_sub_left
        (f := fun x => continuationWeight (holderOrder c) h (1 - x) ^ 2 *
          (survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x)))
        (a := 1 - c.x0) (b := 1 - h) (1 : ℝ))
  have htbound : |(∫ t in (1 - c.x0)..(1 - h), f t) - A * Real.log (c.x0 / h)| ≤ B := by
    rw [hterminal]
    exact hb P hP a h hh hh0
  have hAb : |A| ≤ c.lambdaMax / c.gMin := by
    have hg := c.gMin_pos.trans_le (hP.endpointCoefficientBounds a).1
    have hl0 := c.lambdaMin_pos.le.trans (hP.recurrenceBounds a 1 (by norm_num)).1
    have hs0 : 0 ≤ survival P a 1 := (Real.exp_pos _).le
    dsimp [A]
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hs0 hl0) hg.le)]
    apply div_le_div₀ hL _ c.gMin_pos (hP.endpointCoefficientBounds a).1
    calc
      _ ≤ 1 * c.lambdaMax := mul_le_mul
        (survival_bounds_of_deathBounds c P hP.deathBounds a (by norm_num)).2
        (hP.recurrenceBounds a 1 (by norm_num)).2 hl0 (by norm_num)
      _ = _ := one_mul _
  have hlog : Real.log (c.x0 / h) = Real.log (1 / h) + Real.log c.x0 := by
    rw [Real.log_div c.x0_pos.ne' hh.ne', Real.log_div one_ne_zero hh.ne', Real.log_one]
    ring
  change |(∫ t in (0 : ℝ)..(1 - h), f t) - A * Real.log (1 / h)| ≤ I + B + E
  rw [← he]
  calc
    _ = |(∫ t in (0 : ℝ)..(1 - c.x0), f t) +
      ((∫ t in (1 - c.x0)..(1 - h), f t) - A * Real.log (c.x0 / h)) +
        A * Real.log c.x0| := by rw [hlog]; congr 1; ring
    _ ≤ |∫ t in (0 : ℝ)..(1 - c.x0), f t| +
      |(∫ t in (1 - c.x0)..(1 - h), f t) - A * Real.log (c.x0 / h)| +
        |A * Real.log c.x0| := (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ I + B + E := add_le_add
      (add_le_add (critical_oracle_interior_integral_uniform_le c P hP a hh) htbound)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hAb (abs_nonneg _))

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
