module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzEnvelopes
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernelBounds

/-! # PrawitzBudgetGaussian

One independent sufficient estimate in the deterministic Prawitz budget.
The full budget retains its original cutoffs and constant; the three
integral allocations add to one and introduce no probability hypotheses.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- A rational supersolution for the Gaussian tail, valid past one. -/
private theorem gaussian_tail_le (a : ℝ) (ha : 1 ≤ a) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2 / 2)) / t) (Set.Ioi a) ∧
    (∫ t in Set.Ioi a, Real.exp (-(t ^ 2 / 2)) / t) ≤
      Real.exp (-(a ^ 2 / 2)) / (a ^ 2 + 1) := by
  let g := fun t : ℝ => Real.exp (-(t ^ 2 / 2)) / (t ^ 2 + 1)
  let d := fun t : ℝ =>
    -(t * Real.exp (-(t ^ 2 / 2)) * (t ^ 2 + 3) / (t ^ 2 + 1) ^ 2)
  have hd (t : ℝ) : HasDerivAt g (d t) t := by
    have hn : t ^ 2 + 1 ≠ 0 := by positivity
    convert (((((hasDerivAt_id t).pow 2).div_const 2).neg.exp).div
      (((hasDerivAt_id t).pow 2).add_const 1) hn) using 1 <;>
      first | rfl | (dsimp [d]; field_simp; ring)
  have hdneg (t : ℝ) (ht : t ∈ Set.Ioi a) : d t ≤ 0 := by
    dsimp [d]
    have : 0 ≤ t := by linarith [ht.out]
    apply neg_nonpos.mpr
    positivity
  have hg : Filter.Tendsto g Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun t => by dsimp [g]; positivity))
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with t ht
      dsimp [g]
      calc
        _ ≤ Real.exp (-(t ^ 2 / 2)) :=
          div_le_self (Real.exp_nonneg _) (by nlinarith [sq_nonneg t])
        _ ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by nlinarith)
    · exact Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot
  have hdi : IntegrableOn d (Set.Ioi a) :=
    integrableOn_Ioi_deriv_of_nonpos' (fun t _ => hd t) hdneg hg
  have hdom (t : ℝ) (ht : t ∈ Set.Ioi a) :
      Real.exp (-(t ^ 2 / 2)) / t ≤ -d t := by
    have htpos : 0 < t := by linarith [ht.out]
    have htsq : 1 ≤ t ^ 2 := by nlinarith [ht.out]
    have hden : 0 < (t ^ 2 + 1) ^ 2 := by positivity
    dsimp [d]
    rw [neg_neg]
    apply (div_le_div_iff₀ htpos hden).mpr
    have he := Real.exp_nonneg (-(t ^ 2 / 2))
    have hp := mul_nonneg he (sub_nonneg.mpr htsq)
    nlinarith
  have hmeas : Measurable (fun t : ℝ => Real.exp (-(t ^ 2 / 2)) / t) := by fun_prop
  have hfi : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2 / 2)) / t) (Set.Ioi a) := by
    apply hdi.neg.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_nonneg _) (by linarith [ht.out]))]
    exact hdom t ht
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ t in Set.Ioi a, -d t := integral_mono_ae hfi hdi.neg (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hdom t ht)
    _ = g a := by
      rw [integral_neg, integral_Ioi_of_hasDerivAt_of_nonpos'
        (fun t _ => hd t) hdneg hg]
      ring
    _ = _ := rfl

@[fun_prop]
private theorem measurable_prawitzKernel : Measurable prawitzKernel := by
  unfold prawitzKernel Real.sign
  apply Measurable.ite
  · exact (measurableSet_eq_fun measurable_id measurable_const).union
      (measurableSet_lt measurable_const continuous_abs.measurable)
  · exact measurable_const
  · apply Measurable.add
    · exact Complex.measurable_ofReal.comp (by fun_prop)
    · apply Measurable.mul _ measurable_const
      apply Complex.measurable_ofReal.comp
      apply Measurable.div_const
      apply Measurable.add
      · fun_prop
      · apply Measurable.div_const
        apply Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
        exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
          measurable_const measurable_const

/-- The scaled correction is bounded even beyond the kernel's support and at zero. -/
private theorem scaled_correction_le (U t : ℝ) (hU : 0 < U) (ht : 0 ≤ t) :
    ‖prawitzKernel (t / U) / (U : ℂ) -
      Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ ≤ 1 / (2 * U) := by
  by_cases hz : t = 0
  · subst t
    simp [prawitzKernel, hU.le]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  have hratio : 0 < t / U := div_pos htpos hU
  by_cases hband : t ≤ U
  · have hk := prawitzKernel_principal_correction_norm_le (t / U)
      (by simpa [abs_of_pos hratio])
      (by rw [abs_of_pos hratio]; exact (div_le_one hU).mpr hband)
    have hUc : (U : ℂ) ≠ 0 := by exact_mod_cast hU.ne'
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast hz
    have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have heq : prawitzKernel (t / U) / (U : ℂ) -
        Complex.I / ((2 * Real.pi * t : ℝ) : ℂ) =
        (prawitzKernel (t / U) -
          Complex.I / ((2 * Real.pi * (t / U) : ℝ) : ℂ)) / (U : ℂ) := by
      push_cast
      field_simp
    rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hU]
    calc
      _ ≤ (1 / 2 : ℝ) / U := div_le_div_of_nonneg_right hk hU.le
      _ = _ := by ring
  · have houtside : 1 < |t / U| := by
      rw [abs_of_pos hratio]
      exact (one_lt_div hU).mpr (lt_of_not_ge hband)
    rw [prawitzKernel, if_pos (Or.inr houtside)]
    simp only [zero_div, zero_sub, norm_neg, norm_div, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi * t)]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.pi * t)
      (by positivity : 0 < 2 * U)).mpr
    nlinarith [Real.pi_gt_three]

/-- Gaussian domination supplies integrability before the principal comparison. -/
private theorem gaussian_correction_integral_le (U a : ℝ) (hU : 0 < U) (ha : 0 ≤ a) :
    2 * (∫ t in (0 : ℝ)..a,
      ‖prawitzKernel (t / U) / (U : ℂ) -
        Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
        Real.exp (-(t ^ 2 / 2))) ≤ Real.sqrt (Real.pi / (1 / 2)) / (2 * U) := by
  let f := fun t : ℝ =>
    ‖prawitzKernel (t / U) / (U : ℂ) -
      Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ * Real.exp (-(t ^ 2 / 2))
  let G := fun t : ℝ => (1 / (2 * U)) * Real.exp (-(t ^ 2 / 2))
  have hg : Integrable G := by
    have he : (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) =
        (fun t : ℝ => Real.exp (-(1 / 2) * t ^ 2)) := by
      funext t
      congr 1
      ring
    have hi : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) := by
      rw [he]
      exact integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    exact hi.const_mul _
  have hmeas : Measurable f := by dsimp [f]; fun_prop
  have hbound (t : ℝ) (ht : 0 ≤ t) : f t ≤ G t := by
    exact mul_le_mul_of_nonneg_right (scaled_correction_le U t hU ht) (Real.exp_nonneg _)
  have hfi : IntegrableOn f (Set.Ioc 0 a) := by
    apply hg.integrableOn.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [f]; positivity)]
    exact hbound t ht.1.le
  rw [intervalIntegral.integral_of_le ha]
  change 2 * (∫ t in Set.Ioc 0 a, f t) ≤ _
  have hcmp : (∫ t in Set.Ioc 0 a, f t) ≤ ∫ t in Set.Ioi 0, G t := by
    calc
      _ ≤ ∫ t in Set.Ioc 0 a, G t := integral_mono_ae hfi hg.integrableOn (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hbound t ht.1.le)
      _ ≤ _ := setIntegral_mono_set hg.integrableOn
        (Filter.Eventually.of_forall (fun t => by dsimp [G]; positivity))
        (Filter.Eventually.of_forall (fun t ht => ht.1))
  have heval : (∫ t in Set.Ioi 0, G t) =
      (1 / (2 * U)) * (Real.sqrt (Real.pi / (1 / 2)) / 2) := by
    dsimp [G]
    rw [integral_const_mul]
    convert congrArg (fun x : ℝ => (1 / (2 * U)) * x) (integral_gaussian_Ioi (1 / 2)) using 1
    congr 2
    funext t
    congr 1
    ring
  rw [heval] at hcmp
  calc
    _ ≤ 2 * ((1 / (2 * U)) * (Real.sqrt (Real.pi / (1 / 2)) / 2)) :=
      mul_le_mul_of_nonneg_left hcmp (by norm_num)
    _ = _ := by ring

/-- For [a moment ratio ρ strictly between zero and one](hyp:ρ,hρ,hρ1), with
cutoffs U0 = max(3/2, √(4 log(1/ρ))) and U = 12/(5ρ) and K the Prawitz filter,
[the Gaussian principal correction 2·∫ over [0, U0] of
|K(t/U)/U − i/(2πt)|·exp(−t²/2), plus the omitted Gaussian tail
(1/π)·∫ over t > U0 of exp(−t²/2)/t, is at most three fifths of ρ](goal). -/
theorem prawitz_budget_gaussian
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    2 * (∫ t in (0 : ℝ)..U0,
      ‖prawitzKernel (t / U) / (U : ℂ) -
        Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
        Real.exp (-(t ^ 2 / 2))) +
    (1 / Real.pi) * (∫ t in Set.Ioi U0,
      Real.exp (-(t ^ 2 / 2)) / t) ≤ 3 * ρ / 5 := by
  /- Separate the principal-correction integral and Gaussian tail. The
  closed kernel lemma gives correction≤1/(2U) a.e.; integrate the Gaussian
  to get ≤sqrt(π/2)/U, which is <(8/15)ρ. It is enough to show the
  remaining tail≤ρ/15. For U0=max(3/2,sqrt(4log(1/ρ))), bound
  ∫_U0^∞ exp(-t²/2)/t by exp(-U0²/2)/U0², splitting at
  ρ=exp(-9/16); if this coarse estimate is insufficient near that point,
  sharpen the tail via integration by parts or a rational exponential bound.
  All integrability claims must be proved, not inferred from total integrals. -/
  dsimp only
  let a := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
  let U := 12 / (5 * ρ)
  have ha : (3 / 2 : ℝ) ≤ a := le_max_left _ _
  have hapos : 0 < a := by linarith
  have hU : 0 < U := by dsimp [U]; positivity
  have hprincipal := gaussian_correction_integral_le U a hU hapos.le
  have hsqrt : Real.sqrt (Real.pi / (1 / 2)) ≤ 64 / 25 := by
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 64 / 25)).mpr
    linarith [Real.pi_lt_d2]
  have hprincipal' :
      2 * (∫ t in (0 : ℝ)..a,
        ‖prawitzKernel (t / U) / (U : ℂ) -
          Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
          Real.exp (-(t ^ 2 / 2))) ≤ (8 / 15 : ℝ) * ρ := by
    calc
      _ ≤ Real.sqrt (Real.pi / (1 / 2)) / (2 * U) := hprincipal
      _ ≤ (64 / 25 : ℝ) / (2 * U) := div_le_div_of_nonneg_right hsqrt (by positivity)
      _ = _ := by dsimp [U]; field_simp; ring
  have hlogpos : 0 ≤ 4 * Real.log (1 / ρ) := by
    have hinv : 1 ≤ 1 / ρ := (le_div_iff₀ hρ).mpr (by linarith)
    exact mul_nonneg (by norm_num) (Real.log_nonneg hinv)
  have hcut : 4 * Real.log (1 / ρ) ≤ a ^ 2 := by
    have hroot := le_max_right (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    have hsq := Real.sq_sqrt hlogpos
    have hn := Real.sqrt_nonneg (4 * Real.log (1 / ρ))
    dsimp [a]
    nlinarith
  have hlog : Real.log ρ = -Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv, neg_neg]
  have hexp : Real.exp (-(a ^ 2 / 2)) ≤ ρ * Real.exp (-(a ^ 2 / 4)) := by
    rw [← Real.exp_log hρ, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hlog]
    linarith
  have hsmall : Real.exp (-(a ^ 2 / 4)) ≤ 3 / 5 := by
    have hseries := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 16) 3
    norm_num [Finset.sum_range_succ] at hseries
    have hlower : (5 / 3 : ℝ) ≤ Real.exp (9 / 16) := by linarith
    have hneg : Real.exp (-(9 / 16 : ℝ)) ≤ 3 / 5 := by
      rw [Real.exp_neg]
      rw [← one_div]
      exact (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith)
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans hneg
  have htail := (gaussian_tail_le a (by linarith)).2
  have hden : 0 < a ^ 2 + 1 := by positivity
  have htail' : (1 / Real.pi) *
      (∫ t in Set.Ioi a, Real.exp (-(t ^ 2 / 2)) / t) ≤ ρ / 15 := by
    have hnum : Real.exp (-(a ^ 2 / 2)) ≤ ρ * (3 / 5) :=
      hexp.trans (mul_le_mul_of_nonneg_left hsmall hρ.le)
    calc
      _ ≤ (1 / Real.pi) * (Real.exp (-(a ^ 2 / 2)) / (a ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (1 / Real.pi) * ((ρ * (3 / 5)) / (a ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hden.le) (by positivity)
      _ ≤ ρ / 15 := by
        rw [one_div_mul_eq_div, div_div, mul_comm (a ^ 2 + 1) Real.pi]
        apply (div_le_iff₀ (mul_pos Real.pi_pos hden)).mpr
        have hsq : (13 / 4 : ℝ) ≤ a ^ 2 + 1 := by nlinarith
        have hp : (9 : ℝ) ≤ Real.pi * (a ^ 2 + 1) := by
          nlinarith [Real.pi_gt_three]
        nlinarith
  change _ + (1 / Real.pi) *
    (∫ t in Set.Ioi a, Real.exp (-(t ^ 2 / 2)) / t) ≤ _
  change 2 * (∫ t in (0 : ℝ)..a,
    ‖prawitzKernel (t / U) / (U : ℂ) -
      Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
      Real.exp (-(t ^ 2 / 2))) + _ ≤ _
  linarith

end Causalean.Stat.CLT.BerryEsseen
