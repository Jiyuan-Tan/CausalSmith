module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Weighted Gaussian upper tails

This real probability-independent tail estimate integrates the reciprocal
and constant weights appearing in a scaled spectral-kernel bound. It isolates
the improper-integral calculation from Prawitz's parameter-dependent cutoffs.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a positive lower endpoint a and damping rate b](hyp:a,b,ha,hb) and
[a nonnegative constant weight c](hyp:c,hc), [the integral over t > a of
(1/(πt) + c)·exp(−bt²) is at most
(1/(2πba²) + c/(2ba))·exp(−ba²)](goal). -/
theorem gaussian_reciprocal_linear_tail_bound
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) :
    (∫ t in Set.Ioi a,
      (1 / (Real.pi * t) + c) * Real.exp (-(b * t ^ 2))) ≤
      (1 / (2 * Real.pi * b * a ^ 2) + c / (2 * b * a)) *
        Real.exp (-(b * a ^ 2)) := by
  /- Bound the reciprocal and constant parts separately by the standard
  Gaussian tail supersolutions e^(-bt²)/(2πbt²) and c*e^(-bt²)/(2bt).
  Their negative derivatives dominate the integrands for t>0. Show the
  supersolutions tend to zero and apply integral comparison/Fundamental
  Theorem of Calculus on Ioi a. Alternatively bound 1/t by t/a² and 1 by
  t/a, then integrate t*e^(-bt²) exactly. This second proof needs only the
  derivative of -e^(-bt²)/(2b), plus Gaussian integrability away from zero.
  No Prawitz module is imported; this leaf must stay independently usable.

  For the small-ratio middle-frequency budget use b=2/5, c=5ρ/12,
  a=U0. On t≤1/(2ρ), the cubic damping is at most e^(-2t²/5).
  U0²≥4log(1/ρ) gives e^(-2U0²/5)≤ρ*sqrt ρ, and U0≥3/2;
  for ρ≤1/100 the resulting allocation is less than ρ/20. This connection
  belongs to the later high-budget assembly, not to this generic theorem. -/
  let K : ℝ := 1 / (Real.pi * a ^ 2) + c / a
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun x : ℝ => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2))
      (t * Real.exp (-b * t ^ 2)) t := by
    intro t
    convert ((hasDerivAt_pow 2 t).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹) using 1
    all_goals first | rfl | (field_simp; ring)
  have hlim : Filter.Tendsto
      (fun x : ℝ => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2))
      Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      ((Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
        (neg_lt_zero.mpr hb))).const_mul (-(2 * b)⁻¹)
  have hgi : IntegrableOn (fun t : ℝ => t * Real.exp (-b * t ^ 2)) (Set.Ioi a) :=
    (integrable_mul_exp_neg_mul_sq hb).integrableOn
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => hderiv t) hgi hlim
  have hmajor : ∀ t ∈ Set.Ioi a,
      (1 / (Real.pi * t) + c) * Real.exp (-(b * t ^ 2)) ≤
        K * (t * Real.exp (-b * t ^ 2)) := by
    intro t ht
    have htpos : 0 < t := lt_trans ha ht
    have hrec : 1 / (Real.pi * t) ≤ t / (Real.pi * a ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hs : a ^ 2 ≤ t ^ 2 := by nlinarith [show a < t from ht]
      have hm := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
      nlinarith [hm]
    have hc' : c ≤ (c / a) * t := by
      have hat : 1 ≤ t / a := (le_div_iff₀ ha).2 (by simpa using (le_of_lt ht : a ≤ t))
      have := mul_le_mul_of_nonneg_left hat hc
      simpa only [mul_one, div_mul_eq_mul_div, mul_div_assoc] using this
    have hw : 1 / (Real.pi * t) + c ≤ K * t := by
      dsimp [K]
      calc
        _ ≤ t / (Real.pi * a ^ 2) + (c / a) * t := add_le_add hrec hc'
        _ = _ := by ring
    have hm := mul_le_mul_of_nonneg_right hw (Real.exp_nonneg (-(b * t ^ 2)))
    simpa only [neg_mul, mul_assoc] using hm
  have hmi : IntegrableOn (fun t : ℝ => K * (t * Real.exp (-b * t ^ 2)))
      (Set.Ioi a) := hgi.const_mul K
  have hcont : ContinuousOn (fun t : ℝ =>
      (1 / (Real.pi * t) + c) * Real.exp (-(b * t ^ 2))) (Set.Ioi a) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.add
      · exact continuousOn_const.div (continuous_const.mul continuous_id).continuousOn
          (fun t ht => ne_of_gt (mul_pos Real.pi_pos (lt_trans ha ht)))
      · exact continuousOn_const
    · fun_prop
  have hfi : IntegrableOn (fun t : ℝ =>
      (1 / (Real.pi * t) + c) * Real.exp (-(b * t ^ 2))) (Set.Ioi a) := by
    refine hmi.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have htpos : 0 < t := lt_trans ha ht
      positivity)]
    exact hmajor t ht
  have hi := setIntegral_mono_on hfi hmi measurableSet_Ioi hmajor
  rw [integral_const_mul, hval] at hi
  refine hi.trans_eq ?_
  dsimp [K]
  simp only [zero_sub, neg_mul, neg_neg]
  field_simp


end Causalean.Stat.CLT.BerryEsseen
