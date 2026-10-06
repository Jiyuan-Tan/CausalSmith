module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Fourier coefficient of a triangular weight

The deterministic coefficient is valid at zero frequency as well. Product-to-sum
then evaluates the weighted sine coefficients in the Abel expansion of cotangent.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- [The unit-interval triangular cosine coefficient ∫₀¹ (1 − t)·cos(2πat) dt
equals one half of sinc(πa)²](goal) at [any real frequency a](hyp:a). -/
theorem triangular_cosine_integral (a : ℝ) :
    (∫ t in (0 : ℝ)..1, (1 - t) * Real.cos (2 * Real.pi * a * t)) =
      Real.sinc (Real.pi * a) ^ 2 / 2 := by
  /- Separate a=0. Otherwise integrate twice, or use an explicit antiderivative
  (1-t)*sin(c*t)/c-cos(c*t)/c² with c=2πa. The endpoint value is
  (1-cos(2πa))/(2πa)²; use 1-cos(2z)=2sin(z)² and sinc_of_ne_zero.
  All functions here are continuous: no singular integral or series exchange.
  Weighted sine products are half the difference of the coefficients at n-x
  and n+x. At integer n this simplifies to reciprocal squares when sin(πx)≠0. -/
  by_cases ha : a = 0
  · subst a
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, Real.sinc_zero, one_pow]
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
      (continuous_const.intervalIntegrable 0 1) (continuous_id.intervalIntegrable 0 1)]
    norm_num [integral_id]
  let c : ℝ := 2 * Real.pi * a
  have hc : c ≠ 0 := by dsimp [c]; exact mul_ne_zero (by positivity) ha
  let f : ℝ → ℝ := fun t =>
    (1 - t) * Real.sin (c * t) / c - Real.cos (c * t) / c ^ 2
  have hd (t : ℝ) : HasDerivAt f ((1 - t) * Real.cos (c * t)) t := by
    have hl := (hasDerivAt_id t).const_mul c
    convert! ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul
      hl.sin).div_const c).sub (hl.cos.div_const (c ^ 2)) using 1
    dsimp [f]
    field_simp
    ring
  have hi : IntervalIntegrable (fun t : ℝ => (1 - t) * Real.cos (c * t))
      volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => (1 - t) * Real.cos (c * t))).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) hi
  change (∫ t in (0 : ℝ)..1, (1 - t) * Real.cos (c * t)) = _
  rw [he]
  dsimp [f, c]
  simp only [mul_one, mul_zero, sub_self, zero_mul, zero_div, Real.cos_zero,
    sub_zero, Real.sin_zero, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero ha)]
  rw [show 2 * Real.pi * a = 2 * (Real.pi * a) by ring,
    Real.cos_two_mul_eq_one_sub]
  field_simp
  ring

end Causalean.Stat.CLT.BerryEsseen
