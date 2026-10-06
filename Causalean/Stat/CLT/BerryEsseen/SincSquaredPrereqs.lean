module
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Elementary prerequisites for the squared-sinc Fourier transform

The squared-sinc transform uses an integrable spatial function and the
overlap length of two translated unit intervals. Both facts are stated here
without Fourier analysis so they can be proved independently.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The square of the real sinc function has finite integral over the real
line. -/
theorem sincSquared_integrable :
    Integrable (fun x : ℝ => Real.sinc x ^ 2) volume := by
  apply (integrable_inv_one_add_sq.const_mul (2 : ℝ)).mono
  · fun_prop
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.sinc x ^ 2)]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * (1 + x ^ 2)⁻¹)]
    rw [inv_eq_one_div, mul_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
    by_cases hx : |x| ≤ 1
    · have ha2 : |x| * |x| ≤ 1 * 1 :=
        mul_self_le_mul_self (abs_nonneg x) hx
      have hx2 : x ^ 2 ≤ 1 := by simpa [sq_abs, pow_two] using ha2
      have hs := Real.abs_sinc_le_one x
      have hsl := neg_abs_le (Real.sinc x)
      have hsr := le_abs_self (Real.sinc x)
      have hs2 : Real.sinc x ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (Real.sinc x)]
    · have hxabs : 1 < |x| := lt_of_not_ge hx
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        norm_num at hxabs
      rw [Real.sinc_of_ne_zero hx0, div_pow, div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < x ^ 2)).2
      have habs2 : (1 : ℝ) ^ 2 < |x| ^ 2 :=
        (sq_lt_sq₀ (by positivity) (abs_nonneg x)).2 hxabs
      have hx2 : 1 < x ^ 2 := by simpa [sq_abs] using habs2
      have hs := Real.abs_sin_le_one x
      have hsl := neg_abs_le (Real.sin x)
      have hsr := le_abs_self (Real.sin x)
      have hs2 : Real.sin x ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (Real.sin x)]

/-- [The two closed intervals of length two centered at zero and at t overlap in
a set of Lebesgue length max(2 − |t|, 0)](goal), for [every real t](hyp:t). -/
theorem centeredUnitIntervals_overlap (t : ℝ) :
    volume.real (Set.Icc (-1 : ℝ) 1 ∩ Set.Icc (t - 1) (t + 1)) =
      max (2 - |t|) 0 := by
  rw [Set.Icc_inter_Icc, Real.volume_real_Icc]
  change max (min 1 (t + 1) - max (-1) (t - 1)) 0 = max (2 - |t|) 0
  rcases le_total t 0 with ht | ht
  · rw [max_eq_left (by linarith : t - 1 ≤ (-1 : ℝ)),
      min_eq_right (by linarith : t + 1 ≤ (1 : ℝ)), abs_of_nonpos ht]
    congr 1
    ring
  · rw [max_eq_right (by linarith : (-1 : ℝ) ≤ t - 1),
      min_eq_left (by linarith : (1 : ℝ) ≤ t + 1), abs_of_nonneg ht]
    congr 1
    ring

end Causalean.Stat.CLT.BerryEsseen
