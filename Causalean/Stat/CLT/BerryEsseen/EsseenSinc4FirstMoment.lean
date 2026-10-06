module
public import Causalean.Stat.CLT.BerryEsseen.SincSquaredPrereqs
public import Causalean.Stat.CLT.BerryEsseen.SmoothingKernel
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # First moment of the unit-bandwidth sinc-fourth density

The unit-bandwidth sinc-fourth kernel is even. Its absolute first moment is
finite, and its signed first moment vanishes. These facts are used to shift
the kernel in the one-sided Esseen comparison.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- [The first-moment density x·K(x) of the unit-bandwidth sinc-fourth kernel K
is integrable, and its integral is zero](goal). -/
theorem sinc4Kernel_unit_first_moment :
    Integrable (fun x : ℝ => x * sinc4Kernel 1 x) volume ∧
      (∫ x : ℝ, x * sinc4Kernel 1 x) = 0 := by
  have hs : Integrable (fun x : ℝ => Real.sinc (x / 4) ^ 2) volume := by
    convert sincSquared_integrable.comp_mul_left' (by norm_num : (1 / 4 : ℝ) ≠ 0) using 1
    ext x
    congr 1
    ring_nf
  have hb (x : ℝ) : |x * Real.sinc (x / 4) ^ 2| ≤ 4 := by
    have hxs : x * Real.sinc (x / 4) = 4 * Real.sin (x / 4) := by
      by_cases hx : x = 0
      · subst x; simp
      · rw [Real.sinc_of_ne_zero (by exact div_ne_zero hx (by norm_num))]
        field_simp
    have hsin : |x * Real.sinc (x / 4)| ≤ 4 := by
      rw [hxs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      nlinarith [Real.abs_sin_le_one (x / 4)]
    calc
      |x * Real.sinc (x / 4) ^ 2| = |x * Real.sinc (x / 4)| * |Real.sinc (x / 4)| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ 4 * 1 := by
        calc
          _ ≤ 4 * |Real.sinc (x / 4)| :=
            mul_le_mul_of_nonneg_right hsin (abs_nonneg _)
          _ ≤ 4 * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (by norm_num)
      _ = 4 := by ring
  have hp : Integrable
      (fun x : ℝ => (x * Real.sinc (x / 4) ^ 2) * Real.sinc (x / 4) ^ 2) volume := by
    refine Integrable.bdd_mul (c := 4) hs (by fun_prop) ?_
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using hb x
  have hi : Integrable (fun x : ℝ => x * sinc4Kernel 1 x) volume := by
    convert hp.const_mul (3 / (8 * Real.pi)) using 1
    ext x
    simp only [sinc4Kernel, one_mul]
    ring
  refine ⟨hi, ?_⟩
  have heven (x : ℝ) : sinc4Kernel 1 (-x) = sinc4Kernel 1 x := by
    simp only [sinc4Kernel, one_mul, neg_div, Real.sinc_neg]
  have href := integral_neg_eq_self (fun x : ℝ => x * sinc4Kernel 1 x) volume
  have hneg : (∫ x : ℝ, (-x) * sinc4Kernel 1 (-x)) =
      -(∫ x : ℝ, x * sinc4Kernel 1 x) := by
    simp only [heven, neg_mul, integral_neg]
  rw [hneg] at href
  linarith

end Causalean.Stat.CLT.BerryEsseen
