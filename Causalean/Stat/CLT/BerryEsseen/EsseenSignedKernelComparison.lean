module
public import Causalean.Stat.CLT.BerryEsseen.EsseenSignedKernel
public import Causalean.Stat.CLT.BerryEsseen.EsseenSinc4SecondMoment

/-! # Spatial comparison for the signed sinc-fourth kernel

The one-sided increment condition is integrated against a positive
linearly weighted sinc-fourth density. The first two exact moments fix the
numerical comparison error at seven.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- If [H has downward increments at most the distance between its
arguments](hyp:hdown) and [the product of the reflected function H(−y) with
the signed sinc-fourth comparison kernel is integrable](hyp:hprod), then
[the value of H at zero is at most twice the absolute value of that
convolution integral plus seven](goal). -/
theorem esseenSignedSinc4Kernel_comparison
    (H : ℝ → ℝ)
    (hdown : ∀ a b : ℝ, a ≤ b → H a ≤ H b + (b - a))
    (hprod : Integrable (fun y : ℝ =>
      H (-y) * esseenSignedSinc4Kernel y) volume) :
    H 0 ≤ 2 * |∫ y : ℝ, H (-y) * esseenSignedSinc4Kernel y| + 7 := by
  /- The increment condition gives
  `H 0 * x ≤ H x * x + x²` for every real x. Multiply by
  `sinc4Kernel 1 (x-4) / 8 ≥ 0` and integrate. Translation of the
  zeroth, first, and second moments gives respectively 1, 4, and 28.
  Reflection turns the resulting integral into the stated convolution;
  `a ≤ |a|` finishes. -/
  let q : ℝ → ℝ := sinc4Kernel 1
  have hq : Integrable q volume := sinc4Kernel_integrable 1 (by norm_num)
  have hq0 : (∫ x : ℝ, q x) = 1 := sinc4Kernel_integral_eq_one 1 (by norm_num)
  have hq1 := sinc4Kernel_unit_first_moment
  have hq2 := sinc4Kernel_unit_second_moment
  have hlinear : Integrable (fun x : ℝ => (x + 4) * q x) volume := by
    apply (hq1.1.add (hq.const_mul 4)).congr
    filter_upwards with x
    dsimp [q]
    ring
  have hlinear_val : (∫ x : ℝ, (x + 4) * q x) = 4 := by
    have hp (x : ℝ) : (x + 4) * q x = x * q x + 4 * q x := by ring
    simp_rw [hp]
    rw [integral_add hq1.1 (hq.const_mul 4), integral_const_mul, hq1.2, hq0]
    ring
  have hquad : Integrable (fun x : ℝ => (x + 4) ^ 2 * q x) volume := by
    apply ((hq2.1.add (hq1.1.const_mul 8)).add (hq.const_mul 16)).congr
    filter_upwards with x
    dsimp [q]
    ring
  have hquad_val : (∫ x : ℝ, (x + 4) ^ 2 * q x) = 28 := by
    have hp (x : ℝ) : (x + 4) ^ 2 * q x =
        x ^ 2 * q x + 8 * (x * q x) + 16 * q x := by ring
    simp_rw [hp]
    change (∫ x : ℝ, (x ^ 2 * q x + 8 * (x * q x)) + 16 * q x) = 28
    have ha := integral_add (hq2.1.add (hq1.1.const_mul 8)) (hq.const_mul 16)
    have hb := integral_add hq2.1 (hq1.1.const_mul 8)
    simp only [Pi.add_apply] at ha hb
    rw [ha, hb, integral_const_mul, integral_const_mul, hq2.2, hq1.2, hq0]
    norm_num
  have hshift1 : Integrable (fun x : ℝ => x * q (x - 4)) volume := by
    convert hlinear.comp_add_left (-4) using 1
    ext x; congr 1 <;> ring
  have hshift2 : Integrable (fun x : ℝ => x ^ 2 * q (x - 4)) volume := by
    convert hquad.comp_add_left (-4) using 1
    ext x; congr 1 <;> ring
  have hshift1_val : (∫ x : ℝ, x * q (x - 4)) = 4 := by
    have ht := integral_add_right_eq_self (μ := volume)
      (fun x : ℝ => (x + 4) * q x) (-4)
    convert ht.trans hlinear_val using 1
    congr 1; ext x; congr 1 <;> ring
  have hshift2_val : (∫ x : ℝ, x ^ 2 * q (x - 4)) = 28 := by
    have ht := integral_add_right_eq_self (μ := volume)
      (fun x : ℝ => (x + 4) ^ 2 * q x) (-4)
    convert ht.trans hquad_val using 1
    congr 1; ext x; congr 1 <;> ring
  have hweighted : Integrable (fun x : ℝ => H x * x * q (x - 4)) volume := by
    have ht := hprod.comp_neg.const_mul 8
    convert ht using 1
    ext x
    simp only [esseenSignedSinc4Kernel, neg_neg]
    ring
  have hreflect : (∫ x : ℝ, H x * x * q (x - 4)) =
      8 * ∫ y : ℝ, H (-y) * esseenSignedSinc4Kernel y := by
    have ht := integral_neg_eq_self
      (fun x : ℝ => H x * x * q (x - 4)) volume
    calc
      _ = ∫ y : ℝ, H (-y) * (-y) * q (-y - 4) := by
        convert ht.symm using 1
      _ = _ := by
        rw [← integral_const_mul]
        congr 1
        ext y
        simp only [esseenSignedSinc4Kernel]
        ring
  have hpoint (x : ℝ) : H 0 * x ≤ H x * x + x ^ 2 := by
    rcases le_total 0 x with hx | hx
    · have hh := hdown 0 x hx
      nlinarith [mul_nonneg (sub_nonneg.mpr hx)
        (sub_nonneg.mpr (show H x + x ≥ H 0 by simpa using hh))]
    · have hh := hdown x 0 hx
      nlinarith [mul_nonneg (neg_nonneg.mpr hx)
        (show 0 ≤ H 0 - H x - x by linarith)]
  have hleft : Integrable (fun x : ℝ => H 0 * (x * q (x - 4))) volume :=
    hshift1.const_mul (H 0)
  have hright : Integrable (fun x : ℝ =>
      H x * x * q (x - 4) + x ^ 2 * q (x - 4)) volume :=
    hweighted.add hshift2
  have hint : (∫ x : ℝ, H 0 * (x * q (x - 4))) ≤
      ∫ x : ℝ, H x * x * q (x - 4) + x ^ 2 * q (x - 4) := by
    apply integral_mono hleft hright
    intro x
    have hnonneg : 0 ≤ q (x - 4) := sinc4Kernel_nonneg 1 (by norm_num) _
    nlinarith [mul_nonneg (sub_nonneg.mpr (hpoint x)) hnonneg]
  rw [integral_const_mul, hshift1_val,
    integral_add hweighted hshift2, hshift2_val, hreflect] at hint
  have habs : (∫ y : ℝ, H (-y) * esseenSignedSinc4Kernel y) ≤
      |∫ y : ℝ, H (-y) * esseenSignedSinc4Kernel y| := le_abs_self _
  nlinarith

end Causalean.Stat.CLT.BerryEsseen
