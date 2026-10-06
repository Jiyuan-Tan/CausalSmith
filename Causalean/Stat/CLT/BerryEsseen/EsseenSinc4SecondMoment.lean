module
public import Causalean.Stat.CLT.BerryEsseen.SmoothingKernel

/-! # Second moment of the unit-bandwidth sinc-fourth density

The exact second moment of this compact-frequency density controls the
spatial error of a signed, shifted kernel used in Esseen's comparison.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- [The second-moment density x²·K(x) of the unit-bandwidth sinc-fourth kernel K
is integrable, and its integral equals twelve](goal). -/
theorem sinc4Kernel_unit_second_moment :
    Integrable (fun x : ℝ => x ^ 2 * sinc4Kernel 1 x) volume ∧
      (∫ x : ℝ, x ^ 2 * sinc4Kernel 1 x) = 12 := by
  have hsinc (a : ℝ) (ha : a ≠ 0) :
      Integrable (fun x : ℝ => Real.sinc (a * x) ^ 2) volume :=
    sincSquared_integrable.comp_mul_left' ha
  have hsq : (∫ x : ℝ, Real.sinc x ^ 2) = Real.pi := by
    have h := sincSquared_fourier_triangle 0
    simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul,
      abs_zero, zero_div, sub_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      mul_one, integral_complex_ofReal] at h
    exact Complex.ofReal_injective h
  have hscale (a : ℝ) (ha : 0 < a) :
      (∫ x : ℝ, Real.sinc (a * x) ^ 2) = Real.pi / a := by
    have h := Measure.integral_comp_mul_left (fun x : ℝ => Real.sinc x ^ 2) a
    rw [hsq] at h
    calc
      _ = a⁻¹ * Real.pi := by simpa [smul_eq_mul, abs_of_pos ha] using h
      _ = _ := by ring
  have hpoint (u : ℝ) :
      u ^ 2 * Real.sinc u ^ 4 = Real.sinc u ^ 2 - Real.sinc (2 * u) ^ 2 := by
    by_cases hu : u = 0
    · subst u; norm_num
    · have h2u : 2 * u ≠ 0 := mul_ne_zero (by norm_num) hu
      rw [Real.sinc_of_ne_zero hu, Real.sinc_of_ne_zero h2u,
        Real.sin_two_mul]
      have htrig := Real.sin_sq_add_cos_sq u
      field_simp
      nlinarith [sq_nonneg (Real.sin u), sq_nonneg (Real.cos u)]
  have hpoint' (x : ℝ) :
      x ^ 2 * sinc4Kernel 1 x =
        (3 / (8 * Real.pi)) *
          (16 * (Real.sinc (x / 4) ^ 2 - Real.sinc (x / 2) ^ 2)) := by
    calc
      _ = (3 / (8 * Real.pi)) * 16 *
            ((x / 4) ^ 2 * Real.sinc (x / 4) ^ 4) := by
          simp only [sinc4Kernel, one_mul]
          ring
      _ = _ := by
        rw [hpoint]
        have hx : 2 * (x / 4) = x / 2 := by ring
        rw [hx]
        ring
  have hi : Integrable (fun x : ℝ => x ^ 2 * sinc4Kernel 1 x) volume := by
    have h1 : Integrable (fun x : ℝ => Real.sinc (x / 4) ^ 2) volume := by
      convert hsinc (1 / 4) (by norm_num) using 1
      ext x; congr 1; ring
    have h2 : Integrable (fun x : ℝ => Real.sinc (x / 2) ^ 2) volume := by
      convert hsinc (1 / 2) (by norm_num) using 1
      ext x; congr 1; ring
    convert ((h1.sub h2).const_mul 16).const_mul (3 / (8 * Real.pi)) using 1
    ext x; exact hpoint' x
  refine ⟨hi, ?_⟩
  simp_rw [hpoint']
  rw [integral_const_mul, integral_const_mul, integral_sub]
  · have h4 : (∫ x : ℝ, Real.sinc (x / 4) ^ 2) = 4 * Real.pi := by
      convert hscale (1 / 4) (by norm_num) using 1
      · congr 1; ext x; congr 1; ring
      · ring
    have h2 : (∫ x : ℝ, Real.sinc (x / 2) ^ 2) = 2 * Real.pi := by
      convert hscale (1 / 2) (by norm_num) using 1
      · congr 1; ext x; congr 1; ring
      · ring
    rw [h4, h2]
    field_simp [Real.pi_ne_zero]
    ring
  · convert hsinc (1 / 4) (by norm_num) using 1
    ext x; congr 1; ring
  · convert hsinc (1 / 2) (by norm_num) using 1
    ext x; congr 1; ring

end Causalean.Stat.CLT.BerryEsseen
