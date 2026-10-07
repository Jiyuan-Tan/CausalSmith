module
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Fourier transform of a compact interval density

The interval density whose Fourier transform is sinc is the first step in
computing the squared-sinc transform by convolution and Fourier inversion.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The interval density at a real point: the complex number π when the
point lies in the half-open interval (−1/(2π), 1/(2π)], and zero otherwise.
It integrates to one, and its Fourier transform is the real sinc function. -/
noncomputable def sincBox (t : ℝ) : ℂ :=
  (Set.Ioc (-(2 * Real.pi)⁻¹) ((2 * Real.pi)⁻¹)).indicator
    (fun _ => (Real.pi : ℂ)) t

/-- The compactly supported interval density defining `sincBox` is
Lebesgue integrable. -/
theorem sincBox_integrable : Integrable sincBox := by
  unfold sincBox
  exact
    (continuous_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).integrable_indicator
      measurableSet_Ioc

/-- At [every real frequency x](hyp:x), [the Fourier transform of the compact
interval density equal to π on `(−1/(2π), 1/(2π)]` is the real sinc function
sin(x)/x, viewed as a complex number](goal). -/
theorem sincBox_fourier (x : ℝ) :
    FourierTransform.fourier sincBox x = (Real.sinc x : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold sincBox
  let a : ℝ := (2 * Real.pi)⁻¹
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hind :
      (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) •
        (Set.Ioc (-a) a).indicator (fun _ => (Real.pi : ℂ)) v) =
      (Set.Ioc (-a) a).indicator (fun v =>
        Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) • (Real.pi : ℂ)) := by
    funext v
    by_cases hv : v ∈ Set.Ioc (-a) a <;> simp [Set.indicator, hv]
  change (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) •
        (Set.Ioc (-a) a).indicator (fun _ => (Real.pi : ℂ)) v) = _
  rw [hind, integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le (neg_le_self ha.le)]
  by_cases hx : x = 0
  · subst x
    simp [a]
    field_simp [Real.pi_ne_zero] <;> ring
  · simp_rw [smul_eq_mul]
    rw [intervalIntegral.integral_mul_const]
    have hexp :
        (fun t : ℝ => Complex.exp (↑(-2 * Real.pi * t * x) * Complex.I)) =
        (fun t : ℝ => Complex.exp ((↑(-2 * Real.pi * x) * Complex.I) * t)) := by
      funext t
      congr 1
      push_cast
      ring
    rw [hexp, integral_exp_mul_complex]
    · rw [Real.sinc_of_ne_zero hx]
      dsimp [a]
      push_cast
      have h₁ : -2 * (Real.pi : ℂ) * x * Complex.I * (2 * (Real.pi : ℂ))⁻¹ =
          -(x : ℂ) * Complex.I := by
        field_simp [Real.pi_ne_zero]
      have h₂ : -2 * (Real.pi : ℂ) * x * Complex.I * -(2 * (Real.pi : ℂ))⁻¹ =
          (x : ℂ) * Complex.I := by
        field_simp [Real.pi_ne_zero]
      rw [h₁, h₂]
      simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      field_simp [Real.pi_ne_zero, hx]
      ring
    · norm_num [Real.pi_ne_zero, hx]

end Causalean.Stat.CLT.BerryEsseen
