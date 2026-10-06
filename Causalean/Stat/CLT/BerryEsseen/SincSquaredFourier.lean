module
public import Causalean.Stat.CLT.BerryEsseen.SincBoxConvolution
public import Causalean.Stat.CLT.BerryEsseen.SincSquaredPrereqs
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Fourier transform of squared sinc

The triangle transform of squared sinc is the base analytic calculation for
the compact-frequency fourth-power smoothing kernel. The endpoint formula
includes the boundary of its Fourier support.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory
open scoped Convolution

/-- At [every real frequency t](hyp:t), [the Fourier integral of squared sinc is
the triangular function π·max(1 − |t|/2, 0)](goal): it equals π(1 − |t|/2)
on frequencies of absolute value at most two and zero outside, including at
the two support endpoints. -/
theorem sincSquared_fourier_triangle (t : ℝ) :
    ∫ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          ((Real.sinc x ^ 2 : ℝ) : ℂ) =
      ((Real.pi * max (1 - |t| / 2) 0 : ℝ) : ℂ) := by
  let f : ℝ → ℂ := sincBox ⋆[ContinuousLinearMap.mul ℂ ℂ] sincBox
  have hf (u : ℝ) : f u = ((Real.pi * max (1 - Real.pi * |u|) 0 : ℝ) : ℂ) := by
    simpa [f, convolution, mul_comm] using sincBox_self_convolution u
  have hcont : Continuous f := by
    have h : Continuous (fun u : ℝ => ((Real.pi * max (1 - Real.pi * |u|) 0 : ℝ) : ℂ)) := by
      fun_prop
    simpa only [← funext hf] using h
  have hfi : Integrable f :=
    sincBox_integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) sincBox_integrable
  have hFourier (u : ℝ) : FourierTransform.fourier f u = ((Real.sinc u ^ 2 : ℝ) : ℂ) := by
    rw [Real.fourier_mul_convolution_eq sincBox_integrable sincBox_integrable]
    simp [sincBox_fourier, pow_two]
  have hFourierInt : Integrable (FourierTransform.fourier f) := by
    rw [funext hFourier]
    exact sincSquared_integrable.ofReal
  calc
    _ = FourierTransform.fourierInv (FourierTransform.fourier f)
          (t / (2 * Real.pi)) := by
      rw [Real.fourierInv_eq']
      simp_rw [hFourier]
      apply integral_congr_ae
      filter_upwards with x
      have hx : 2 * Real.pi * inner ℝ x (t / (2 * Real.pi)) = t * x := by
        simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial]
        field_simp [Real.pi_ne_zero]
      simp only [smul_eq_mul, hx]
    _ = f (t / (2 * Real.pi)) :=
      hfi.fourierInv_fourier_eq hFourierInt hcont.continuousAt
    _ = ((Real.pi * max (1 - |t| / 2) 0 : ℝ) : ℂ) := by
      rw [hf]
      congr 1
      have hpi : 0 < Real.pi := Real.pi_pos
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hpi]
      field_simp [Real.pi_ne_zero]

end Causalean.Stat.CLT.BerryEsseen
