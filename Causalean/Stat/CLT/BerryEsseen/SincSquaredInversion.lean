module
public import Causalean.Stat.CLT.BerryEsseen.SincSquaredFourier

/-! # Inversion of the squared-sinc Fourier triangle

The triangle transform of squared sinc is integrable. Fourier inversion then
recovers squared sinc at every spatial point, with the positive-exponential
transform convention and its `1/(2π)` normalization made explicit.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The real triangular Fourier transform `π max (1 - |u|/2) 0` of squared
sinc is integrable over the whole line. -/
theorem sincTriangle_integrable :
    Integrable (fun u : ℝ => Real.pi * max (1 - |u| / 2) 0) volume := by
  let f : ℝ → ℝ := fun u => Real.pi * max (1 - |u| / 2) 0
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hsupp : Function.support f ⊆ Set.Icc (-2) 2 := by
    intro u hu
    simp only [Function.mem_support] at hu
    constructor
    · by_contra hn
      have hle : u < -2 := lt_of_not_ge hn
      have hz : f u = 0 := by
        dsimp [f]
        rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
        ring
      exact hu hz
    · by_contra hn
      have hge : 2 < u := lt_of_not_ge hn
      have hz : f u = 0 := by
        dsimp [f]
        rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
        ring
      exact hu hz
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hf.integrableOn_Icc

/-- At [every real point x](hyp:x), including zero, [squared sinc equals 1/(2π)
times the inverse Fourier integral of its triangle transform
u ↦ π·max(1 − |u|/2, 0)](goal). -/
theorem sincSquared_fourier_inversion (x : ℝ) :
    ((Real.sinc x ^ 2 : ℝ) : ℂ) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ,
          Complex.exp (((-u * x : ℝ) : ℂ) * Complex.I) *
            ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ)) := by
  let f : ℝ → ℂ := fun y => ((Real.sinc y ^ 2 : ℝ) : ℂ)
  let g : ℝ → ℂ := fun u =>
    Complex.exp (((-u * x : ℝ) : ℂ) * Complex.I) *
      ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ)
  have hscale : (-2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hf : Integrable f := by
    exact sincSquared_integrable.ofReal
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hFourier (t : ℝ) : FourierTransform.fourier f t =
      ((Real.pi * max (1 - |(-2 * Real.pi) * t| / 2) 0 : ℝ) : ℂ) := by
    rw [Real.fourier_eq']
    convert sincSquared_fourier_triangle ((-2 * Real.pi) * t) using 1
    apply integral_congr_ae
    filter_upwards with y
    simp only [smul_eq_mul, f, RCLike.inner_apply', starRingEnd_apply, star_trivial]
    congr 2
    push_cast
    ring
  have hFourierInt : Integrable (FourierTransform.fourier f) := by
    rw [funext hFourier]
    have htri : Integrable (fun u : ℝ =>
        ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ)) :=
      sincTriangle_integrable.ofReal
    exact htri.comp_mul_left' hscale
  have hinv := hf.fourierInv_fourier_eq hFourierInt hcont.continuousAt (v := x)
  have hchange : (∫ t : ℝ, g ((-2 * Real.pi) * t)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u : ℝ, g u := by
    rw [Measure.integral_comp_mul_left]
    have hcoeff : |((-2 * Real.pi : ℝ)⁻¹)| = 1 / (2 * Real.pi) := by
      rw [abs_inv, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
      norm_num
    rw [hcoeff]
    rw [Complex.real_smul]
  calc
    ((Real.sinc x ^ 2 : ℝ) : ℂ) = FourierTransform.fourierInv
        (FourierTransform.fourier f) x := hinv.symm
    _ = ∫ t : ℝ, g ((-2 * Real.pi) * t) := by
      rw [Real.fourierInv_eq']
      simp_rw [hFourier]
      apply integral_congr_ae
      filter_upwards with t
      dsimp [g]
      simp only [starRingEnd_apply, star_trivial]
      congr 2
      push_cast
      ring
    _ = _ := hchange

end Causalean.Stat.CLT.BerryEsseen
