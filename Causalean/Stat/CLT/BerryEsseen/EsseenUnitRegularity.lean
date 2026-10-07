module
public import Causalean.Stat.CLT.BerryEsseen.EsseenConvolutionTransfer

/-! # Regularity consequences of a unit-bandlimited kernel

For an integrable real kernel whose Fourier transform vanishes outside the
unit interval and has magnitude at most one, the Fourier transform is
integrable (`integrable_unit_supported_kernel_fourier`) and the product of
the kernel with a reflected factor is integrable
(`integrable_reflected_mul_unit_supported_kernel`). These are the two
integrability facts used by the one-sided spectral comparison.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The Fourier transform of an integrable real kernel is integrable when it
vanishes outside the unit interval and has magnitude at most one. -/
theorem integrable_unit_supported_kernel_fourier
    (K : ℝ → ℝ) (hK : Integrable K volume)
    (hsupp : ∀ t : ℝ, 1 ≤ |t| →
      (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) = 0)
    (hnorm : ∀ t : ℝ,
      ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)‖ ≤ 1) :
    Integrable (fun t : ℝ =>
      ∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) volume := by
  let f : ℝ → ℂ := fun y => (K y : ℂ)
  let F : ℝ → ℂ := fun t => ∫ y : ℝ,
    Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * f y
  have hf : Integrable f := hK.ofReal
  have hFfourier (w : ℝ) : FourierTransform.fourier f w = F ((-2 * Real.pi) * w) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    simp only [smul_eq_mul, f, RCLike.inner_apply', starRingEnd_apply, star_trivial]
    congr 2
    push_cast
    ring
  have hFcont : Continuous F := by
    have hc : Continuous (FourierTransform.fourier f) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hf
    have heq : F = fun t : ℝ => FourierTransform.fourier f (t / (-2 * Real.pi)) := by
      funext t
      rw [hFfourier]
      congr 1
      field_simp
    rw [heq]
    fun_prop
  have hsupport : Function.support F ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    by_contra hn
    have ht' : 1 ≤ |t| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hn
      rcases hn with hn | hn
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith
    exact ht (hsupp t ht')
  have hmajor : Integrable ((Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  apply Integrable.mono' hmajor hFcont.aestronglyMeasurable
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem ht]
    exact hnorm t
  · rw [Set.indicator_of_notMem ht]
    have hzero : F t = 0 := by
      by_contra hn
      exact ht (hsupport hn)
    simp [hzero]

/-- For [an integrable function H](hyp:hH) and [an integrable](hyp:hK)
[continuous](hyp:hKcont) kernel K whose [Fourier transform vanishes outside
(−1, 1)](hyp:hsupp) and [has magnitude at most one](hyp:hnorm),
[the product y ↦ H(−y)·K(y) is integrable](goal). -/
theorem integrable_reflected_mul_unit_supported_kernel
    (H K : ℝ → ℝ) (hH : Integrable H volume)
    (hK : Integrable K volume) (hKcont : Continuous K)
    (hsupp : ∀ t : ℝ, 1 ≤ |t| →
      (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) = 0)
    (hnorm : ∀ t : ℝ,
      ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)‖ ≤ 1) :
    Integrable (fun y : ℝ => H (-y) * K y) volume := by
  let f : ℝ → ℂ := fun y => (K y : ℂ)
  let F : ℝ → ℂ := fun t => ∫ y : ℝ,
    Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * f y
  have hf : Integrable f := hK.ofReal
  have hfc : Continuous f := by fun_prop
  have hFfourier (w : ℝ) : FourierTransform.fourier f w = F ((-2 * Real.pi) * w) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    simp only [smul_eq_mul, f, RCLike.inner_apply', starRingEnd_apply, star_trivial]
    congr 2
    push_cast
    ring
  have hFint : Integrable F := integrable_unit_supported_kernel_fourier K hK hsupp hnorm
  have hFourierInt : Integrable (FourierTransform.fourier f) := by
    rw [funext hFfourier]
    exact hFint.comp_mul_left' (by positivity : (-2 * Real.pi : ℝ) ≠ 0)
  have hbound (y : ℝ) : ‖K y‖ ≤ ∫ w : ℝ, ‖FourierTransform.fourier f w‖ := by
    have hinv : (K y : ℂ) = FourierTransform.fourierInv
        (FourierTransform.fourier f) y :=
      (hf.fourierInv_fourier_eq hFourierInt hfc.continuousAt).symm
    rw [← Complex.norm_real (K y), hinv, Real.fourierInv_eq']
    simp only [smul_eq_mul, RCLike.inner_apply', starRingEnd_apply, star_trivial]
    calc
      ‖∫ w : ℝ, Complex.exp
          (((2 * Real.pi * (w * y) : ℝ) : ℂ) * Complex.I) *
          FourierTransform.fourier f w‖ ≤
          ∫ w : ℝ, ‖Complex.exp
            (((2 * Real.pi * (w * y) : ℝ) : ℂ) * Complex.I) *
            FourierTransform.fourier f w‖ := norm_integral_le_integral_norm _
      _ = _ := by
        congr 1
        ext w
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hHneg : Integrable (fun y : ℝ => H (-y)) volume := hH.comp_neg
  exact hHneg.mul_bdd hKcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

end Causalean.Stat.CLT.BerryEsseen
