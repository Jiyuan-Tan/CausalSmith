module
public import Causalean.Stat.CLT.BerryEsseen.SmoothingKernel
public import Mathlib.Analysis.Fourier.Inversion

/-! # Fourier inversion of the compact-frequency sinc kernel

This analytic identity is the independent inversion step needed to bound a
CDF difference after convolution with the fourth-power sinc kernel. It uses
the same positive-frequency Fourier convention as `sinc4Kernel_fourier_eq_zero`.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- At [positive bandwidth T](hyp:hT), [the fourth-power sinc density at every
point y equals 1/(2π) times the inverse Fourier integral, over the support
interval [−T, T], of its Fourier transform](goal). -/
theorem sinc4Kernel_fourier_inversion
    (T : ℝ) (hT : 0 < T) (y : ℝ) :
    (sinc4Kernel T y : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (-T)..T,
          Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) *
            (∫ u : ℝ,
              Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
                (sinc4Kernel T u : ℂ)) := by
  let f : ℝ → ℂ := fun u => (sinc4Kernel T u : ℂ)
  let F : ℝ → ℂ := fun t => ∫ u : ℝ,
    Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * f u
  let g : ℝ → ℂ := fun t =>
    Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * F t
  have hf : Integrable f := (sinc4Kernel_integrable T hT).ofReal
  have hfc : Continuous f := by
    dsimp [f, sinc4Kernel]
    fun_prop
  have hzero (t : ℝ) (ht : T ≤ |t|) : F t = 0 := by
    exact sinc4Kernel_fourier_eq_zero T t hT ht
  have hFfourier (w : ℝ) : FourierTransform.fourier f w = F ((-2 * Real.pi) * w) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with u
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
  have hFsupp : Function.support F ⊆ Set.Icc (-T) T := by
    intro t ht
    simp only [Function.mem_support, Set.mem_Icc] at *
    constructor
    · by_contra hn
      exact ht (hzero t (by rw [abs_of_nonpos (by linarith)]; linarith))
    · by_contra hn
      exact ht (hzero t (by rw [abs_of_nonneg (by linarith)]; linarith))
  have hFint : Integrable F :=
    (integrableOn_iff_integrable_of_support_subset hFsupp).mp hFcont.integrableOn_Icc
  have hFourierInt : Integrable (FourierTransform.fourier f) := by
    rw [funext hFfourier]
    exact hFint.comp_mul_left' (by positivity : (-2 * Real.pi : ℝ) ≠ 0)
  have hinv := hf.fourierInv_fourier_eq hFourierInt hfc.continuousAt (v := y)
  have hgsupp : Function.support g ⊆ Set.Ioc (-T) T := by
    intro t ht
    simp only [Function.mem_support, Set.mem_Ioc] at *
    constructor
    · by_contra hn
      exact ht (by dsimp [g]; rw [hzero t (by rw [abs_of_nonpos (by linarith)]; linarith)]; simp)
    · by_contra hn
      exact ht (by dsimp [g]; rw [hzero t (by rw [abs_of_nonneg (by linarith)]; linarith)]; simp)
  have hchange : (∫ w : ℝ, g ((-2 * Real.pi) * w)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, g t := by
    rw [Measure.integral_comp_mul_left]
    have hcoeff : |((-2 * Real.pi : ℝ)⁻¹)| = 1 / (2 * Real.pi) := by
      rw [abs_inv, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
      norm_num
    rw [hcoeff, Complex.real_smul]
  calc
    (sinc4Kernel T y : ℂ) = FourierTransform.fourierInv
        (FourierTransform.fourier f) y := hinv.symm
    _ = ∫ w : ℝ, g ((-2 * Real.pi) * w) := by
      rw [Real.fourierInv_eq']
      simp_rw [hFfourier]
      apply integral_congr_ae
      filter_upwards with w
      dsimp [g]
      simp only [starRingEnd_apply, star_trivial]
      congr 2
      push_cast
      ring
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, g t := hchange
    _ = _ := by
      rw [← intervalIntegral.integral_eq_integral_of_support_subset hgsupp]

end Causalean.Stat.CLT.BerryEsseen
