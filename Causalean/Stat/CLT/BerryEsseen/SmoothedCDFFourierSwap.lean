module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceIntegrable
public import Causalean.Stat.CLT.BerryEsseen.SincKernelInversion

/-! # Fubini interchange for a smoothed CDF difference

This module isolates the absolute-integrability and Fubini step after
inserting the compact-frequency inverse Fourier formula for sinc fourth.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [two probability laws with finite first moments](hyp:hμ,hν) and
[a positive bandwidth T](hyp:hT), [the convolution at z of their CDF
difference with the fourth-power sinc density equals 1/(2π) times the
integral over [−T, T] of the kernel's Fourier transform times the spatial
transform of the shifted CDF difference](goal); no change of variables or
division by frequency is used. -/
theorem sinc4_smoothed_cdf_fourier_swap
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ => y) μ)
    (hν : Integrable (fun y : ℝ => y) ν)
    (T : ℝ) (hT : 0 < T) (z : ℝ) :
    ((∫ y : ℝ,
      ((μ (Set.Iic (z - y))).toReal -
        (ν (Set.Iic (z - y))).toReal) * sinc4Kernel T y : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (-T)..T,
          (∫ u : ℝ,
            Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
              (sinc4Kernel T u : ℂ)) *
            (∫ y : ℝ,
              Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) *
                (((μ (Set.Iic (z - y))).toReal -
                  (ν (Set.Iic (z - y))).toReal : ℝ) : ℂ)) := by
  /- Insert `sinc4Kernel_fourier_inversion`. The spatial factor is
  integrable by `integrable_cdf_difference_of_first_moments` and reflection;
  the frequency transform is bounded by `sinc4Kernel_integral_eq_one`.
  Establish joint integrability on the finite interval, swap, then pull out
  the constant and coerce the real integral to a complex integral. -/
  let D : ℝ → ℝ := fun y =>
    (μ (Set.Iic (z - y))).toReal - (ν (Set.Iic (z - y))).toReal
  let K : ℝ → ℂ := fun t => ∫ u : ℝ,
    Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (sinc4Kernel T u : ℂ)
  let F : ℝ → ℝ → ℂ := fun t y =>
    K t * (Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * (D y : ℂ))
  have hD : Integrable D volume := by
    exact (integrable_cdf_difference_of_first_moments μ ν hμ hν).comp_sub_left z
  have hkernel : Integrable (fun u : ℝ => (sinc4Kernel T u : ℂ)) volume :=
    (sinc4Kernel_integrable T hT).ofReal
  have hKcont : Continuous K := by
    let f : ℝ → ℂ := fun u => (sinc4Kernel T u : ℂ)
    have hFfourier (w : ℝ) : FourierTransform.fourier f w = K ((-2 * Real.pi) * w) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with u
      simp only [smul_eq_mul, f, RCLike.inner_apply', starRingEnd_apply, star_trivial]
      congr 2
      push_cast
      ring
    have hc : Continuous (FourierTransform.fourier f) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hkernel
    have heq : K = fun t : ℝ => FourierTransform.fourier f (t / (-2 * Real.pi)) := by
      funext t
      rw [hFfourier]
      congr 1
      field_simp
    rw [heq]
    fun_prop
  have hKbound (t : ℝ) : ‖K t‖ ≤ 1 := by
    calc
      ‖K t‖ ≤ ∫ u : ℝ, ‖Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
          (sinc4Kernel T u : ℂ)‖ := norm_integral_le_integral_norm _
      _ = ∫ u : ℝ, sinc4Kernel T u := by
        apply integral_congr_ae
        filter_upwards with u
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I,
          one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sinc4Kernel_nonneg T hT u)]
      _ = 1 := sinc4Kernel_integral_eq_one T hT
  have hDℂ : Integrable (fun y : ℝ => (D y : ℂ)) volume := hD.ofReal
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (-T) T)) := by
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)]
    infer_instance
  have hmajor : Integrable (fun p : ℝ × ℝ => ‖(D p.2 : ℂ)‖)
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) :=
    hDℂ.norm.comp_snd _
  have hF : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) := by
    apply Integrable.mono' hmajor
    · have hc : Continuous (fun p : ℝ × ℝ =>
          K p.1 * Complex.exp (((-(p.1 * p.2) : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      have hd : AEStronglyMeasurable (fun p : ℝ × ℝ => (D p.2 : ℂ))
          ((volume.restrict (Set.uIoc (-T) T)).prod volume) :=
        (hDℂ.comp_snd _).aestronglyMeasurable
      convert hc.aestronglyMeasurable.mul hd using 1
      ext p
      simp only [F, Function.uncurry, Pi.mul_apply]
      ring
    · filter_upwards with p
      dsimp [F, Function.uncurry]
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hKbound p.1)
  have hswap := intervalIntegral_integral_swap (a := -T) (b := T) hF
  calc
    ((∫ y : ℝ, D y * sinc4Kernel T y : ℝ) : ℂ) =
        ∫ y : ℝ, (D y : ℂ) * (sinc4Kernel T y : ℂ) := by
      calc
        ((∫ y : ℝ, D y * sinc4Kernel T y : ℝ) : ℂ) =
            ∫ y : ℝ, ((D y * sinc4Kernel T y : ℝ) : ℂ) :=
          (integral_complex_ofReal).symm
        _ = _ := by
          congr 1
          ext y
          push_cast
          rfl
    _ = ∫ y : ℝ, (D y : ℂ) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T,
              Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * K t) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [sinc4Kernel_fourier_inversion T hT y]
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y : ℝ, ∫ t in (-T)..T, F t y := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      calc
        (D y : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T,
              Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * K t) =
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ((D y : ℂ) * ∫ t in (-T)..T,
                Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * K t) := by ring
        _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ t in (-T)..T, F t y := by
          congr 1
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t _
          dsimp [F]
          ring
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, ∫ y : ℝ, F t y := by rw [hswap]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [F, K, D]
      rw [← integral_const_mul]

end Causalean.Stat.CLT.BerryEsseen
