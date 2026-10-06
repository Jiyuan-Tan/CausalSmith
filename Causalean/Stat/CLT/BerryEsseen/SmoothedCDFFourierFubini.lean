module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourier
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourierShift
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceIntegrable
public import Causalean.Stat.CLT.BerryEsseen.SincKernelInversion
public import Causalean.Stat.CLT.BerryEsseen.SmoothedCDFFourierSwap

/-! # Fourier representation of a smoothed CDF difference

This isolates the Fubini and frequency-zero steps in the smoothing bound.
The real CDF difference has an integrable envelope from the first moments,
and the sinc kernel has compact Fourier support.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [two probability laws μ and ν with finite first moments](hyp:hμ,hν) and
[a positive bandwidth T](hyp:hT), [the convolution at z of their CDF
difference with the fourth-power sinc density equals 1/(2π) times the
integral over [−T, T] of exp(−itz)·i·(φ_μ(t) − φ_ν(t))/t times the kernel's
Fourier transform at t](goal). The quotient is assigned zero at frequency
zero, which does not change the interval integral. -/
theorem sinc4_smoothed_cdf_fourier_identity
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ => y) μ)
    (hν : Integrable (fun y : ℝ => y) ν)
    (T : ℝ) (hT : 0 < T) (z : ℝ) :
    ((∫ y : ℝ,
      ((μ (Set.Iic (z - y))).toReal -
        (ν (Set.Iic (z - y))).toReal) * sinc4Kernel T y : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (-T)..T,
          (Complex.exp (((-(t * z) : ℝ) : ℂ) * Complex.I) *
            (Complex.I * (charFun μ t - charFun ν t)) / (t : ℂ)) *
            (∫ u : ℝ,
              Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
                (sinc4Kernel T u : ℂ)) := by
  /- Apply `sinc4_smoothed_cdf_fourier_swap`, then
  `cdf_difference_fourier_shift`. Apply
  `cdf_difference_fourier_identity` for t ≠ 0; divide its displayed
  `t * integral = i * (charFun μ t - charFun ν t)` equality in ℂ using
  `Complex.ofReal_ne_zero.mpr ht`. Identify the two interval integrands
  almost everywhere by excluding the singleton {0}; `volume_singleton`
  and `intervalIntegral.integral_congr_ae` should dispose of that point.
  Move the reflected phase and kernel transform outside the spatial
  integral using `integral_const_mul`, keeping the factor order explicit.
  The displayed order of complex factors is chosen so the remaining bound
  follows directly from `norm_integral_le_of_norm_le`. -/
  have hfreq (t : ℝ) (ht : t ≠ 0) :
      (∫ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ)) =
        Complex.I * (charFun μ t - charFun ν t) / (t : ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr ht)).2
    simpa only [mul_comm] using cdf_difference_fourier_identity μ ν hμ hν t ht
  rw [sinc4_smoothed_cdf_fourier_swap μ ν hμ hν T hT z]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht _
  rw [cdf_difference_fourier_shift μ ν hμ hν t z, hfreq t ht]
  ring

end Causalean.Stat.CLT.BerryEsseen
