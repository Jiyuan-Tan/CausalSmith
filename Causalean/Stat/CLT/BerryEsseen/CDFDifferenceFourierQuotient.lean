module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourier

/-! # Weighted Fourier magnitude of a CDF difference

The nonzero-frequency CDF Fourier identity becomes an equality of truncated
real magnitude integrals. Frequency zero is a null singleton for Lebesgue
measure, so no atomlessness of either probability law is required.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [two probability laws with finite first moments](hyp:hμ,hν),
[the integral over [−T, T] of the magnitude of the Fourier transform of their
CDF difference equals the integral over [−T, T] of their
characteristic-function discrepancy divided by |t|](goal). -/
theorem cdf_difference_fourier_magnitude_integral
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ => y) μ)
    (hν : Integrable (fun y : ℝ => y) ν) (T : ℝ) :
    (∫ t in (-T)..T,
      ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
        (((μ (Set.Iic y)).toReal - (ν (Set.Iic y)).toReal : ℝ) : ℂ)‖) =
    ∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t| := by
  /- Take norms in cdf_difference_fourier_identity for t≠0.
  norm_mul, Complex.norm_real, Real.norm_eq_abs, and Complex.norm_I
  give |t|*‖Fourier H t‖=‖charFun μ t-charFun ν t‖.
  Divide by |t|, then use intervalIntegral.integral_congr_ae and the
  nullity of {0}. This is a congruence of integrals, not an inequality,
  and introduces no new probabilistic assumptions. -/
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  intro _
  have hnorm := congrArg norm (cdf_difference_fourier_identity μ ν hμ hν t ht)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    one_mul] at hnorm
  apply (eq_div_iff (abs_ne_zero.mpr ht)).2
  simpa only [mul_comm] using hnorm

end Causalean.Stat.CLT.BerryEsseen
