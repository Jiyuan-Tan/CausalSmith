module
public import Causalean.Stat.CLT.BerryEsseen.GaussianSineInversion
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSpectralComparison

/-! # Prawitz's Gaussian CDF smoothing inequality

This four-term Fourier inequality separates low-frequency approximation,
high-frequency damping, the bounded principal correction, and the Gaussian
tail. It is the analytic transfer needed by a constant-one Berry–Esseen proof.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a scalar probability law with finite first moment](hyp:hfirst) and
[positive cutoffs U0 ≤ U](hyp:hU0,hcut), [its CDF at every threshold x differs
from the standard Gaussian CDF by at most the four Prawitz Fourier terms: the
filtered low-frequency characteristic-function discrepancy on [0, U0], the
filtered high-frequency characteristic-function modulus on [U0, U], the
Gaussian principal correction on [0, U0], and the Gaussian tail beyond
U0](goal). -/
theorem normal_cdf_prawitz_smoothing
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun y : ℝ => y) μ)
    (U0 U : ℝ) (hU0 : 0 < U0) (hcut : U0 ≤ U) (x : ℝ) :
    |(μ (Set.Iic x)).toReal -
      ((gaussianReal 0 1) (Set.Iic x)).toReal| ≤
      (2 / U) * (∫ t in (0 : ℝ)..U0,
        ‖prawitzKernel (t / U)‖ *
          ‖charFun μ t - charFun (gaussianReal 0 1) t‖) +
      (2 / U) * (∫ t in U0..U,
        ‖prawitzKernel (t / U)‖ * ‖charFun μ t‖) +
      2 * (∫ t in (0 : ℝ)..U0,
        ‖prawitzKernel (t / U) / (U : ℂ) -
          Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
          Real.exp (-(t ^ 2 / 2))) +
      (1 / Real.pi) * (∫ t in Set.Ioi U0,
        Real.exp (-(t ^ 2 / 2)) / t) := by
  apply prawitz_cdf_error_of_spectral_bound μ U (hU0.trans_le hcut) x
  have hspec := prawitz_gaussian_sine_spectral_bound μ hfirst U0 U hU0 hcut x
  have he :
      1 + (∫ y, prawitzSignApprox (U * (x - y)) ∂μ) -
        2 * ((gaussianReal 0 1) (Set.Iic x)).toReal =
      2 * ((∫ y, prawitzSignApprox (U * (x - y)) ∂μ) / 2 -
        (1 / Real.pi) * (∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t)) := by
    rw [gaussian_cdf_sine_inversion x]
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [hspec]

end Causalean.Stat.CLT.BerryEsseen
