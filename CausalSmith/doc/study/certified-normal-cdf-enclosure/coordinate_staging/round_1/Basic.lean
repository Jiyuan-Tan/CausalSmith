import Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.NormalCDF

/-!
# Basic operations for certified standard-normal CDF enclosures

This module fixes the supported numerical range and target cell width, and
packages the exact interval reflection used to transport a certificate between
positive and negative endpoints.  The analytic CDF is Causalean's
`stdNormalCDF`; all reported endpoints remain exact rationals.
-/

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- The requested maximum width of a high-precision caller cell is exactly
`10⁻¹²`, represented as a rational rather than a floating-point number. -/
def targetWidth : ℚ := 1 / 10 ^ 12

/-- The reusable checker is required to support endpoints of absolute value at
most `193 / 5`. -/
def supportedEndpointBound : ℚ := 193 / 5

/-- The central-series/tail boundary is the exact rational number eight. -/
def centralCutoff : ℚ := 8

/-- Reflecting an interval `I` across one half produces the interval `1 - I`. -/
def reflectInterval (I : RatInterval) : RatInterval :=
  (RatInterval.point 1).sub I

/-- If an interval contains `x`, its reflection contains `1 - x`. -/
theorem reflectInterval_sound {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (reflectInterval I).Contains (1 - x) := by
  rcases hx with ⟨hlo, hhi⟩
  simp only [reflectInterval, RatInterval.sub, RatInterval.add, RatInterval.neg,
    RatInterval.point, RatInterval.Contains, Rat.cast_add, Rat.cast_neg,
    Rat.cast_one]
  exact ⟨sub_le_sub_left hhi 1, sub_le_sub_left hlo 1⟩

/-- An enclosure of `Φ(x)` reflects to an enclosure of `Φ(-x)`. -/
theorem reflectInterval_stdNormalCDF_sound {I : RatInterval} {x : ℝ}
    (hx : I.Contains (Causalean.Mathlib.stdNormalCDF x)) :
    (reflectInterval I).Contains (Causalean.Mathlib.stdNormalCDF (-x)) := by
  rw [Causalean.Mathlib.stdNormalCDF_neg]
  exact reflectInterval_sound hx

/-- Every endpoint lies either in the central regime or strictly in the tail
regime; this is the exhaustive case split used by the top-level checker. -/
theorem central_or_tail (q : ℚ) :
    |q| ≤ centralCutoff ∨ centralCutoff < |q| := by
  exact le_or_gt |q| centralCutoff

/-- At [a rational endpoint](hyp:q) with [nonnegative value](hyp:hq), [the standard-normal CDF](goal) is one half plus the density normalization constant times the unnormalised Gaussian integral from zero to that endpoint. -/
theorem stdNormalCDF_eq_half_add_scale_mul_integral (q : ℚ) (hq : 0 ≤ q) :
    Causalean.Mathlib.stdNormalCDF (q : ℝ) =
      (1 / 2 : ℝ) + (1 / Real.sqrt (2 * Real.pi)) *
        (∫ t in (0 : ℝ)..(q : ℝ), Real.exp (-(t ^ 2) / 2)) := by
  rw [Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.stdNormalCDF_eq_half_add_rescaled_integral
    q hq]
  congr 1
  have hsubst :
      (∫ u in (0 : ℝ)..1,
        (q : ℝ) * Causalean.Mathlib.stdNormalPDF ((q : ℝ) * u)) =
      ∫ x in (0 : ℝ)..(q : ℝ), Causalean.Mathlib.stdNormalPDF x := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.mul_integral_comp_mul_left]
    simp
  rw [hsubst, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  simp [Causalean.Mathlib.stdNormalPDF,
    ProbabilityTheory.gaussianPDFReal]

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure
