module
public import Causalean.Mathlib.Probability.Certified.NormalCDFInterval

/-!
# Basic operations for certified standard-normal CDF enclosures

This module fixes the endpoint and width acceptance limits, and packages the
exact interval reflection used to transport a certificate between positive
and negative endpoints.  The analytic CDF is Causalean's
`stdNormalCDF`; all reported endpoints remain exact rationals.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Analysis.IntervalArithmetic.Contour
/-- [The accepted maximum width of a fine-checker interval](goal) is exactly
`10⁻¹²`; this limit constrains supplied certificates and does not assert that
certificates of that width can be generated. -/
def targetWidth : ℚ := 1 / 10 ^ 12

/-- [The endpoint acceptance bound](goal) is exactly `193 / 5`; this limit is
checked on supplied certificates and does not assert that certificates can be
generated throughout the range. -/
def acceptedEndpointBound : ℚ := 193 / 5

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

/-- At [a rational endpoint](hyp:q), [its central-or-tail classification](goal)
says that its absolute value is at most the cutoff or strictly above it. -/
theorem central_or_tail (q : ℚ) :
    |q| ≤ centralCutoff ∨ centralCutoff < |q| := by
  exact le_or_gt |q| centralCutoff

/-- At [a rational endpoint](hyp:q) with [nonnegative value](hyp:hq),
[the standard-normal CDF](goal) is one half plus the density normalization constant times the
unnormalised Gaussian integral from zero to that endpoint. -/
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
