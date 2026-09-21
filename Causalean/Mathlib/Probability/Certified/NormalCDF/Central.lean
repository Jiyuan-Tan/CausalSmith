module
public import Causalean.Mathlib.Probability.Certified.NormalCDF.PowerSeries
public import Causalean.Mathlib.Probability.Certified.NormalCDF.Normalization

/-!
# Central-range standard-normal CDF certificates

Central certificates combine an exact Gaussian-integral alternating enclosure
with a certified rational normalization constant.  Absolute value reduces the
work to a nonnegative endpoint and `reflectInterval` transports the result back
to a negative endpoint.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Analysis.IntervalArithmetic.Contour
/-- Finite certificate data for central evaluation: a series degree and a
certified enclosure of `1 / sqrt (2π)`. -/
structure CentralCertificate where
  /-- Last included Gaussian-integral series index. -/
  degree : ℕ
  /-- Certified normalization constant used to scale the raw integral. -/
  normalization : NormalizationCertificate

/-- The positive-magnitude central evaluator returns `1/2` plus the product of
the normalization enclosure and alternating integral enclosure. -/
def centralMagnitudeInterval (x : ℚ) (c : CentralCertificate) : RatInterval :=
  (RatInterval.point (1 / 2)).add
    (c.normalization.enclosure.mul (gaussianIntegralInterval x c.degree))

/-- The signed central evaluator uses CDF symmetry when the endpoint is
negative. -/
def centralInterval (q : ℚ) (c : CentralCertificate) : RatInterval :=
  if 0 ≤ q then centralMagnitudeInterval |q| c
  else reflectInterval (centralMagnitudeInterval |q| c)

/-- The central checker validates normalization, the cutoff, the exact
alternating-tail condition, and refinement into the caller-supplied interval. -/
def centralCheck (q : ℚ) (c : CentralCertificate) (reported : RatInterval) : Bool :=
  normalizationCheck c.normalization &&
    decide (|q| ≤ centralCutoff ∧
      |q| ^ 2 ≤ 2 * (c.degree + 2 : ℕ) ∧
      reported.lo ≤ (centralInterval q c).lo ∧
      (centralInterval q c).hi ≤ reported.hi)

/-- When [the central-series checker accepts the supplied certificate and interval](hyp:hcheck), [that interval contains the standard-normal CDF at the rational endpoint](goal). -/
theorem centralCheck_sound {q : ℚ} {c : CentralCertificate} {reported : RatInterval}
    (hcheck : centralCheck q c reported = true) :
    reported.Contains (Causalean.Mathlib.stdNormalCDF (q : ℝ)) := by
  unfold centralCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hnormalization, hconditions⟩
  have hconditions' :
      |q| ≤ centralCutoff ∧
        |q| ^ 2 ≤ 2 * (c.degree + 2 : ℕ) ∧
        reported.lo ≤ (centralInterval q c).lo ∧
        (centralInterval q c).hi ≤ reported.hi :=
    of_decide_eq_true hconditions
  rcases hconditions' with ⟨_, hmono, hlo, hhi⟩
  have hmagnitude :
      (centralMagnitudeInterval |q| c).Contains
        (Causalean.Mathlib.stdNormalCDF (((|q| : ℚ) : ℝ))) := by
    rw [stdNormalCDF_eq_half_add_scale_mul_integral |q| (abs_nonneg q)]
    have hhalf : (RatInterval.point (1 / 2)).Contains (1 / 2 : ℝ) := by
      norm_num [RatInterval.point, RatInterval.Contains]
    exact RatInterval.add_sound hhalf
      (RatInterval.mul_sound (c.normalization.sound hnormalization)
        (gaussianIntegralInterval_sound |q| (abs_nonneg q) c.degree hmono))
  have hcentral :
      (centralInterval q c).Contains
        (Causalean.Mathlib.stdNormalCDF (q : ℝ)) := by
    by_cases hq : 0 ≤ q
    · simpa [centralInterval, hq, abs_of_nonneg hq] using hmagnitude
    · have hqneg : q < 0 := lt_of_not_ge hq
      have hqabs : q = -|q| := by simp [abs_of_neg hqneg]
      rw [centralInterval, if_neg hq]
      have hreflected := reflectInterval_stdNormalCDF_sound hmagnitude
      rw [show (q : ℝ) = -(((|q| : ℚ) : ℝ)) by exact_mod_cast hqabs]
      exact hreflected
  exact RatInterval.Contains.mono ⟨hlo, hhi⟩ hcentral

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure
