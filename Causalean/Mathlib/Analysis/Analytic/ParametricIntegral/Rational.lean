module
public import Causalean.Mathlib.Analysis.Analytic.ParametricIntegral.Rational.Affine
public import Causalean.Mathlib.Analysis.Analytic.ParametricIntegral.Rational.Definitions
public import Causalean.Mathlib.Analysis.Analytic.ParametricIntegral.Rational.Examples
public import Causalean.Mathlib.Analysis.Analytic.ParametricIntegral.Rational.Main
public import Causalean.Mathlib.Analysis.Analytic.ParametricIntegral.Rational.PowerSeries

/-!
# Analytic polynomial-over-affine integrals

Real analyticity in a scalar parameter t of integrals of the form
∫_K (∑_{i ≤ N} cᵢ(x)·tⁱ) / ((1 − t)·a(x) + t·b(x)) dμ(x). If K is a measurable set of finite
measure, the coefficient functions cᵢ and the endpoint functions a, b are measurable, each cᵢ is
bounded on K, and the affine denominator is bounded away from zero by some ε > 0 for all t in an
open set O and all x in K, then the integral is a real-analytic function of t on O. The proof
expands the reciprocal of the denominator as a geometric series around each parameter value and
integrates the dominated power series term by term.

## Contents

* `Definitions` — the affine denominator `affineDenominator` and the fixed-degree numerator
  `polynomialNumerator`.
* `Affine` — the denominator stays uniformly away from zero near a parameter value, and its
  reciprocal has a geometric power-series expansion there.
* `PowerSeries` — `analyticAt_integral_of_powerSeries_domination`: under a finite measure, a power
  series in t with summably dominated coefficient functions integrates term by term to an analytic
  function.
* `Main` — `analyticOnNhd_setIntegral_polynomial_div_affine_of_uniform_nonzero`, the analyticity
  theorem above, with pointwise variants at a single parameter value.
* `Examples` — t ↦ ∫₀¹ (1 + t·x)/(2 + t·x) dx is real analytic on (−1, 1).
-/
