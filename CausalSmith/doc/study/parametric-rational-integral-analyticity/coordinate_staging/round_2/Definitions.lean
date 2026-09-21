import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Building blocks for parametric rational integrals

This file defines the affine denominator and fixed-degree polynomial numerator used by the
parametric rational-integral analyticity API.
-/

namespace Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity

/-- Given [two real-valued functions](hyp:a,b), [a parameter](hyp:t), and [an input point](hyp:x),
[the affine denominator](goal) is given by [their displayed linear interpolation at that parameter](step:1). -/
def affineDenominator {α : Type*} (a b : α → ℝ) (t : ℝ) (x : α) : ℝ :=
  (1 - t) * a x + t * b x

/-- Given [a degree bound](hyp:N), [coefficient functions](hyp:c), [a parameter](hyp:t), and [an input point](hyp:x),
[the polynomial numerator](goal) is given by [the displayed finite polynomial evaluated at that parameter and point](step:1). -/
def polynomialNumerator {α : Type*} (N : ℕ) (c : Fin (N + 1) → α → ℝ)
    (t : ℝ) (x : α) : ℝ :=
  ∑ i, c i x * t ^ (i : ℕ)

end Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity
