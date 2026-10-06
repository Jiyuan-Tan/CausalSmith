module
public import Causalean.Mathlib.Probability.HermiteGaussian
public import Causalean.Mathlib.Probability.HermiteGenerating

/-!
# Classical facts for probabilists’ Hermite polynomials

This facade combines the exponential generating-series and standard-Gaussian
orthogonality theorems for Mathlib’s probabilists’ Hermite polynomials with
Mathlib’s zero-order identity in the exact neutral three-part interface.
-/

public section

open MeasureTheory Polynomial ProbabilityTheory

namespace Causalean.Mathlib.Probability


/-- Probabilists' Hermite polynomials [satisfy the real exponential generating
series, Gaussian orthogonality with factorial norms, and the zero-order identity](goal). -/
theorem classicalHermiteFacts :
    (∀ z t : ℝ, HasSum (fun j : ℕ =>
      (Polynomial.aeval z (Polynomial.hermite j) : ℝ) * t ^ j / (Nat.factorial j : ℝ))
        (Real.exp (z * t - t ^ 2 / 2))) ∧
    (∀ j k : ℕ, (∫ z, (Polynomial.aeval z (Polynomial.hermite j) : ℝ) *
        Polynomial.aeval z (Polynomial.hermite k) ∂gaussianReal 0 1) =
        if j = k then (Nat.factorial j : ℝ) else 0) ∧ Polynomial.hermite 0 = 1 := by
  exact ⟨hasSum_hermite, integral_hermite_mul, hermite_zero⟩


end Causalean.Mathlib.Probability

