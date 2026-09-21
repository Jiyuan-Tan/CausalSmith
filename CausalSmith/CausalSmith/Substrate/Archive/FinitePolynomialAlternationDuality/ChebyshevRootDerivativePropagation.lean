/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.ChebyshevVerticalModulus
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.HalfPlaneDerivativeComparison

/-!
# Propagating derivative control from Chebyshev roots

This module isolates the real first-derivative specialization of the
Duffin--Schaeffer comparison theorem.  Control of a degree-`L` polynomial's
derivative at every zero of `T_L` propagates to the sharp global `L²` bound
on `[-1,1]`.
-/

public section

open Polynomial Set

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-- If a degree-at-most-`L` real polynomial has derivative no larger than
`T_L'` at every zero of `T_L`, then its derivative is bounded by `L²`
throughout `[-1,1]`. -/
theorem abs_eval_derivative_le_sq_of_chebyshev_root_control
    {L : ℕ} (hL : 0 < L) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ L)
    (hroots : ∀ z : ℝ,
      (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval z = 0 →
        |Q.derivative.eval z| ≤
          |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval z|)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |Q.derivative.eval x| ≤ (L : ℝ) ^ 2 := by
  have hendpoint := abs_eval_derivative_le_chebyshev_endpoint_of_root_control
    hL Q hQ hroots hx (fun y ↦ norm_eval_chebyshev_le_endpoint_vertical hx y)
  rw [Polynomial.Chebyshev.derivative_T_eval_one] at hendpoint
  simpa [abs_of_nonneg (sq_nonneg (L : ℝ))] using hendpoint

end CausalSmith.Substrate.FinitePolynomialAlternationDuality
