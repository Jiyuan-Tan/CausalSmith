/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.ChebyshevDerivativeWeights

/-!
# The Duffin--Schaeffer refinement of Markov's inequality

This module isolates the sharp discrete interpolation step behind Markov's
derivative inequality.  Control at the `L+1` extrema of the degree-`L`
Chebyshev polynomial already controls the derivative everywhere on `[-1,1]`.
-/

public section

open Polynomial Set

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-- If a real polynomial of degree at most `L`, with `L > 0`, is bounded by
`C` at every degree-`L` Chebyshev extremum, then its derivative is bounded by
`L² C` throughout `[-1,1]`. -/
theorem duffinSchaeffer_derivative_le
    (Q : Polynomial ℝ) {L : ℕ} (hL : 0 < L) (hQ : Q.natDegree ≤ L)
    {C : ℝ} (hC : 0 ≤ C)
    (hnodes : ∀ i, i ≤ L →
      |Q.eval (Polynomial.Chebyshev.node L i)| ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |Q.derivative.eval x| ≤ (L : ℝ) ^ 2 * C := by
  rw [eval_derivative_eq_sum_chebyshevDerivativeWeight Q hQ x]
  calc
    |∑ i ∈ Finset.range (L + 1),
        Q.eval (Polynomial.Chebyshev.node L i) * chebyshevDerivativeWeight L x i| ≤
        ∑ i ∈ Finset.range (L + 1),
          |Q.eval (Polynomial.Chebyshev.node L i) *
            chebyshevDerivativeWeight L x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (L + 1),
          C * |chebyshevDerivativeWeight L x i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (hnodes i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (abs_nonneg _)
    _ = C * ∑ i ∈ Finset.range (L + 1),
          |chebyshevDerivativeWeight L x i| := by rw [Finset.mul_sum]
    _ ≤ C * (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_abs_chebyshevDerivativeWeight_le_sq hL hx) hC
    _ = (L : ℝ) ^ 2 * C := by ring

end CausalSmith.Substrate.FinitePolynomialAlternationDuality
