/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.ChebyshevRootProduct

/-!
# Complex vertical-line domination for Chebyshev polynomials

This module isolates the complex-modulus input in the Duffin--Schaeffer proof
of Markov's inequality.  On every horizontal slice, the modulus of `T_L` above
`[-1,1]` is dominated by its modulus above the endpoint `1`.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- Above any point `x` of `[-1,1]`, the complex modulus of the degree-`L`
Chebyshev polynomial is no larger than its modulus at the point with the same
imaginary part above the endpoint `1`. [the stated inputs](hyp:L,x,hx,y) establish [the stated conclusion](goal). -/
theorem norm_eval_chebyshev_le_endpoint_vertical
    {L : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) (y : ℝ) :
    ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((1 : ℂ) + (y : ℂ) * Complex.I)‖ := by
  by_cases hL : L = 0
  · subst L
    simp
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  calc
    ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ =
        ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).leadingCoeff‖ *
          ∏ k ∈ Finset.range L,
            ‖((x - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ :=
      norm_eval_chebyshev_eq_leadingCoeff_mul_rootProduct hLpos x y
    _ ≤ ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).leadingCoeff‖ *
          ∏ k ∈ Finset.range L,
            ‖((1 - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ :=
      mul_le_mul_of_nonneg_left
        (prod_norm_sub_chebyshevZero_le_endpoint hLpos hx y) (norm_nonneg _)
    _ = ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((1 : ℂ) + (y : ℂ) * Complex.I)‖ := by
      simpa using
        (norm_eval_chebyshev_eq_leadingCoeff_mul_rootProduct hLpos (1 : ℝ) y).symm

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
