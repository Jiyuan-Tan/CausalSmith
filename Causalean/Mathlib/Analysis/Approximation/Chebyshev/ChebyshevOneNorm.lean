module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.PolynomialOneNorm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Silver-ratio coefficient one-norm bound for Chebyshev polynomials

The Chebyshev recurrence gives the silver-ratio coefficient one-norm estimate used when a
tensor Chebyshev expansion is converted to monomial coefficients.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev

open Polynomial
open scoped BigOperators

private theorem oneNorm_range (p : Polynomial ℝ) {m : ℕ} (hp : p.natDegree < m) :
    polynomialCoeffOneNorm p = ∑ k ∈ Finset.range m, |p.coeff k| := by
  change p.sum (fun _ c => |c|) = _
  exact p.sum_over_range' (fun _ => abs_zero) m hp

private theorem oneNorm_sub_le (p q : Polynomial ℝ) :
    polynomialCoeffOneNorm (p - q) ≤ polynomialCoeffOneNorm p +
      polynomialCoeffOneNorm q := by
  let m := max p.natDegree q.natDegree + 1
  rw [oneNorm_range (p - q)
      (lt_of_le_of_lt (natDegree_sub_le _ _) (Nat.lt_succ_self _)),
    oneNorm_range p (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)),
    oneNorm_range q (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [sub_eq_add_neg, coeff_add, coeff_neg, abs_neg] using
      abs_add_le (p.coeff i) (-q.coeff i)

private theorem oneNorm_smul (c : ℝ) (p : Polynomial ℝ) :
    polynomialCoeffOneNorm (c • p) = |c| * polynomialCoeffOneNorm p := by
  rw [oneNorm_range (c • p)
      (lt_of_le_of_lt (natDegree_smul_le _ _) (Nat.lt_succ_self _)),
    oneNorm_range p (Nat.lt_succ_self _)]
  simp only [coeff_smul, smul_eq_mul, abs_mul, Finset.mul_sum]

private theorem oneNorm_X_mul (p : Polynomial ℝ) :
    polynomialCoeffOneNorm (X * p) = polynomialCoeffOneNorm p := by
  by_cases hp : p = 0
  · simp [hp, polynomialCoeffOneNorm,
      Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1]
  · rw [oneNorm_range (X * p) (m := p.natDegree + 2)
        (by rw [natDegree_X_mul hp]; omega),
      oneNorm_range p (Nat.lt_succ_self _)]
    rw [show p.natDegree + 2 = (p.natDegree + 1) + 1 by omega,
      Finset.sum_range_succ']
    simp only [coeff_X_mul_zero, abs_zero, add_zero, Nat.succ_eq_add_one, coeff_X_mul]

/-- For [a natural-number order n](hyp:n), [the sum of the absolute values of the monomial coefficients of the n-th first-kind Chebyshev polynomial is at most (1 + √2)ⁿ](goal).

The sum of the absolute monomial coefficients of the `n`th Chebyshev polynomial is at
most `(1 + √2)^n`. The recurrence has characteristic equation `x² = 2x + 1`.

Prove the one-norm triangle inequality and that multiplying by `X` preserves it, then induct
using `T_(n+2) = 2 X T_(n+1) - T_n`. The existing `chebyshev_coeffL1_le` in Causalean uses
the coarser factor `3`, so it does not imply this bound.
-/
theorem polynomialCoeffOneNorm_chebyshev_le (n : ℕ) :
    polynomialCoeffOneNorm (Polynomial.Chebyshev.T ℝ (n : ℤ)) ≤
      (1 + Real.sqrt 2) ^ n := by
  let r : ℝ := 1 + Real.sqrt 2
  have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
  have hr_sq : r ^ 2 = 2 * r + 1 := by
    dsimp [r]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  change polynomialCoeffOneNorm (Polynomial.Chebyshev.T ℝ (n : ℤ)) ≤ r ^ n
  induction n using Nat.twoStepInduction with
  | zero =>
      change polynomialCoeffOneNorm (Polynomial.Chebyshev.T ℝ 0) ≤ 1
      rw [Polynomial.Chebyshev.T_zero,
        oneNorm_range (1 : Polynomial ℝ) (m := 1) (by simp)]
      simp
  | one =>
      norm_num only [Nat.cast_one, pow_one]
      rw [Polynomial.Chebyshev.T_one,
        oneNorm_range (X : Polynomial ℝ) (m := 2) (by simp)]
      norm_num [Finset.sum_range_succ, coeff_X, r]
  | more n hn hn1 =>
      have hT : Polynomial.Chebyshev.T ℝ ((n + 2 : ℕ) : ℤ) =
          (2 : ℝ) • (X * Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) -
            Polynomial.Chebyshev.T ℝ (n : ℤ) := by
        convert Polynomial.Chebyshev.T_add_two ℝ (n : ℤ) using 1
        · norm_num
        · simp only [Polynomial.smul_eq_C_mul]
          norm_num
          rw [Polynomial.C_ofNat]
          ring
      rw [hT]
      calc
        polynomialCoeffOneNorm ((2 : ℝ) •
            (X * Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) -
              Polynomial.Chebyshev.T ℝ (n : ℤ))
            ≤ polynomialCoeffOneNorm ((2 : ℝ) •
                (X * Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ))) +
                polynomialCoeffOneNorm (Polynomial.Chebyshev.T ℝ (n : ℤ)) :=
              oneNorm_sub_le _ _
        _ = 2 * polynomialCoeffOneNorm
              (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) +
              polynomialCoeffOneNorm (Polynomial.Chebyshev.T ℝ (n : ℤ)) := by
            rw [oneNorm_smul, oneNorm_X_mul]
            norm_num
        _ ≤ 2 * r ^ (n + 1) + r ^ n := by gcongr
        _ = r ^ (n + 2) := by
            calc
              2 * r ^ (n + 1) + r ^ n = (2 * r + 1) * r ^ n := by
                rw [pow_succ]
                ring
              _ = r ^ 2 * r ^ n := by rw [hr_sq]
              _ = r ^ (n + 2) := by rw [pow_add]; ring

end Causalean.Mathlib.Analysis.Approximation.Chebyshev

