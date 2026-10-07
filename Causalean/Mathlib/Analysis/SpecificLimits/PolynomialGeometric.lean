/-
Copyright (c) 2026 CausalSmith contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Polynomially weighted geometric series

This module supplies explicit geometric majorants for series whose terms are a polynomial
weight times a geometric power. The shift by two is convenient when the first relevant size is
two, while the statements themselves are independent of any probabilistic application.
-/
public section

namespace Causalean.Mathlib.Analysis.SpecificLimits.PolynomialGeometric

/-- A natural-number index shifted by two is bounded by the corresponding dyadic power.
[The asserted bound holds](goal). -/
lemma nat_add_two_le_two_pow_succ (j : ℕ) : (j + 2 : ℝ) ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    push_cast
    nlinarith

/-- A polynomially weighted geometric term has an explicit geometric majorant when
[the base is nonnegative](hyp:hz). [The asserted termwise bound holds](goal). -/
lemma polynomial_geometric_term_le (r j : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (j + 2 : ℝ) ^ r * z ^ (j + 2) ≤
      2 ^ r * z ^ 2 * (2 ^ r * z) ^ j := by
  calc
    _ ≤ (2 ^ (j + 1) : ℝ) ^ r * z ^ (j + 2) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (nat_add_two_le_two_pow_succ j) r)
        (pow_nonneg hz _)
    _ = _ := by
      rw [mul_pow, pow_add z j 2, ← pow_mul, ← pow_mul]
      rw [show (j + 1) * r = r + r * j by ring, pow_add]
      ring

/-- A polynomially weighted geometric series is summable when [the base is nonnegative](hyp:hz)
and [the explicit geometric ratio is at most one half](hyp:hsmall).
[The asserted summability holds](goal). -/
lemma polynomial_geometric_series_summable (r : ℕ) (z : ℝ) (hz : 0 ≤ z)
    (hsmall : 2 ^ r * z ≤ 1 / 2) :
    Summable (fun j : ℕ => (j + 2 : ℝ) ^ r * z ^ (j + 2)) := by
  have hratio : |(2 : ℝ) ^ r * z| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun j => polynomial_geometric_term_le r j z hz)
    ((summable_geometric_of_abs_lt_one hratio).mul_left (2 ^ r * z ^ 2))

/-- For a natural exponent r and a real base z, when
[the base is nonnegative](hyp:hz) and
[2^r times the base is at most one half](hyp:hsmall),
[the series of (j+2)^r·z^(j+2) over all natural j is at most 2^(r+1)·z²](goal). -/
lemma polynomial_geometric_series_bound (r : ℕ) (z : ℝ) (hz : 0 ≤ z)
    (hsmall : 2 ^ r * z ≤ 1 / 2) :
    (∑' j : ℕ, (j + 2 : ℝ) ^ r * z ^ (j + 2)) ≤ 2 ^ (r + 1) * z ^ 2 := by
  have hratio : |(2 : ℝ) ^ r * z| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hden : 0 < 1 - (2 : ℝ) ^ r * z := by linarith
  calc
    _ ≤ ∑' j : ℕ, 2 ^ r * z ^ 2 * (2 ^ r * z) ^ j :=
      (polynomial_geometric_series_summable r z hz hsmall).tsum_le_tsum
        (fun j => polynomial_geometric_term_le r j z hz)
        ((summable_geometric_of_abs_lt_one hratio).mul_left _)
    _ = 2 ^ r * z ^ 2 / (1 - 2 ^ r * z) := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hratio, div_eq_mul_inv]
    _ ≤ 2 ^ (r + 1) * z ^ 2 := by
      apply (div_le_iff₀ hden).2
      rw [pow_succ (2 : ℝ) r]
      have hc : 0 ≤ (2 : ℝ) ^ r * z ^ 2 := by positivity
      have hm := mul_le_mul_of_nonneg_left hsmall hc
      nlinarith

end Causalean.Mathlib.Analysis.SpecificLimits.PolynomialGeometric
