/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Small real-power arithmetic helpers

This file provides reusable arithmetic identities and inequalities for real
powers, logarithms, and square roots, especially for sample-size factors,
negative exponents, and multiplicative windows. The main lemmas identify
reciprocals with real powers
(`inv_eq_rpow_neg_one`), factor `(A / n) ^ p` into an `A` part
and an `n` part (`div_rpow_of_nonneg_of_pos`), bound nonpositive powers of natural casts
(`rpow_natCast_nonpos_le_one`), and rewrite `q⁻¹ * sqrt q` as `q ^ (-1/2)`
(`inv_mul_sqrt_eq_rpow_neg_half`). It also controls logarithmic real-power
expressions when their positive inputs differ by a fixed multiplicative factor.
-/

public section

namespace Causalean.Mathlib.RpowArith

/-- For [any real number `x`](hyp:x), [its reciprocal equals its real power raised to the
exponent `−1`](goal). -/
lemma inv_eq_rpow_neg_one (x : ℝ) : x⁻¹ = x ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one]

/-- **Factoring a real power of a quotient.** For [a nonnegative numerator `A`](hyp:hA) and [a
strictly positive denominator `n`](hyp:hn), [the real power `(A/n)^p` equals `A^p` times `n`
raised to the power `−p`](goal), for any real exponent `p`. -/
lemma div_rpow_of_nonneg_of_pos
    (A p n : ℝ) (hA : 0 ≤ A) (hn : 0 < n) :
    (A / n) ^ p = A ^ p * n ^ (-p) := by
  have hnnonneg : 0 ≤ n := le_of_lt hn
  have hinv_nonneg : 0 ≤ n⁻¹ := inv_nonneg.mpr hnnonneg
  have hinv := inv_eq_rpow_neg_one n
  calc
    (A / n) ^ p = (A * n⁻¹) ^ p := by
      rw [div_eq_mul_inv]
    _ = A ^ p * (n⁻¹) ^ p := by
      rw [Real.mul_rpow hA hinv_nonneg]
    _ = A ^ p * (n ^ (-1 : ℝ)) ^ p := by
      rw [hinv]
    _ = A ^ p * n ^ ((-1 : ℝ) * p) := by
      rw [Real.rpow_mul hnnonneg]
    _ = A ^ p * n ^ (-p) := by
      congr 1
      ring_nf

/-- **Nonpositive real power of a natural number is at most one.** For [a nonpositive real exponent
`e`](hyp:he), [the real power of any natural-number cast raised to `e` is at most `1`](goal). -/
lemma rpow_natCast_nonpos_le_one
    (n : ℕ) (e : ℝ) (he : e ≤ 0) :
    (n : ℝ) ^ e ≤ 1 := by
  cases n with
  | zero =>
    by_cases he_zero : e = 0
    · simp [he_zero]
    · simp [Real.zero_rpow he_zero]
  | succ n =>
    have hn_ge_one : 1 ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    exact Real.rpow_le_one_of_one_le_of_nonpos hn_ge_one he

/-- **Reciprocal times square root as a negative-half power.** For [a nonnegative real number
`q`](hyp:hq), [the reciprocal of `q` times the square root of `q` equals `q` raised to the power
`−1/2`](goal). -/
lemma inv_mul_sqrt_eq_rpow_neg_half (q : ℝ) (hq : 0 ≤ q) :
    q⁻¹ * Real.sqrt q = q ^ (-(1 / 2 : ℝ)) := by
  rcases hq.eq_or_lt with rfl | hq
  · simp
  · calc
      q⁻¹ * Real.sqrt q = q ^ (-1 : ℝ) * q ^ (1 / (2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        rw [Real.rpow_neg hq.le, Real.rpow_one]
      _ = q ^ ((-1 : ℝ) + 1 / (2 : ℝ)) := by
        rw [← Real.rpow_add hq]
      _ = q ^ (-(1 / 2 : ℝ)) := by ring_nf

/-- For [a multiplicative factor `K`](hyp:K), [a nonnegative real exponent `d`](hyp:d,hd),
[a nonnegative weight `w`](hyp:w,hw), and [positive inputs `a` and `b`](hyp:a,b,ha,hb), if
[`K` is at least one](hyp:hK) and [`a` is at most `K * b`](hyp:hab), then [multiplying the
input of `w * x ^ d` by at most `K` increases its positive logarithmic transform by at most
`d * log K`](goal). -/
lemma window_log_power_le (K d w a b : ℝ) (hK : 1 ≤ K) (hd : 0 ≤ d)
    (hw : 0 ≤ w) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ K * b) :
    Real.log (Real.exp 1 + w * a ^ d) ≤
      d * Real.log K + Real.log (Real.exp 1 + w * b ^ d) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hp : 1 ≤ K ^ d := Real.one_le_rpow hK hd
  have hpow := Real.rpow_le_rpow ha.le hab hd
  rw [Real.mul_rpow hKpos.le hb.le] at hpow
  have hm := mul_le_mul_of_nonneg_left hpow hw
  have he := mul_le_mul_of_nonneg_right hp (Real.exp_pos 1).le
  have harg : Real.exp 1 + w * a ^ d ≤ K ^ d * (Real.exp 1 + w * b ^ d) := by
    nlinarith
  have hl := Real.log_le_log (by positivity : 0 < Real.exp 1 + w * a ^ d) harg
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hKpos] at hl
  exact hl

/-- For [a multiplicative factor `K`](hyp:K), [a nonnegative real exponent `d`](hyp:d,hd),
[a nonnegative weight `w`](hyp:w,hw), and [positive inputs `a` and `b`](hyp:a,b,ha,hb), if
[`K` is at least one](hyp:hK) and [`a` is at most `K * b`](hyp:hab), then [their positive
logarithmic real-power transforms differ by at most the factor `1 + d * log K`](goal). -/
lemma window_log_power_comparison (K d w a b : ℝ) (hK : 1 ≤ K) (hd : 0 ≤ d)
    (hw : 0 ≤ w) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ K * b) :
    Real.log (Real.exp 1 + w * a ^ d) ≤
      (1 + d * Real.log K) * Real.log (Real.exp 1 + w * b ^ d) := by
  have hl := window_log_power_le K d w a b hK hd hw ha hb hab
  have h1 : 1 ≤ Real.log (Real.exp 1 + w * b ^ d) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right (by positivity))
  have hc : 0 ≤ d * Real.log K := mul_nonneg hd (Real.log_nonneg hK)
  nlinarith [mul_le_mul_of_nonneg_left h1 hc]

/-- For [a multiplicative factor `K`](hyp:K), [a nonnegative real exponent `d`](hyp:d,hd),
[a nonnegative weight `w`](hyp:w,hw), and [positive inputs `a` and `b`](hyp:a,b,ha,hb), if
[`K` is at least one](hyp:hK) and [`a` is at most `K * b`](hyp:hab), then [the square roots
of their positive logarithmic real-power transforms differ by at most the factor
`1 + d * log K`](goal). -/
lemma window_sqrt_log_comparison (K d w a b : ℝ) (hK : 1 ≤ K) (hd : 0 ≤ d)
    (hw : 0 ≤ w) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ K * b) :
    Real.sqrt (Real.log (Real.exp 1 + w * a ^ d)) ≤
      (1 + d * Real.log K) * Real.sqrt (Real.log (Real.exp 1 + w * b ^ d)) := by
  have hl := window_log_power_comparison K d w a b hK hd hw ha hb hab
  have hc : 1 ≤ 1 + d * Real.log K := by
    have := mul_nonneg hd (Real.log_nonneg hK)
    linarith
  have hla : 0 ≤ Real.log (Real.exp 1 + w * a ^ d) := by
    apply Real.log_nonneg
    have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    have : 0 ≤ w * a ^ d := by positivity
    linarith
  have hlb : 0 ≤ Real.log (Real.exp 1 + w * b ^ d) := by
    apply Real.log_nonneg
    have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    have : 0 ≤ w * b ^ d := by positivity
    linarith
  have hsa := Real.sqrt_nonneg (Real.log (Real.exp 1 + w * a ^ d))
  have hsb := Real.sqrt_nonneg (Real.log (Real.exp 1 + w * b ^ d))
  have hqa := Real.sq_sqrt hla
  have hqb := Real.sq_sqrt hlb
  have hmul := mul_le_mul_of_nonneg_right (show
    1 + d * Real.log K ≤ (1 + d * Real.log K) ^ 2 by nlinarith) hlb
  apply (sq_le_sq₀ hsa (mul_nonneg (by linarith) hsb)).mp
  calc
    _ = Real.log (Real.exp 1 + w * a ^ d) := hqa
    _ ≤ (1 + d * Real.log K) ^ 2 * Real.log (Real.exp 1 + w * b ^ d) := hl.trans hmul
    _ = _ := by rw [mul_pow, hqb]

end Causalean.Mathlib.RpowArith
