/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.Complex.Trigonometric

/-! # Exponential remainder bounds for martingale CLTs

This module collects the elementary complex-exponential estimates used in the
characteristic-function proof of the martingale triangular-array CLT.  The
estimates are deterministic and independent of the probability-space layer.
-/

namespace Causalean.Stat

open Complex

/-- The quadratic Taylor remainder of the characteristic-function kernel at a
real argument `u` is `exp(iu) - 1 - iu + u²/2`. -/
noncomputable def expQuadraticRemainder (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ) + (u : ℂ) ^ 2 / 2

/-- If [the real argument has absolute value at most one](hyp:hu), then [the norm
of the quadratic Taylor remainder of `exp(iu)` is at most `|u|³`](goal). -/
theorem norm_expQuadraticRemainder_le_cube (u : ℝ) (hu : |u| ≤ 1) :
    ‖expQuadraticRemainder u‖ ≤ |u| ^ 3 := by
  /-
  Normalize `expQuadraticRemainder` to the first three terms of the complex
  exponential series and apply `Complex.exp_bound` with `n = 3`.  The resulting
  numerical coefficient is at most one, and `‖I * (u : ℂ)‖ = |u|`.
  -/
  let z : ℂ := Complex.I * (u : ℂ)
  have hz : ‖z‖ ≤ 1 := by simp [z, hu]
  have hzsq : z ^ 2 = -((u : ℂ) ^ 2) := by
    dsimp [z]
    rw [mul_pow, pow_two Complex.I, Complex.I_mul_I]
    ring
  have hrem :
      expQuadraticRemainder u = Complex.exp z - 1 - z - z ^ 2 / 2 := by
    rw [expQuadraticRemainder]
    dsimp [z]
    rw [hzsq]
    ring
  have hsum :
      (∑ m ∈ Finset.range 3, z ^ m / m.factorial) =
        1 + z + z ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have h := Complex.exp_bound (x := z) (n := 3) hz (by norm_num)
  rw [hsum] at h
  rw [hrem]
  norm_num [Nat.factorial] at h
  calc
    ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ =
        ‖Complex.exp z - (1 + z + z ^ 2 / 2)‖ := by
          congr 1
          ring
    _ ≤ ‖z‖ ^ 3 * (2 / 9 : ℝ) := h
    _ ≤ ‖z‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg z) 3]
    _ = |u| ^ 3 := by simp [z]

/-- For [every real argument](hyp:u), [the norm of the quadratic Taylor remainder
of `exp(iu)` is bounded by `2 + |u| + u²/2`](goal). -/
theorem norm_expQuadraticRemainder_le_global (u : ℝ) :
    ‖expQuadraticRemainder u‖ ≤ 2 + |u| + u ^ 2 / 2 := by
  /-
  Expand the definition, use the triangle inequality, and rewrite
  `‖exp (I * u)‖ = 1`, `‖I * u‖ = |u|`, and the norm of the real quadratic term.
  -/
  rw [expQuadraticRemainder]
  calc
    ‖Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ) +
        (u : ℂ) ^ 2 / 2‖
        ≤ ‖Complex.exp (Complex.I * (u : ℂ)) - 1 -
            Complex.I * (u : ℂ)‖ + ‖(u : ℂ) ^ 2 / 2‖ :=
      norm_add_le _ _
    _ ≤ (‖Complex.exp (Complex.I * (u : ℂ)) - 1‖ +
          ‖Complex.I * (u : ℂ)‖) + ‖(u : ℂ) ^ 2 / 2‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ((‖Complex.exp (Complex.I * (u : ℂ))‖ + ‖(1 : ℂ)‖) +
          ‖Complex.I * (u : ℂ)‖) + ‖(u : ℂ) ^ 2 / 2‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = 2 + |u| + u ^ 2 / 2 := by
      have hone : ‖(1 : ℂ)‖ = 1 := by
        change ‖((1 : ℝ) : ℂ)‖ = 1
        rw [Complex.norm_real, Real.norm_eq_abs]
        norm_num
      rw [Complex.norm_exp, hone]
      norm_num [Complex.norm_pow, Complex.norm_real,
        abs_of_nonneg (sq_nonneg u)]

/-- Given [a frequency](hyp:t), [an increment](hyp:x), and [a positive truncation
level](hyp:hη) small enough that `|t| · η ≤ 1` [as assumed](hyp:htη), [the
quadratic exponential remainder is bounded by a small cubic contribution plus
a quadratic contribution supported on increments larger than `η`](goal). -/
theorem norm_expQuadraticRemainder_le_truncated (t x η : ℝ)
    (hη : 0 < η) (htη : |t| * η ≤ 1) :
    ‖expQuadraticRemainder (t * x)‖ ≤
      |t| ^ 3 * η * x ^ 2 +
        (2 / η ^ 2 + |t| / η + t ^ 2 / 2) *
          (if η < |x| then x ^ 2 else 0) := by
  /-
  Split on `η < |x|`.  On the small-increment branch, use
  `norm_expQuadraticRemainder_le_cube`, `|t*x| ≤ 1`, and
  `|x|³ ≤ η*x²`.  On the large branch, use the global estimate and absorb
  `2` and `|t*x|` into multiples of `x²` using `0 < η < |x|`.
  -/
  by_cases hx : η < |x|
  · rw [if_pos hx]
    have hηsq : 0 < η ^ 2 := sq_pos_of_pos hη
    have hsq : η ^ 2 ≤ x ^ 2 := by
      nlinarith [sq_abs x]
    have htwo : 2 ≤ 2 / η ^ 2 * x ^ 2 := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hηsq).2 (by nlinarith)
    have hηabs : η * |x| ≤ x ^ 2 := by
      have habs : 0 ≤ |x| := abs_nonneg x
      have hle : η ≤ |x| := hx.le
      nlinarith [sq_abs x]
    have hlin : |t * x| ≤ |t| / η * x ^ 2 := by
      rw [abs_mul, div_mul_eq_mul_div]
      apply (le_div_iff₀ hη).2
      nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hηabs)]
    have hquad : (t * x) ^ 2 / 2 = (t ^ 2 / 2) * x ^ 2 := by ring
    have hglobal := norm_expQuadraticRemainder_le_global (t * x)
    have hcubic : 0 ≤ |t| ^ 3 * η * x ^ 2 := by positivity
    calc
      ‖expQuadraticRemainder (t * x)‖
          ≤ 2 + |t * x| + (t * x) ^ 2 / 2 := hglobal
      _ ≤ (2 / η ^ 2 + |t| / η + t ^ 2 / 2) * x ^ 2 := by
        rw [hquad]
        nlinarith
      _ ≤ |t| ^ 3 * η * x ^ 2 +
          (2 / η ^ 2 + |t| / η + t ^ 2 / 2) * x ^ 2 := by
        linarith
  · rw [if_neg hx, mul_zero, add_zero]
    have hxle : |x| ≤ η := le_of_not_gt hx
    have htx : |t * x| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hxle (abs_nonneg t)).trans htη
    have hlocal := norm_expQuadraticRemainder_le_cube (t * x) htx
    have hxcube : |x| ^ 3 ≤ η * x ^ 2 := by
      calc
        |x| ^ 3 = |x| * x ^ 2 := by
          rw [pow_succ, sq_abs]
          ring
        _ ≤ η * x ^ 2 :=
          mul_le_mul_of_nonneg_right hxle (sq_nonneg x)
    calc
      ‖expQuadraticRemainder (t * x)‖ ≤ |t * x| ^ 3 := hlocal
      _ = |t| ^ 3 * |x| ^ 3 := by rw [abs_mul, mul_pow]
      _ ≤ |t| ^ 3 * (η * x ^ 2) :=
        mul_le_mul_of_nonneg_left hxcube (by positivity)
      _ = |t| ^ 3 * η * x ^ 2 := by ring

end Causalean.Stat
