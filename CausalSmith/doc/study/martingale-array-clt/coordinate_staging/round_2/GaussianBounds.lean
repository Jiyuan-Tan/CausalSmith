/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Deterministic Gaussian interpolation bounds

This module collects the scalar exponential estimates used by the compensated
Gaussian-time interpolation in the martingale-array CLT.  They are deterministic
and make no probabilistic or independence assumptions.
-/

namespace Causalean.Stat

open Complex

/-- For [a nonnegative real argument](hyp:hx), [the error in the exponential
Euler factor `exp(x) * (1 - x)` is at most `exp(x) * x² / 2`](goal). -/
theorem abs_exp_mul_one_sub_sub_one_le (x : ℝ) (hx : 0 ≤ x) :
    |Real.exp x * (1 - x) - 1| ≤ Real.exp x * x ^ 2 / 2 := by
  let f : ℝ → ℝ := fun y => 1 - y + y ^ 2 / 2 - Real.exp (-y)
  have hfderiv (y : ℝ) :
      HasDerivAt f (-1 + y + Real.exp (-y)) y := by
    have hraw :=
      ((((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
        (((hasDerivAt_id y).mul (hasDerivAt_id y)).div_const 2)).sub
          ((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y)))
    have hg : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y))
        (0 - 1 + (1 * y + y * 1) / 2 - Real.exp (-y) * (-1)) y := by
      apply hraw.congr_of_eventuallyEq
      filter_upwards with z
      simp [pow_two]
    simpa only [f] using (hg.congr_deriv (by ring))
  have hfmono : Monotone f := monotone_of_deriv_nonneg
      (fun y => (hfderiv y).differentiableAt)
      (fun y => by
        rw [(hfderiv y).deriv]
        linarith [Real.one_sub_le_exp_neg y])
  have htaylor : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
    have h := hfmono hx
    simpa [f] using h
  have hsign : Real.exp x * (1 - x) - 1 ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg x) (Real.exp_nonneg x)
    rw [← Real.exp_add] at h
    norm_num at h
    linarith
  rw [abs_of_nonpos hsign]
  have h := mul_le_mul_of_nonneg_left htaylor (Real.exp_nonneg x)
  rw [← Real.exp_add] at h
  norm_num at h
  nlinarith

/-- For [any real argument](hyp:x), [the increment of the real exponential is
bounded by `exp(|x|) * |x|`](goal). -/
theorem abs_exp_sub_one_le_exp_abs_mul_abs (x : ℝ) :
    |Real.exp x - 1| ≤ Real.exp |x| * |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one] at h
  rw [← Complex.ofReal_exp] at h
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub] at h
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  simpa only [mul_comm] using h

/-- For [nonnegative coefficients](hyp:hc,hv) and [a complex Taylor error](hyp:r),
[one compensated Gaussian step differs from one by at most the exponential
weight times the Taylor error plus a quadratic Euler error](goal). -/
theorem norm_exp_mul_quadraticFactor_sub_one_le
    (c v : ℝ) (r : ℂ) (hc : 0 ≤ c) (hv : 0 ≤ v) :
    ‖((Real.exp (c * v) : ℝ) : ℂ) *
          (1 - (((c * v : ℝ) : ℂ)) + r) - 1‖ ≤
      Real.exp (c * v) * (‖r‖ + (c * v) ^ 2 / 2) := by
  have hcv : 0 ≤ c * v := mul_nonneg hc hv
  calc
    ‖((Real.exp (c * v) : ℝ) : ℂ) *
          (1 - (((c * v : ℝ) : ℂ)) + r) - 1‖ =
        ‖(((Real.exp (c * v) * (1 - c * v) - 1 : ℝ) : ℂ) +
          ((Real.exp (c * v) : ℝ) : ℂ) * r)‖ := by
            congr 1
            push_cast
            ring
    _ ≤ ‖((Real.exp (c * v) * (1 - c * v) - 1 : ℝ) : ℂ)‖ +
          ‖((Real.exp (c * v) : ℝ) : ℂ) * r‖ := norm_add_le _ _
    _ = |Real.exp (c * v) * (1 - c * v) - 1| +
          Real.exp (c * v) * ‖r‖ := by
            rw [Complex.norm_real, Complex.norm_mul, Complex.norm_real]
            simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (c * v) * (c * v) ^ 2 / 2 +
          Real.exp (c * v) * ‖r‖ := by
            gcongr
            exact abs_exp_mul_one_sub_sub_one_le (c * v) hcv
    _ = Real.exp (c * v) * (‖r‖ + (c * v) ^ 2 / 2) := by ring

/-- If [the exponential coefficient is nonnegative](hyp:hc) and [a variance value lies between
zero and a nonnegative budget](hyp:hV0,hVK),
then [its terminal Gaussian correction is Lipschitz in its distance from one,
with a constant depending only on the budget](goal). -/
theorem abs_exp_varianceCorrection_sub_one_le
    (c V K : ℝ) (hc : 0 ≤ c) (hV0 : 0 ≤ V) (hVK : V ≤ K) :
    |Real.exp (c * (V - 1)) - 1| ≤
      Real.exp (c * max K 1) * c * |V - 1| := by
  have hVabs : |V - 1| ≤ max K 1 := by
    rw [abs_le]
    constructor <;> linarith [le_max_left K 1, le_max_right K 1]
  have harg : |c * (V - 1)| ≤ c * max K 1 := by
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hVabs hc
  calc
    |Real.exp (c * (V - 1)) - 1|
        ≤ Real.exp |c * (V - 1)| * |c * (V - 1)| :=
          abs_exp_sub_one_le_exp_abs_mul_abs _
    _ = Real.exp |c * (V - 1)| * c * |V - 1| := by
          rw [abs_mul, abs_of_nonneg hc]
          ring
    _ ≤ Real.exp (c * max K 1) * c * |V - 1| := by
          gcongr

end Causalean.Stat
