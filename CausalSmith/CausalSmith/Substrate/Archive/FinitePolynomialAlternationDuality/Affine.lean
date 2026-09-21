/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Affine transport of real polynomials between compact intervals

This module defines the pullback of a polynomial from `[r,s]` to `[-1,1]`
and records its evaluation, degree, derivative, and supremum-norm behavior.
-/

@[expose] public section

open Polynomial Set

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-- Pull a polynomial on `[r,s]` back along the affine map sending `[-1,1]`
onto `[r,s]`. -/
noncomputable def pullbackToUnitInterval
    (Q : Polynomial ℝ) (r s : ℝ) : Polynomial ℝ :=
  Q.comp (Polynomial.C ((s - r) / 2) * Polynomial.X +
    Polynomial.C ((r + s) / 2))

/-- Evaluating the affine pullback at `t` equals evaluating the original
polynomial at the corresponding point of `[r,s]`. -/
theorem eval_pullbackToUnitInterval
    (Q : Polynomial ℝ) (r s t : ℝ) :
    (pullbackToUnitInterval Q r s).eval t =
      Q.eval (((s - r) / 2) * t + (r + s) / 2) := by
  simp [pullbackToUnitInterval]

/-- Affine pullback does not increase the natural degree of a real polynomial. -/
theorem natDegree_pullbackToUnitInterval_le
    (Q : Polynomial ℝ) (r s : ℝ) :
    (pullbackToUnitInterval Q r s).natDegree ≤ Q.natDegree := by
  unfold pullbackToUnitInterval
  calc
    (Q.comp (C ((s - r) / 2) * X + C ((r + s) / 2))).natDegree
        ≤ Q.natDegree * (C ((s - r) / 2) * X + C ((r + s) / 2)).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ Q.natDegree * 1 :=
      Nat.mul_le_mul_left _ Polynomial.natDegree_linear_le
    _ = Q.natDegree := by simp

/-- The derivative of the affine pullback is the original derivative evaluated
at the corresponding point, multiplied by the interval half-length. -/
theorem derivative_eval_pullbackToUnitInterval
    (Q : Polynomial ℝ) (r s t : ℝ) :
    (pullbackToUnitInterval Q r s).derivative.eval t =
      ((s - r) / 2) * Q.derivative.eval
        (((s - r) / 2) * t + (r + s) / 2) := by
  simp [pullbackToUnitInterval, Polynomial.derivative_comp]

/-- On a nondegenerate interval, affine pullback preserves the compact
supremum norm exactly. -/
theorem intervalSupNorm_pullbackToUnitInterval
    (Q : Polynomial ℝ) {r s : ℝ} (hrs : r < s) :
    intervalSupNorm (fun t => (pullbackToUnitInterval Q r s).eval t) (-1) 1 =
      intervalSupNorm (fun x => Q.eval x) r s := by
  apply le_antisymm
  · rw [intervalSupNorm_le_iff
      (pullbackToUnitInterval Q r s).continuous.continuousOn
      (by norm_num : (-1 : ℝ) ≤ 1)]
    intro t ht
    rw [eval_pullbackToUnitInterval]
    apply (intervalSupNorm_le_iff Q.continuous.continuousOn hrs.le).mp le_rfl
    have hhalf : 0 ≤ (s - r) / 2 := by linarith
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left ht.1 hhalf]
    · nlinarith [mul_le_mul_of_nonneg_left ht.2 hhalf]
  · rw [intervalSupNorm_le_iff Q.continuous.continuousOn hrs.le]
    intro x hx
    let t : ℝ := (2 * x - (r + s)) / (s - r)
    have hden : 0 < s - r := sub_pos.mpr hrs
    have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · apply (le_div_iff₀ hden).2
        linarith [hx.1]
      · apply (div_le_iff₀ hden).2
        linarith [hx.2]
    have hmap : ((s - r) / 2) * t + (r + s) / 2 = x := by
      dsimp [t]
      field_simp [ne_of_gt hden]
      ring
    have hbound :=
      (intervalSupNorm_le_iff
        (pullbackToUnitInterval Q r s).continuous.continuousOn
        (by norm_num : (-1 : ℝ) ≤ 1)).mp le_rfl t ht
    rw [eval_pullbackToUnitInterval, hmap] at hbound
    exact hbound

end CausalSmith.Substrate.FinitePolynomialAlternationDuality
