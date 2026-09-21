/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Basic
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.DuffinSchaeffer
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Markov's polynomial derivative inequality

This module proves the sharp Markov derivative inequality on `[-1,1]` from the
Duffin--Schaeffer bound and transports it affinely to arbitrary nondegenerate
compact intervals.
-/

@[expose] public section

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-! ## Affine transport -/


/-- Pull a polynomial on `[r,s]` back along the affine map sending `[-1,1]`
onto `[r,s]`. [the stated inputs](hyp:Q,r,s) establish [the defined object](goal). -/
noncomputable def pullbackToUnitInterval
    (Q : Polynomial ℝ) (r s : ℝ) : Polynomial ℝ :=
  Q.comp (Polynomial.C ((s - r) / 2) * Polynomial.X +
    Polynomial.C ((r + s) / 2))

/-- Evaluating the affine pullback at `t` equals evaluating the original
polynomial at the corresponding point of `[r,s]`. [the stated inputs](hyp:Q,r,s,t) establish [the stated conclusion](goal). -/
theorem eval_pullbackToUnitInterval
    (Q : Polynomial ℝ) (r s t : ℝ) :
    (pullbackToUnitInterval Q r s).eval t =
      Q.eval (((s - r) / 2) * t + (r + s) / 2) := by
  simp [pullbackToUnitInterval]

/-- Affine pullback does not increase the natural degree of a real polynomial. [the stated inputs](hyp:Q,r,s) establish [the stated conclusion](goal). -/
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
at the corresponding point, multiplied by the interval half-length. [the stated inputs](hyp:Q,r,s,t) establish [the stated conclusion](goal). -/
theorem derivative_eval_pullbackToUnitInterval
    (Q : Polynomial ℝ) (r s t : ℝ) :
    (pullbackToUnitInterval Q r s).derivative.eval t =
      ((s - r) / 2) * Q.derivative.eval
        (((s - r) / 2) * t + (r + s) / 2) := by
  simp [pullbackToUnitInterval, Polynomial.derivative_comp]

/-- On a nondegenerate interval, affine pullback preserves the compact
supremum norm exactly. [the stated inputs](hyp:Q,r,s,hrs) establish [the stated conclusion](goal). -/
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

/-! ## The unit-interval inequality -/


/-- A real polynomial of degree at most `L` has derivative supremum norm on
`[-1,1]` at most `L²` times its own supremum norm there. [the stated inputs](hyp:Q,L,hQ) establish [the stated conclusion](goal). -/
theorem markov_derivative_unitInterval
    (Q : Polynomial ℝ) (L : ℕ) (hQ : Q.natDegree ≤ L) :
    intervalSupNorm (fun x => Q.derivative.eval x) (-1) 1 ≤
      (L : ℝ) ^ 2 * intervalSupNorm (fun x => Q.eval x) (-1) 1 := by
  rw [intervalSupNorm_le_iff Q.derivative.continuous.continuousOn (by norm_num)]
  intro x hx
  by_cases hLzero : L = 0
  · subst L
    have hnat : Q.natDegree = 0 := Nat.eq_zero_of_le_zero hQ
    have hderiv : Q.derivative = 0 := Polynomial.derivative_eq_zero.mpr hnat
    simp [hderiv]
  · have hL : 0 < L := Nat.pos_of_ne_zero hLzero
    have hbound : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
        |Q.eval y| ≤ intervalSupNorm (fun z => Q.eval z) (-1) 1 :=
      (intervalSupNorm_le_iff Q.continuous.continuousOn (by norm_num)).mp le_rfl
    have hC : 0 ≤ intervalSupNorm (fun z => Q.eval z) (-1) 1 :=
      (abs_nonneg (Q.eval (Polynomial.Chebyshev.node L 0))).trans
        (hbound _ Polynomial.Chebyshev.node_mem_Icc)
    exact duffinSchaeffer_derivative_le Q hL hQ hC
      (fun i _ ↦ hbound _ Polynomial.Chebyshev.node_mem_Icc) hx

/-! ## Transport to a compact interval -/


/-- If `r < s` and a real polynomial has degree at most `L`, then its derivative
supremum norm on `[r,s]` is at most `2 L²/(s-r)` times the polynomial's
supremum norm on that interval. [the stated inputs](hyp:Q,r,s,hrs,L,hQ) establish [the stated conclusion](goal). -/
theorem markov_derivative_Icc
    (Q : Polynomial ℝ) {r s : ℝ} (hrs : r < s)
    (L : ℕ) (hQ : Q.natDegree ≤ L) :
    intervalSupNorm (fun x => Q.derivative.eval x) r s ≤
      (2 * (L : ℝ) ^ 2 / (s - r)) *
        intervalSupNorm (fun x => Q.eval x) r s := by
  let P := pullbackToUnitInterval Q r s
  have hP : P.natDegree ≤ L :=
    (natDegree_pullbackToUnitInterval_le Q r s).trans hQ
  have hunit := markov_derivative_unitInterval P L hP
  have hden : 0 < s - r := sub_pos.mpr hrs
  have hhalf : 0 < (s - r) / 2 := by positivity
  rw [intervalSupNorm_le_iff Q.derivative.continuous.continuousOn hrs.le]
  intro x hx
  let t : ℝ := (2 * x - (r + s)) / (s - r)
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
  have hpoint :=
    ((intervalSupNorm_le_iff P.derivative.continuous.continuousOn
      (by norm_num : (-1 : ℝ) ≤ 1)).mp hunit) t ht
  have hpull :
      |((s - r) / 2) * Q.derivative.eval x| ≤
        (L : ℝ) ^ 2 * intervalSupNorm (fun x => Q.eval x) r s := by
    simpa [P, derivative_eval_pullbackToUnitInterval, hmap,
      intervalSupNorm_pullbackToUnitInterval Q hrs] using hpoint
  have hscaled :
      ((s - r) / 2) * |Q.derivative.eval x| ≤
        (L : ℝ) ^ 2 * intervalSupNorm (fun x => Q.eval x) r s := by
    simpa [abs_mul, abs_of_pos hhalf] using hpull
  calc
    |Q.derivative.eval x| ≤
        ((L : ℝ) ^ 2 * intervalSupNorm (fun x => Q.eval x) r s) /
          ((s - r) / 2) := (le_div_iff₀ hhalf).2 (by
            simpa [mul_comm] using hscaled)
    _ = (2 * (L : ℝ) ^ 2 / (s - r)) *
          intervalSupNorm (fun x => Q.eval x) r s := by
      field_simp [ne_of_gt hden]

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
