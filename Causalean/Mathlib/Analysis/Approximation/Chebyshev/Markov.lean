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


/-- The [pullback to the unit interval](goal) of [a real polynomial](hyp:Q) for [interval endpoints
r and s](hyp:r,s) is [the polynomial composed with the affine map t ↦ ((s − r) / 2) t + (r + s) /
2, which carries the interval from −1 to 1 onto the interval from r to s](step:1). -/
noncomputable def pullbackToUnitInterval
    (Q : Polynomial ℝ) (r s : ℝ) : Polynomial ℝ :=
  Q.comp (Polynomial.C ((s - r) / 2) * Polynomial.X +
    Polynomial.C ((r + s) / 2))

/-- For [a real polynomial](hyp:Q) and [real numbers r, s, and t](hyp:r,s,t), [the pullback to the
unit interval evaluated at t equals the original polynomial evaluated at ((s − r) / 2) t + (r + s)
/ 2](goal). -/
theorem eval_pullbackToUnitInterval
    (Q : Polynomial ℝ) (r s t : ℝ) :
    (pullbackToUnitInterval Q r s).eval t =
      Q.eval (((s - r) / 2) * t + (r + s) / 2) := by
  simp [pullbackToUnitInterval]

/-- For [a real polynomial](hyp:Q) and [any interval endpoints r and s](hyp:r,s), [the degree of
the pullback to the unit interval is at most the degree of the original polynomial](goal). -/
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

/-- For [a real polynomial](hyp:Q) and [real numbers r, s, and t](hyp:r,s,t), [the derivative of
the pullback to the unit interval at t equals the half-length (s − r) / 2 times the derivative of
the original polynomial at ((s − r) / 2) t + (r + s) / 2](goal). -/
theorem derivative_eval_pullbackToUnitInterval
    (Q : Polynomial ℝ) (r s t : ℝ) :
    (pullbackToUnitInterval Q r s).derivative.eval t =
      ((s - r) / 2) * Q.derivative.eval
        (((s - r) / 2) * t + (r + s) / 2) := by
  simp [pullbackToUnitInterval, Polynomial.derivative_comp]

/-- For [a real polynomial](hyp:Q) and [endpoints with r strictly less than s](hyp:hrs), [the
supremum norm of the pullback on the interval from −1 to 1 equals the supremum norm of the original
polynomial on the interval from r to s](goal). -/
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


/-- For [a real polynomial](hyp:Q) of [degree at most L](hyp:L,hQ), [the supremum norm of its
derivative on the interval from −1 to 1 is at most L² times the supremum norm of the polynomial on
that interval](goal). -/
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


/-- For [a real polynomial](hyp:Q) of [degree at most L](hyp:L,hQ) and [endpoints with r strictly
less than s](hyp:hrs), [the supremum norm of its derivative on the interval from r to s is at most
2 L² / (s − r) times the supremum norm of the polynomial on that interval](goal). -/
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
