/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.Basic
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.DuffinSchaeffer
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Markov's derivative inequality on the unit interval

This module contains the sharp first-derivative Markov inequality for a real
polynomial on `[-1,1]`.  Affine transport to a general interval is separated
into the downstream `Markov` module.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

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

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
