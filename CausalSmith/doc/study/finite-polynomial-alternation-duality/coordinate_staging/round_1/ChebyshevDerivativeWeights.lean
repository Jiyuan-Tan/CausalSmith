/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.ChebyshevRootDerivativePropagation
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.ChebyshevZeroDerivativeComparison

/-!
# Derivative weights at Chebyshev extrema

This module isolates the analytic core of the Duffin--Schaeffer refinement.
It expresses differentiation through the Lagrange basis at the Chebyshev
extrema and states the sharp `L²` bound for the resulting differentiation
weights.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- The Chebyshev differentiation weight at `x` and node index `i` is the
derivative at `x` of the corresponding Lagrange cardinal polynomial. [the stated inputs](hyp:L,x,i) establish [the defined object](goal). -/
noncomputable def chebyshevDerivativeWeight (L : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  (Lagrange.basis (Finset.range (L + 1)) (Polynomial.Chebyshev.node L) i).derivative.eval x

/-- The derivative of every degree-at-most-`L` polynomial is the weighted sum
of its values at the `L+1` Chebyshev extrema, with the Chebyshev
differentiation weights. [the stated inputs](hyp:Q,L,hQ,x) establish [the stated conclusion](goal). -/
theorem eval_derivative_eq_sum_chebyshevDerivativeWeight
    (Q : Polynomial ℝ) {L : ℕ} (hQ : Q.natDegree ≤ L) (x : ℝ) :
    Q.derivative.eval x =
      ∑ i ∈ Finset.range (L + 1),
        Q.eval (Polynomial.Chebyshev.node L i) * chebyshevDerivativeWeight L x i := by
  classical
  have hdegree : Q.degree < (Finset.range (L + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Q.degree_le_natDegree
      (by exact_mod_cast (Nat.lt_succ_of_le hQ))
  have hinterp := Lagrange.eq_interpolate
    (Polynomial.Chebyshev.strictAntiOn_node L).injOn hdegree
  calc
    Q.derivative.eval x =
        (Lagrange.interpolate (Finset.range (L + 1))
          (Polynomial.Chebyshev.node L)
          (fun i ↦ Q.eval (Polynomial.Chebyshev.node L i))).derivative.eval x := by
      rw [← hinterp]
    _ = ∑ i ∈ Finset.range (L + 1),
        Q.eval (Polynomial.Chebyshev.node L i) *
          chebyshevDerivativeWeight L x i := by
      simp [Lagrange.interpolate_apply, eval_finsetSum, chebyshevDerivativeWeight]

/-- On `[-1,1]`, the total absolute mass of the degree-`L` Chebyshev
differentiation weights is at most `L²` when `L` is positive. [the stated inputs](hyp:L,hL,x,hx) establish [the stated conclusion](goal). -/
theorem sum_abs_chebyshevDerivativeWeight_le_sq
    {L : ℕ} (hL : 0 < L) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    ∑ i ∈ Finset.range (L + 1), |chebyshevDerivativeWeight L x i| ≤
      (L : ℝ) ^ 2 := by
  classical
  let s : Finset ℕ := Finset.range (L + 1)
  let v : ℕ → ℝ := Polynomial.Chebyshev.node L
  let c : ℕ → ℝ := fun i ↦ chebyshevDerivativeWeight L x i
  let ε : ℕ → ℝ := fun i ↦ if c i < 0 then -1 else 1
  let P : Polynomial ℝ := Lagrange.interpolate s v ε
  have hinj : Set.InjOn v s := Polynomial.Chebyshev.strictAntiOn_node L |>.injOn
  have hPdeg : P.natDegree ≤ L := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    have hdegree := Lagrange.degree_interpolate_le ε hinj
    simpa [P, s] using hdegree
  have hPnodes : ∀ i, i ≤ L → |P.eval (Polynomial.Chebyshev.node L i)| ≤ 1 := by
    intro i hi
    have his : i ∈ s := by simp [s, hi]
    rw [show Polynomial.Chebyshev.node L i = v i from rfl]
    rw [show P.eval (v i) = ε i by
      exact Lagrange.eval_interpolate_at_node ε hinj his]
    simp only [ε]
    split <;> norm_num
  have hroot : ∀ z : ℝ,
      (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval z = 0 →
        |P.derivative.eval z| ≤
          |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval z| := by
    intro z hz
    exact abs_eval_derivative_le_chebyshev_at_root hL P hPdeg hPnodes hz
  have hPder : P.derivative.eval x = ∑ i ∈ s, ε i * c i := by
    rw [eval_derivative_eq_sum_chebyshevDerivativeWeight P hPdeg x]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show P.eval (Polynomial.Chebyshev.node L i) = ε i by
      exact Lagrange.eval_interpolate_at_node ε hinj hi]
  have hmass : ∑ i ∈ s, |c i| = P.derivative.eval x := by
    rw [hPder]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hci : c i < 0
    · simp [ε, hci, abs_of_neg hci]
    · have hci' : 0 ≤ c i := le_of_not_gt hci
      simp [ε, hci, abs_of_nonneg hci']
  calc
    ∑ i ∈ Finset.range (L + 1), |chebyshevDerivativeWeight L x i| =
        P.derivative.eval x := by simpa [s, c] using hmass
    _ ≤ |P.derivative.eval x| := le_abs_self _
    _ ≤ (L : ℝ) ^ 2 :=
      abs_eval_derivative_le_sq_of_chebyshev_root_control hL P hPdeg hroot hx

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
