/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Derivative comparison at Chebyshev zeros

This module isolates the first classical comparison lemma in the
Duffin--Schaeffer proof.  Nodal control at the extrema of a Chebyshev
polynomial bounds the derivative at each zero of that Chebyshev polynomial.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

private lemma chebyshev_nodal_eq
    {L : ℕ} (hL : 0 < L) :
    C ((L : ℝ) * 2 ^ (L - 1)) *
        Lagrange.nodal (Finset.range (L + 1)) (Polynomial.Chebyshev.node L) =
      (X ^ 2 - 1) * (Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative := by
  classical
  let A : ℝ := (L : ℝ) * 2 ^ (L - 1)
  let N : ℝ[X] := Lagrange.nodal (Finset.range (L + 1))
    (Polynomial.Chebyshev.node L)
  let T : ℝ[X] := Polynomial.Chebyshev.T ℝ (L : ℤ)
  have hA : A ≠ 0 := by
    dsimp [A]
    positivity
  have hNdeg : N.degree = (L + 1 : ℕ) := by simp [N]
  have hTnat : T.natDegree = L := by simp [T]
  have hdTdeg : T.derivative.degree = (L - 1 : ℕ) := by
    rw [Polynomial.degree_derivative]
    · simp [hTnat]
    · simpa [hTnat] using (Nat.ne_of_gt hL)
  have hXdeg : (X ^ 2 - 1 : ℝ[X]).degree = 2 := by
    simpa using Polynomial.degree_X_pow_sub_C (R := ℝ) (by omega : 0 < 2) 1
  have hXmonic : (X ^ 2 - 1 : ℝ[X]).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (R := ℝ) 1 (by omega : 2 ≠ 0)
  apply Polynomial.eq_of_degree_le_of_eval_index_eq
    (s := Finset.range (L + 1)) (v := Polynomial.Chebyshev.node L)
    (Polynomial.Chebyshev.strictAntiOn_node L).injOn
  · rw [Polynomial.degree_C_mul hA, hNdeg]
    simp
  · rw [Polynomial.degree_C_mul hA, hNdeg, Polynomial.degree_mul, hXdeg, hdTdeg]
    norm_cast
    omega
  · rw [leadingCoeff_mul, Lagrange.nodal_monic.leadingCoeff, leadingCoeff_C, mul_one,
      leadingCoeff_mul, hXmonic.leadingCoeff, one_mul,
      Polynomial.leadingCoeff_derivative]
    simp
    ring
  · intro i hi
    have hiL : i ≤ L := Finset.mem_range_succ_iff.mp hi
    simp only [eval_mul, eval_C]
    rw [Lagrange.eval_nodal_at_node hi, mul_zero]
    symm
    by_cases hi0 : i = 0
    · subst i
      simp [Polynomial.Chebyshev.node_eq_one]
    by_cases hiEq : i = L
    · subst i
      rw [Polynomial.Chebyshev.node_eq_neg_one (Nat.ne_of_gt hL)]
      norm_num
    have hz := (Polynomial.Chebyshev.isLocalExtr_T_real
      (Nat.ne_of_gt hL) (Nat.pos_of_ne_zero hi0) (lt_of_le_of_ne hiL hiEq)).deriv_eq_zero
    rw [Polynomial.deriv] at hz
    have hz' : (Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval
        (Polynomial.Chebyshev.node L i) = 0 := by
      simpa [Polynomial.Chebyshev.node] using hz
    rw [hz', mul_zero]

private lemma negOnePow_mul_derivative_basis_mul_derivative_T_pos
    {L : ℕ} (hL : 0 < L) {x : ℝ}
    (hx : (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval x = 0)
    {i : ℕ} (hi : i ≤ L) :
    0 < (-1 : ℝ) ^ i *
        (Lagrange.basis (Finset.range (L + 1))
          (Polynomial.Chebyshev.node L) i).derivative.eval x *
        (Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval x := by
  classical
  let s := Finset.range (L + 1)
  let v := Polynomial.Chebyshev.node L
  let T : ℝ[X] := Polynomial.Chebyshev.T ℝ (L : ℤ)
  let A : ℝ := (L : ℝ) * 2 ^ (L - 1)
  let t : ℝ := v i
  let E : ℝ[X] := Lagrange.nodal (s.erase i) v
  let w : ℝ := Lagrange.nodalWeight s v i
  have hiS : i ∈ s := by simp [s, hi]
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hxnode : ∀ j ∈ s, x ≠ v j := by
    intro j hj hxj
    have hjL : j ≤ L := by simpa [s] using hj
    have hnode := Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hjL)
    change x = Polynomial.Chebyshev.node L j at hxj
    rw [← hxj, hx] at hnode
    exact (pow_ne_zero j (by norm_num : (-1 : ℝ) ≠ 0)) hnode.symm
  have hxabs : |x| < 1 := by
    have hxle : |x| ≤ 1 :=
      (Polynomial.Chebyshev.abs_eval_T_real_le_one_iff
        (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hL)) x).mpr (by simp [hx])
    refine lt_of_le_of_ne hxle ?_
    intro heq
    have hone := Polynomial.Chebyshev.one_le_abs_eval_T_real (L : ℤ) (le_of_eq heq.symm)
    rw [hx] at hone
    norm_num at hone
  have hxt : 0 < 1 - x * t := by
    have ht : |t| ≤ 1 := by
      exact abs_le.mpr Polynomial.Chebyshev.node_mem_Icc
    have hprod : |x * t| < 1 := calc
      |x * t| = |x| * |t| := abs_mul x t
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left ht (abs_nonneg x)
      _ < 1 := by simpa using hxabs
    linarith [le_abs_self (x * t)]
  have hxtne : x - t ≠ 0 := sub_ne_zero.mpr (hxnode i hiS)
  have hw : 0 < (-1 : ℝ) ^ i * w := by
    have hw' := inv_pos_of_pos (Polynomial.Chebyshev.zero_lt_prod_node_sub_node hi)
    dsimp [w, Lagrange.nodalWeight, v, s]
    rw [Finset.prod_inv_distrib]
    simpa [mul_inv, ← inv_pow, inv_neg_one, mul_comm] using hw'
  have hpoly :
      C A * ((X - C t) * E) = (X ^ 2 - 1) * T.derivative := by
    rw [← Lagrange.nodal_eq_mul_nodal_erase hiS]
    exact chebyshev_nodal_eq hL
  have hode := congrArg (Polynomial.eval x)
    (Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
      (R := ℝ) (L : ℤ))
  have hode' : (1 - x ^ 2) * T.derivative.derivative.eval x = x * T.derivative.eval x := by
    simpa [T, hx] using hode
  have hpolyEval := congrArg (Polynomial.eval x) hpoly
  have hpolyDeriv := congrArg Polynomial.derivative hpoly
  have hpolyDerivEval := congrArg (Polynomial.eval x) hpolyDeriv
  have hp0 : A * (x - t) * E.eval x = (x ^ 2 - 1) * T.derivative.eval x := by
    simpa [mul_assoc] using hpolyEval
  have hp1 : A * (E.eval x + (x - t) * E.derivative.eval x) =
      2 * x * T.derivative.eval x +
        (x ^ 2 - 1) * T.derivative.derivative.eval x := by
    simpa [Polynomial.derivative_mul, pow_two, two_mul] using hpolyDerivEval
  have hFder :
      2 * x * T.derivative.eval x +
          (x ^ 2 - 1) * T.derivative.derivative.eval x =
        x * T.derivative.eval x := by
    nlinarith [hode']
  rw [hFder] at hp1
  have hE :
      A * (x - t) ^ 2 * E.derivative.eval x =
        T.derivative.eval x * (1 - x * t) := by
    linear_combination (x - t) * hp1 - hp0
  have hD : T.derivative.eval x ≠ 0 := by
    intro hzero
    have hNeval :
        (Lagrange.nodal s v).eval x ≠ 0 := Lagrange.eval_nodal_not_at_node hxnode
    have hid := congrArg (Polynomial.eval x) (chebyshev_nodal_eq hL)
    have hid' : A * (Lagrange.nodal s v).eval x =
        (x ^ 2 - 1) * T.derivative.eval x := by
      simpa [A, T, s, v] using hid
    rw [hzero, mul_zero] at hid'
    exact hNeval ((mul_eq_zero.mp hid').resolve_left (ne_of_gt hA))
  have hbasis : Lagrange.basis s v i = C w * E := by
    simp [Lagrange.basis, Lagrange.basisDivisor, Lagrange.nodalWeight,
      Lagrange.nodal, E, w, Finset.prod_mul_distrib, ← map_prod]
  rw [show Finset.range (L + 1) = s from rfl,
    show Polynomial.Chebyshev.node L = v from rfl, hbasis]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  have hfactor : 0 < A * (x - t) ^ 2 := mul_pos hA (sq_pos_of_ne_zero hxtne)
  have hED : 0 < E.derivative.eval x * T.derivative.eval x := by
    apply (mul_pos_iff.mpr ?_)
    rcases lt_or_gt_of_ne hD with hneg | hpos
    · right
      constructor
      · nlinarith [hE]
      · exact hneg
    · left
      constructor
      · nlinarith [hE]
      · exact hpos
  calc
    (-1 : ℝ) ^ i * (w * E.derivative.eval x) * T.derivative.eval x =
        ((-1 : ℝ) ^ i * w) *
          (E.derivative.eval x * T.derivative.eval x) := by ring
    _ > 0 := mul_pos hw hED

/-- If a degree-at-most-`L` real polynomial has absolute value at most one at
all `L+1` extrema of `T_L`, then at every real zero of `T_L` its derivative is
no larger in absolute value than the derivative of `T_L`. [the stated inputs](hyp:L,hL,Q,hQ,hnodes,x,hx) establish [the stated conclusion](goal). -/
theorem abs_eval_derivative_le_chebyshev_at_root
    {L : ℕ} (hL : 0 < L) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ L)
    (hnodes : ∀ i, i ≤ L →
      |Q.eval (Polynomial.Chebyshev.node L i)| ≤ 1)
    {x : ℝ} (hx : (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval x = 0) :
    |Q.derivative.eval x| ≤
      |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval x| := by
  classical
  let s := Finset.range (L + 1)
  let v := Polynomial.Chebyshev.node L
  let T : ℝ[X] := Polynomial.Chebyshev.T ℝ (L : ℤ)
  let c : ℕ → ℝ := fun i ↦ (Lagrange.basis s v i).derivative.eval x
  have hQdegree : Q.degree < s.card := by
    simp only [s, Finset.card_range]
    exact lt_of_le_of_lt Q.degree_le_natDegree
      (by exact_mod_cast (Nat.lt_succ_of_le hQ))
  have hTdegree : T.degree < s.card := by
    rw [show T.degree = (L : ℕ) by simp [T], show s.card = L + 1 by simp [s]]
    exact_mod_cast Nat.lt_succ_self L
  have hQinterp := Lagrange.eq_interpolate
    (Polynomial.Chebyshev.strictAntiOn_node L).injOn hQdegree
  have hTinterp := Lagrange.eq_interpolate
    (Polynomial.Chebyshev.strictAntiOn_node L).injOn hTdegree
  have hQder : Q.derivative.eval x =
      ∑ i ∈ s, Q.eval (v i) * c i := by
    calc
      Q.derivative.eval x =
          (Lagrange.interpolate s v (fun i ↦ Q.eval (v i))).derivative.eval x := by
        rw [← hQinterp]
      _ = ∑ i ∈ s, Q.eval (v i) * c i := by
        simp [Lagrange.interpolate_apply, eval_finsetSum, c]
  have hTder : T.derivative.eval x = ∑ i ∈ s, (-1 : ℝ) ^ i * c i := by
    calc
      T.derivative.eval x =
          (Lagrange.interpolate s v (fun i ↦ T.eval (v i))).derivative.eval x := by
        rw [← hTinterp]
      _ = ∑ i ∈ s, (-1 : ℝ) ^ i * c i := by
        rw [show (Lagrange.interpolate s v (fun i ↦ T.eval (v i))).derivative.eval x =
            ∑ i ∈ s, T.eval (v i) * c i by
          simp [Lagrange.interpolate_apply, eval_finsetSum, c]]
        apply Finset.sum_congr rfl
        intro i hi
        have hiL : i ≤ L := by simpa [s] using hi
        rw [show T.eval (v i) = (-1 : ℝ) ^ i by
          exact Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hiL)]
  have hsign : ∀ i ∈ s, 0 < (-1 : ℝ) ^ i * c i * T.derivative.eval x := by
    intro i hi
    have hiL : i ≤ L := by simpa [s] using hi
    exact negOnePow_mul_derivative_basis_mul_derivative_T_pos hL hx hiL
  have hD : T.derivative.eval x ≠ 0 := by
    intro hzero
    have := hsign 0 (by simp [s])
    rw [hzero, mul_zero] at this
    exact lt_irrefl 0 this
  have hmass : ∑ i ∈ s, |c i| = |T.derivative.eval x| := by
    rcases lt_or_gt_of_ne hD with hneg | hpos
    · rw [abs_of_neg hneg, hTder, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hci : (-1 : ℝ) ^ i * c i < 0 := by
        have := hsign i hi
        nlinarith
      calc
        |c i| = |(-1 : ℝ) ^ i * c i| := by
          rw [abs_mul, abs_neg_one_pow, one_mul]
        _ = -((-1 : ℝ) ^ i * c i) := abs_of_neg hci
    · rw [abs_of_pos hpos, hTder]
      apply Finset.sum_congr rfl
      intro i hi
      have hci : 0 < (-1 : ℝ) ^ i * c i := by
        have := hsign i hi
        nlinarith
      calc
        |c i| = |(-1 : ℝ) ^ i * c i| := by
          rw [abs_mul, abs_neg_one_pow, one_mul]
        _ = (-1 : ℝ) ^ i * c i := abs_of_pos hci
  calc
    |Q.derivative.eval x| = |∑ i ∈ s, Q.eval (v i) * c i| := by rw [hQder]
    _ ≤ ∑ i ∈ s, |Q.eval (v i) * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |c i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hiL : i ≤ L := by simpa [s] using hi
      calc
        |Q.eval (v i)| * |c i| ≤ 1 * |c i| :=
          mul_le_mul_of_nonneg_right (by simpa [v] using hnodes i hiL) (abs_nonneg _)
        _ = |c i| := one_mul _
    _ = |T.derivative.eval x| := hmass

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
