/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ChebyshevChordGeometry
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.HalfPlaneDerivativeComparison
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# A real first-derivative corollary of the Duffin--Schaeffer inequality

This module proves the Chebyshev vertical-modulus and rootwise derivative
comparisons, expresses differentiation in Chebyshev interpolation weights, and
derives the real first-derivative bound on `[-1,1]` that follows from the
Duffin--Schaeffer inequality.
-/

@[expose] public section

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-! ## Chebyshev root products -/



private lemma vertical_rootDistance_le_endpoint
    {a x y : ℝ} (ha : a ≤ x) (hx : x ≤ 1) :
    ‖((x - a : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ ≤
      ‖((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero,
    Complex.I_im, zero_mul, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, mul_one]
  nlinarith [sq_nonneg (x - a), sq_nonneg (1 - x)]

/-- The product of distances from a point above `[-1,1]` to the degree-`L`
Chebyshev roots is no larger than the corresponding product above the endpoint
`1` at the same height. [the stated inputs](hyp:L,hL,x,hx,y) establish [the stated conclusion](goal). -/
theorem prod_norm_sub_chebyshevZero_le_endpoint
    {L : ℕ} (hL : 0 < L) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) (y : ℝ) :
    (∏ k ∈ Finset.range L,
        ‖((x - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖) ≤
      ∏ k ∈ Finset.range L,
        ‖((1 - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
  rcases exists_rootProduct_dominating_abscissa_past_chebyshevZeros
      hL hx y with ⟨x₀, hx₀, hzeros, hdom⟩
  refine hdom.trans ?_
  apply Finset.prod_le_prod
  · intro k hk
    positivity
  intro k hk
  exact vertical_rootDistance_le_endpoint (hzeros k hk) hx₀.2

/-- For positive degree, the complex norm of a Chebyshev evaluation is its
leading-coefficient norm times the product of the distances to the explicit
cosine roots. [the stated inputs](hyp:L,hL,x,y) establish [the stated conclusion](goal). -/
theorem norm_eval_chebyshev_eq_leadingCoeff_mul_rootProduct
    {L : ℕ} (hL : 0 < L) (x y : ℝ) :
    ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ =
      ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).leadingCoeff‖ *
        ∏ k ∈ Finset.range L,
          ‖((x - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  let pR : ℝ[X] := Polynomial.Chebyshev.T ℝ (L : ℤ)
  let pC : ℂ[X] := Polynomial.Chebyshev.T ℂ (L : ℤ)
  have hinj : Set.InjOn
      (fun k : ℕ => Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (L : ℝ))))
      (Finset.range L) :=
    (Finset.range L).nodup_map_iff_injOn.mp
      (Polynomial.Chebyshev.roots_T_real_nodup L)
  have hcard : pR.roots.card = pR.natDegree := by
    dsimp [pR]
    rw [Polynomial.Chebyshev.roots_T_real, Finset.card_val,
      Finset.card_image_of_injOn hinj, Finset.card_range,
      Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
  have hrootsMap :
      pR.roots.map Complex.ofReal = (pR.map Complex.ofRealHom).roots := by
    simpa using
      (Polynomial.roots_map_of_injective_of_card_eq_natDegree
        (p := pR) (f := Complex.ofRealHom) Complex.ofReal_injective hcard)
  have hmap : pR.map Complex.ofRealHom = pC := by
    dsimp [pR, pC]
    exact Polynomial.Chebyshev.map_T Complex.ofRealHom (L : ℤ)
  have hroots :
      pC.roots =
        (Finset.range L).val.map (fun k : ℕ => (chebyshevZero L k : ℂ)) := by
    rw [← hmap, ← hrootsMap]
    dsimp [pR]
    rw [Polynomial.Chebyshev.roots_T_real,
      Finset.image_val_of_injOn hinj, Multiset.map_map]
    congr 1
    funext k
    apply congrArg Complex.ofReal
    apply congrArg Real.cos
    norm_num [chebyshevZero, chebyshevRootAngle, Nat.cast_add, Nat.cast_mul]
  have hcardC : pC.roots.card = pC.natDegree := by
    rw [hroots, Multiset.card_map, Finset.card_val, Finset.card_range]
    dsimp [pC]
    rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := pC) hcardC
  have heval := congrArg (Polynomial.eval z) hfac
  rw [eval_mul, eval_C, eval_multiset_prod, hroots] at heval
  simp only [Multiset.map_map, Function.comp_apply, eval_sub, eval_X, eval_C] at heval
  change pC.leadingCoeff *
      (∏ k ∈ Finset.range L, (z - (chebyshevZero L k : ℂ))) = pC.eval z at heval
  rw [← heval, norm_mul, Complex.norm_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  congr 1
  dsimp [z]
  push_cast
  ring

/-! ## Vertical modulus domination -/


/-- Above any point `x` of `[-1,1]`, the complex modulus of the degree-`L`
Chebyshev polynomial is no larger than its modulus at the point with the same
imaginary part above the endpoint `1`. [the stated inputs](hyp:L,x,hx,y) establish [the stated conclusion](goal). -/
theorem norm_eval_chebyshev_le_endpoint_vertical
    {L : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) (y : ℝ) :
    ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((1 : ℂ) + (y : ℂ) * Complex.I)‖ := by
  by_cases hL : L = 0
  · subst L
    simp
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  calc
    ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ =
        ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).leadingCoeff‖ *
          ∏ k ∈ Finset.range L,
            ‖((x - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ :=
      norm_eval_chebyshev_eq_leadingCoeff_mul_rootProduct hLpos x y
    _ ≤ ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).leadingCoeff‖ *
          ∏ k ∈ Finset.range L,
            ‖((1 - chebyshevZero L k : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ :=
      mul_le_mul_of_nonneg_left
        (prod_norm_sub_chebyshevZero_le_endpoint hLpos hx y) (norm_nonneg _)
    _ = ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((1 : ℂ) + (y : ℂ) * Complex.I)‖ := by
      simpa using
        (norm_eval_chebyshev_eq_leadingCoeff_mul_rootProduct hLpos (1 : ℝ) y).symm

/-! ## Derivative comparison at Chebyshev zeros -/


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

/-! ## Propagation from root control -/


/-- If a degree-at-most-`L` real polynomial has derivative no larger than
`T_L'` at every zero of `T_L`, then its derivative is bounded by `L²`
throughout `[-1,1]`. [the stated inputs](hyp:L,hL,Q,hQ,hroots,x,hx) establish [the stated conclusion](goal). -/
theorem abs_eval_derivative_le_sq_of_chebyshev_root_control
    {L : ℕ} (hL : 0 < L) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ L)
    (hroots : ∀ z : ℝ,
      (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval z = 0 →
        |Q.derivative.eval z| ≤
          |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval z|)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |Q.derivative.eval x| ≤ (L : ℝ) ^ 2 := by
  have hendpoint := abs_eval_derivative_le_chebyshev_endpoint_of_root_control
    hL Q hQ hroots hx (fun y ↦ norm_eval_chebyshev_le_endpoint_vertical hx y)
  rw [Polynomial.Chebyshev.derivative_T_eval_one] at hendpoint
  simpa [abs_of_nonneg (sq_nonneg (L : ℝ))] using hendpoint

/-! ## Chebyshev differentiation weights -/


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

/-! ## Real first-derivative corollary -/


/-- If a real polynomial of degree at most `L`, with `L > 0`, is bounded by
`C` at every degree-`L` Chebyshev extremum, then its derivative is bounded by
`L² C` throughout `[-1,1]`. [the stated inputs](hyp:Q,L,hL,hQ,C,hC,hnodes,x,hx) establish [the stated conclusion](goal). -/
theorem duffinSchaeffer_derivative_le
    (Q : Polynomial ℝ) {L : ℕ} (hL : 0 < L) (hQ : Q.natDegree ≤ L)
    {C : ℝ} (hC : 0 ≤ C)
    (hnodes : ∀ i, i ≤ L →
      |Q.eval (Polynomial.Chebyshev.node L i)| ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |Q.derivative.eval x| ≤ (L : ℝ) ^ 2 * C := by
  rw [eval_derivative_eq_sum_chebyshevDerivativeWeight Q hQ x]
  calc
    |∑ i ∈ Finset.range (L + 1),
        Q.eval (Polynomial.Chebyshev.node L i) * chebyshevDerivativeWeight L x i| ≤
        ∑ i ∈ Finset.range (L + 1),
          |Q.eval (Polynomial.Chebyshev.node L i) *
            chebyshevDerivativeWeight L x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (L + 1),
          C * |chebyshevDerivativeWeight L x i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (hnodes i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (abs_nonneg _)
    _ = C * ∑ i ∈ Finset.range (L + 1),
          |chebyshevDerivativeWeight L x i| := by rw [Finset.mul_sum]
    _ ≤ C * (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_abs_chebyshevDerivativeWeight_le_sq hL hx) hC
    _ = (L : ℝ) ^ 2 * C := by ring

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
