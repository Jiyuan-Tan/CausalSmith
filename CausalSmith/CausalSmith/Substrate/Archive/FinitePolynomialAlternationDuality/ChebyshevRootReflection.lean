/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Reflection across a vertical line at Chebyshev roots

This module isolates the algebraic half of the Duffin--Schaeffer comparison.
Rootwise derivative control yields a reflected complex polynomial whose
boundary modulus is the Chebyshev modulus and whose derivative dominates the
original derivative at the reflection line.
-/

@[expose] public section

open Polynomial Set

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

private noncomputable def reflectionRoot (L k : ℕ) : ℝ :=
  Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (L : ℝ)))

private lemma reflectionRoot_injOn (L : ℕ) :
    Set.InjOn (reflectionRoot L) (Finset.range L) := by
  exact (Finset.range L).nodup_map_iff_injOn.mp
    (Polynomial.Chebyshev.roots_T_real_nodup L)

private lemma eval_chebyshev_T_reflectionRoot {L i : ℕ} (hi : i < L) :
    (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval (reflectionRoot L i) = 0 := by
  apply (Polynomial.mem_roots
    (Polynomial.Chebyshev.T_ne_zero ℝ (L : ℤ))).mp
  rw [Polynomial.Chebyshev.roots_T_real]
  change reflectionRoot L i ∈ Finset.image (reflectionRoot L) (Finset.range L)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

private lemma chebyshev_T_eq_rootProduct {L : ℕ} :
    Polynomial.Chebyshev.T ℝ (L : ℤ) =
      C (Polynomial.Chebyshev.T ℝ (L : ℤ)).leadingCoeff *
        ∏ k ∈ Finset.range L, (X - C (reflectionRoot L k)) := by
  let T := Polynomial.Chebyshev.T ℝ (L : ℤ)
  have hinj := reflectionRoot_injOn L
  have hroots : T.roots = (Finset.range L).val.map (reflectionRoot L) := by
    dsimp [T]
    rw [Polynomial.Chebyshev.roots_T_real]
    change (Finset.image (reflectionRoot L) (Finset.range L)).val = _
    rw [Finset.image_val_of_injOn hinj]
    simp [Finset.range_val]
  have hsplits : T.Splits := by
    rw [Polynomial.splits_iff_card_roots, hroots, Multiset.card_map,
      Finset.card_val, Finset.card_range]
    dsimp [T]
    rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
  have hfac := hsplits.eq_prod_roots
  rw [hroots] at hfac
  simp only [Multiset.map_map, Function.comp_apply] at hfac
  simpa [T, Finset.prod_eq_multiset_prod, Finset.range_val] using hfac

private lemma eval_chebyshev_T_derivative_at_root {L i : ℕ} (hi : i < L) :
    (Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval (reflectionRoot L i) =
      (Polynomial.Chebyshev.T ℝ (L : ℤ)).leadingCoeff *
        ∏ j ∈ (Finset.range L).erase i,
          (reflectionRoot L i - reflectionRoot L j) := by
  conv_lhs => rw [chebyshev_T_eq_rootProduct]
  rw [derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_prod_finset, eval_mul, eval_C, eval_finsetSum]
  simp only [eval_prod, eval_sub, eval_X, eval_C, derivative_sub,
    derivative_X, derivative_C, sub_zero, mul_one]
  rw [Finset.sum_eq_single i]
  · intro j hj hji
    exact Finset.prod_eq_zero
      (s := (Finset.range L).erase j)
      (f := fun k => reflectionRoot L i - reflectionRoot L k)
      (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_range.mpr hi⟩)
      (sub_self _)
  · exact fun hnot => (hnot (Finset.mem_range.mpr hi)).elim

private lemma chebyshev_derivative_mul_lagrangeBasis {L i : ℕ} (hi : i < L)
    (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval (reflectionRoot L i) *
        (Lagrange.basis (Finset.range L) (reflectionRoot L) i).eval x =
      (Polynomial.Chebyshev.T ℝ (L : ℤ)).leadingCoeff *
        ∏ j ∈ (Finset.range L).erase i, (x - reflectionRoot L j) := by
  have hden :
      ∏ j ∈ (Finset.range L).erase i,
          (reflectionRoot L i - reflectionRoot L j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr ((reflectionRoot_injOn L).ne
      (Finset.mem_range.mpr hi) (Finset.mem_of_mem_erase hj)
      (Finset.ne_of_mem_erase hj).symm)
  rw [eval_chebyshev_T_derivative_at_root hi, Lagrange.basis, eval_prod]
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_inv_distrib]
  field_simp

private lemma chebyshev_T_complex_eq_rootProduct {L : ℕ} :
    Polynomial.Chebyshev.T ℂ (L : ℤ) =
      C (Polynomial.Chebyshev.T ℂ (L : ℤ)).leadingCoeff *
        ∏ k ∈ Finset.range L, (X - C (reflectionRoot L k : ℂ)) := by
  have h := congrArg (Polynomial.map Complex.ofRealHom)
    (chebyshev_T_eq_rootProduct (L := L))
  simpa [Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.Chebyshev.map_T] using h

private noncomputable def reflectedRootProduct (L : ℕ) (x : ℝ) : Polynomial ℂ :=
  C (Polynomial.Chebyshev.T ℂ (L : ℤ)).leadingCoeff *
    ∏ k ∈ Finset.range L,
      (X + C (((|x - reflectionRoot L k| : ℝ) : ℂ)))

private lemma reflectedRootProduct_natDegree_le (L : ℕ) (x : ℝ) :
    (reflectedRootProduct L x).natDegree ≤ L := by
  unfold reflectedRootProduct
  calc
    (C (Polynomial.Chebyshev.T ℂ (L : ℤ)).leadingCoeff *
        ∏ k ∈ Finset.range L,
          (X + C (((|x - reflectionRoot L k| : ℝ) : ℂ)))).natDegree ≤
      (C (Polynomial.Chebyshev.T ℂ (L : ℤ)).leadingCoeff).natDegree +
        (∏ k ∈ Finset.range L,
          (X + C (((|x - reflectionRoot L k| : ℝ) : ℂ)))).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + ∑ k ∈ Finset.range L,
          (X + C (((|x - reflectionRoot L k| : ℝ) : ℂ))).natDegree := by
        simp only [natDegree_C, zero_add]
        exact Polynomial.natDegree_prod_le (R := ℂ) (Finset.range L)
          (fun k => X + C (((|x - reflectionRoot L k| : ℝ) : ℂ)))
    _ = L := by simp

private lemma reflectedRootProduct_vertical_norm (L : ℕ) (x y : ℝ) :
    ‖(reflectedRootProduct L x).eval ((y : ℂ) * Complex.I)‖ =
      ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
  rw [reflectedRootProduct]
  conv_rhs => rw [chebyshev_T_complex_eq_rootProduct]
  simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X, norm_mul,
    Complex.norm_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]

private lemma reflectedRootProduct_derivative_norm (L : ℕ) (x : ℝ) :
    ‖(reflectedRootProduct L x).derivative.eval 0‖ =
      |(Polynomial.Chebyshev.T ℝ (L : ℤ)).leadingCoeff| *
        ∑ i ∈ Finset.range L,
          ∏ j ∈ (Finset.range L).erase i, |x - reflectionRoot L j| := by
  rw [reflectedRootProduct, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_prod_finset, eval_mul, eval_C, eval_finsetSum]
  simp only [eval_prod, eval_add, eval_X, eval_C, derivative_add,
    derivative_X, derivative_C, add_zero, mul_one, zero_add]
  rw [norm_mul]
  congr 1
  · rw [Polynomial.Chebyshev.leadingCoeff_T,
      Polynomial.Chebyshev.leadingCoeff_T]
    simp
  · have hcast :
        (∑ i ∈ Finset.range L,
            ∏ j ∈ (Finset.range L).erase i,
              (((|x - reflectionRoot L j| : ℝ) : ℂ))) =
          ((∑ i ∈ Finset.range L,
              ∏ j ∈ (Finset.range L).erase i,
                |x - reflectionRoot L j| : ℝ) : ℂ) := by
        push_cast
        rfl
    rw [hcast]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity

/-- If a degree-at-most-`L` real polynomial has derivative bounded by `T_L'`
at every real zero of `T_L`, then at any real base point there is a reflected
degree-at-most-`L` complex polynomial with the same vertical boundary modulus
as the translated `T_L` and with derivative at zero dominating the original
derivative at the base point. -/
theorem exists_chebyshevRootReflection
    {L : ℕ} (hL : 0 < L) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ L)
    (hroots : ∀ z : ℝ,
      (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval z = 0 →
        |Q.derivative.eval z| ≤
          |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval z|)
    (x : ℝ) :
    ∃ R : Polynomial ℂ,
      R.natDegree ≤ L ∧
      (∀ y : ℝ,
        ‖R.eval ((y : ℂ) * Complex.I)‖ =
          ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
            ((x : ℂ) + (y : ℂ) * Complex.I)‖) ∧
      |Q.derivative.eval x| ≤ ‖R.derivative.eval 0‖ := by
  have hPnat : Q.derivative.natDegree < L := by
    refine lt_of_le_of_lt
      ((Polynomial.natDegree_derivative_le Q).trans
        (Nat.sub_le_sub_right hQ 1)) ?_
    exact Nat.sub_lt hL Nat.zero_lt_one
  have hPdegree : Q.derivative.degree < (L : WithBot ℕ) := by
    by_cases hP : Q.derivative = 0
    · simp [hP]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP).mp hPnat
  have hinterp :
      Q.derivative = Lagrange.interpolate (Finset.range L) (reflectionRoot L)
        (fun i => Q.derivative.eval (reflectionRoot L i)) := by
    apply Lagrange.eq_interpolate (reflectionRoot_injOn L)
    simpa using hPdegree
  refine ⟨reflectedRootProduct L x, reflectedRootProduct_natDegree_le L x,
    reflectedRootProduct_vertical_norm L x, ?_⟩
  rw [hinterp, Lagrange.interpolate_apply, eval_finsetSum]
  simp only [eval_mul, eval_C]
  calc
    |∑ i ∈ Finset.range L,
        Q.derivative.eval (reflectionRoot L i) *
          (Lagrange.basis (Finset.range L) (reflectionRoot L) i).eval x| ≤
        ∑ i ∈ Finset.range L,
          |Q.derivative.eval (reflectionRoot L i) *
            (Lagrange.basis (Finset.range L) (reflectionRoot L) i).eval x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range L,
          |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval
              (reflectionRoot L i) *
            (Lagrange.basis (Finset.range L) (reflectionRoot L) i).eval x| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (hroots (reflectionRoot L i)
          (eval_chebyshev_T_reflectionRoot (Finset.mem_range.mp hi)))
        (abs_nonneg _)
    _ = ∑ i ∈ Finset.range L,
          |(Polynomial.Chebyshev.T ℝ (L : ℤ)).leadingCoeff| *
            ∏ j ∈ (Finset.range L).erase i, |x - reflectionRoot L j| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [chebyshev_derivative_mul_lagrangeBasis (Finset.mem_range.mp hi),
        abs_mul, Finset.abs_prod]
    _ = |(Polynomial.Chebyshev.T ℝ (L : ℤ)).leadingCoeff| *
          ∑ i ∈ Finset.range L,
            ∏ j ∈ (Finset.range L).erase i, |x - reflectionRoot L j| := by
      rw [Finset.mul_sum]
    _ = ‖(reflectedRootProduct L x).derivative.eval 0‖ :=
      (reflectedRootProduct_derivative_norm L x).symm

end CausalSmith.Substrate.FinitePolynomialAlternationDuality
