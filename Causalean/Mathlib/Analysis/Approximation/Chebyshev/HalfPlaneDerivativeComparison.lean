/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.Polynomial.GaussLucas
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Half-plane derivative comparison at Chebyshev roots

This module combines root reflection with a half-plane boundary estimate to
propagate derivative control at the real roots of a Chebyshev polynomial to a
sharp endpoint comparison.
-/

@[expose] public section

open Polynomial Set Filter Bornology
open Asymptotics
open scoped Topology

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-! ## Reflection at Chebyshev roots -/


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
derivative at the base point. [the stated inputs](hyp:L,hL,Q,hQ,hroots,x) establish [the stated conclusion](goal). -/
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

/-! ## Half-plane boundary comparison -/


private lemma chebyshev_root_re_lt_one {L : ℕ} (hL : 0 < L) {z : ℂ}
    (hz : (Polynomial.Chebyshev.T ℂ (L : ℤ)).eval z = 0) :
    z.re < 1 := by
  let pR : ℝ[X] := Polynomial.Chebyshev.T ℝ (L : ℤ)
  let pC : ℂ[X] := Polynomial.Chebyshev.T ℂ (L : ℤ)
  have hcard : pR.roots.card = pR.natDegree := by
    dsimp [pR]
    rw [Polynomial.Chebyshev.roots_T_real, Finset.card_val,
      Finset.card_image_of_injOn
        ((Finset.range L).nodup_map_iff_injOn.mp
          (Polynomial.Chebyshev.roots_T_real_nodup L)),
      Finset.card_range, Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
  have hmap : pR.map Complex.ofRealHom = pC := by
    dsimp [pR, pC]
    exact Polynomial.Chebyshev.map_T Complex.ofRealHom (L : ℤ)
  have hroots : pR.roots.map Complex.ofReal = pC.roots := by
    rw [← hmap]
    exact Polynomial.roots_map_of_injective_of_card_eq_natDegree
      (p := pR) (f := Complex.ofRealHom) Complex.ofReal_injective hcard
  have hpC : pC ≠ 0 := by
    dsimp [pC]
    exact Polynomial.Chebyshev.T_ne_zero ℂ (L : ℤ)
  have hzmem : z ∈ pC.roots := (Polynomial.mem_roots hpC).mpr hz
  rw [← hroots] at hzmem
  obtain ⟨r, hrmem, rfl⟩ := Multiset.mem_map.mp hzmem
  have hpR : pR ≠ 0 := by
    dsimp [pR]
    exact Polynomial.Chebyshev.T_ne_zero ℝ (L : ℤ)
  have hrzero : pR.eval r = 0 := (Polynomial.mem_roots hpR).mp hrmem
  have hrabs : |r| ≤ 1 := by
    by_contra hn
    have ht := Polynomial.Chebyshev.one_lt_abs_eval_T_real
      (n := (L : ℤ)) (by exact_mod_cast (Nat.ne_of_gt hL)) (lt_of_not_ge hn)
    rw [show Polynomial.Chebyshev.T ℝ (L : ℤ) = pR from rfl, hrzero] at ht
    norm_num at ht
  have hrle : r ≤ 1 := (le_abs_self r).trans hrabs
  have hrne : r ≠ 1 := by
    intro hr
    subst r
    simp [pR] at hrzero
  simpa using lt_of_le_of_ne hrle hrne

private lemma norm_eval_div_le_one_on_right_half_plane
    (R S : Polynomial ℂ) (hdeg : R.degree ≤ S.degree)
    (hSroots : ∀ z : ℂ, S.eval z = 0 → z.re < 0)
    (hvertical : ∀ y : ℝ, ‖R.eval ((y : ℂ) * Complex.I)‖ ≤
      ‖S.eval ((y : ℂ) * Complex.I)‖) :
    ∀ z : ℂ, 0 ≤ z.re → ‖R.eval z / S.eval z‖ ≤ 1 := by
  have hSright : ∀ z : ℂ, 0 ≤ z.re → S.eval z ≠ 0 := by
    intro z hz hzero
    exact (not_lt_of_ge hz) (hSroots z hzero)
  let f : ℂ → ℂ := fun z => R.eval z / S.eval z
  have hdiff : DiffContOnCl ℂ f {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.diffContOnCl
    rw [Complex.closure_setOfPred_lt_re 0]
    exact R.differentiableOn.fun_div S.differentiableOn
      (fun z hz => hSright z hz)
  have hquotBound : IsBoundedUnder (· ≤ ·) (cobounded ℂ)
      (fun z => ‖R.eval z / S.eval z‖) :=
    div_isBoundedUnder_of_isBigO
      (Polynomial.isBigO_cobounded_of_degree_le hdeg)
  have hexp : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}]
        fun z => Real.exp (B * ‖z‖ ^ c) := by
    refine ⟨1, one_lt_two, 0, ?_⟩
    have hO : f =O[cobounded ℂ] (fun _ => (1 : ℝ)) := by
      simpa [f] using hquotBound.isBigO_one ℝ
    simpa using hO.mono inf_le_left
  have hre : IsBoundedUnder (· ≤ ·) atTop (fun x : ℝ => ‖f x‖) := by
    have ht :=
      (RCLike.tendsto_ofReal_atTop_cobounded ℂ).isBoundedUnder_comp hquotBound
    simpa [f, Function.comp_def] using ht
  have him : ∀ y : ℝ, ‖f (y * Complex.I)‖ ≤ 1 := by
    intro y
    rw [show f (y * Complex.I) = R.eval (y * Complex.I) /
      S.eval (y * Complex.I) from rfl, norm_div]
    exact (div_le_one (norm_pos_iff.mpr (hSright _ (by simp)))).mpr (hvertical y)
  intro z hz
  exact PhragmenLindelof.right_half_plane_of_bounded_on_real
    (f := f) (C := 1) hdiff hexp hre him hz

private lemma norm_eval_derivative_zero_le_of_left_half_plane_roots
    (R S : Polynomial ℂ) (hSdeg : 0 < S.degree) (hdeg : R.degree ≤ S.degree)
    (hSroots : ∀ z : ℂ, S.eval z = 0 → z.re < 0)
    (hSderiv : S.derivative.eval 0 ≠ 0)
    (hvertical : ∀ y : ℝ, ‖R.eval ((y : ℂ) * Complex.I)‖ ≤
      ‖S.eval ((y : ℂ) * Complex.I)‖) :
    ‖R.derivative.eval 0‖ ≤ ‖S.derivative.eval 0‖ := by
  have hquot := norm_eval_div_le_one_on_right_half_plane R S hdeg hSroots hvertical
  by_contra hn
  have hlt : ‖S.derivative.eval 0‖ < ‖R.derivative.eval 0‖ := lt_of_not_ge hn
  let lam : ℂ := R.derivative.eval 0 / S.derivative.eval 0
  have hlam : 1 < ‖lam‖ := by
    rw [show lam = R.derivative.eval 0 / S.derivative.eval 0 from rfl, norm_div]
    exact (one_lt_div (norm_pos_iff.mpr hSderiv)).mpr hlt
  let P : ℂ[X] := R - C lam * S
  have hPder : P.derivative.eval 0 = 0 := by
    simp [P, show lam = R.derivative.eval 0 / S.derivative.eval 0 from rfl]
    field_simp
    ring
  have hPnoroot : ∀ z : ℂ, 0 ≤ z.re → P.eval z ≠ 0 := by
    intro z hz hzero
    have hSz : S.eval z ≠ 0 := by
      intro hs
      exact (not_lt_of_ge hz) (hSroots z hs)
    have heq : R.eval z = lam * S.eval z := by
      simp [P] at hzero
      exact sub_eq_zero.mp hzero
    have hf : R.eval z / S.eval z = lam := by
      rw [heq, mul_div_cancel_right₀ _ hSz]
    have hh := hquot z hz
    rw [hf] at hh
    exact (not_lt_of_ge hh) hlam
  by_cases hPpos : 0 < P.degree
  · have hroot : (0 : ℂ) ∈ P.derivative.rootSet ℂ := by
      rw [Polynomial.mem_rootSet, coe_aeval_eq_eval]
      exact ⟨Polynomial.derivative_ne_zero.mpr
        (Polynomial.natDegree_pos_iff_degree_pos.mpr hPpos).ne', hPder⟩
    have hconv := Polynomial.rootSet_derivative_subset_convexHull_rootSet hPpos hroot
    have hsubset : P.rootSet ℂ ⊆ {z : ℂ | z.re < 0} := by
      intro z hz
      have hz0 : P.eval z = 0 := by
        rw [Polynomial.mem_rootSet, coe_aeval_eq_eval] at hz
        exact hz.2
      exact lt_of_not_ge (fun h => hPnoroot z h hz0)
    have hh := (convexHull_min hsubset (convex_halfSpace_re_lt 0)) hconv
    simpa using hh
  · have hPle : P.degree ≤ 0 := le_of_not_gt hPpos
    have hPC : P = C (P.coeff 0) := Polynomial.eq_C_of_degree_le_zero hPle
    have hrelation : R = C lam * S + C (P.coeff 0) := by
      rw [← hPC]
      simp [P]
    have hSaxis : ∀ y : ℝ, S.eval ((y : ℂ) * Complex.I) ≠ 0 := by
      intro y hs
      exact (not_lt_of_ge (by simp)) (hSroots _ hs)
    have hSnorm : Tendsto
        (fun y : ℝ => ‖S.eval ((y : ℂ) * Complex.I)‖) atTop atTop := by
      apply S.tendsto_norm_atTop hSdeg
      simpa using tendsto_abs_atTop_atTop
    have hScob : Tendsto
        (fun y : ℝ => S.eval ((y : ℂ) * Complex.I)) atTop (cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      exact hSnorm
    have hinv : Tendsto
        (fun y : ℝ => (S.eval ((y : ℂ) * Complex.I))⁻¹) atTop (𝓝 0) :=
      Filter.tendsto_inv₀_cobounded.comp hScob
    have hrat : Tendsto
        (fun y : ℝ => R.eval ((y : ℂ) * Complex.I) /
          S.eval ((y : ℂ) * Complex.I)) atTop (𝓝 lam) := by
      have hc : Tendsto (fun y : ℝ => P.coeff 0 *
          (S.eval ((y : ℂ) * Complex.I))⁻¹) atTop (𝓝 0) := by
        simpa using
          ((tendsto_const_nhds : Tendsto (fun _ : ℝ => P.coeff 0) atTop
            (𝓝 (P.coeff 0))).mul hinv)
      convert (tendsto_const_nhds.add hc) using 1
      · funext y
        rw [hrelation]
        simp only [eval_add, eval_mul, eval_C]
        field_simp [hSaxis y]
      · simp
    have hle : ∀ y : ℝ,
        ‖R.eval ((y : ℂ) * Complex.I) / S.eval ((y : ℂ) * Complex.I)‖ ≤ 1 := by
      intro y
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr (hSaxis y))).mpr (hvertical y)
    have hh : ‖lam‖ ≤ 1 := le_of_tendsto hrat.norm (Eventually.of_forall hle)
    exact (not_lt_of_ge hh) hlam

/-- A degree-at-most-`L` complex polynomial dominated on the imaginary axis by
`z ↦ T_L(1+z)` has derivative at zero no larger than `|T_L'(1)|`. [the stated inputs](hyp:L,hL,R,hR,hvertical) establish [the stated conclusion](goal). -/
theorem norm_eval_derivative_zero_le_chebyshev_endpoint_of_vertical
    {L : ℕ} (hL : 0 < L) (R : Polynomial ℂ) (hR : R.natDegree ≤ L)
    (hvertical : ∀ y : ℝ,
      ‖R.eval ((y : ℂ) * Complex.I)‖ ≤
        ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
          ((1 : ℂ) + (y : ℂ) * Complex.I)‖) :
    ‖R.derivative.eval 0‖ ≤
      |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval 1| := by
  let S : ℂ[X] := (Polynomial.Chebyshev.T ℂ (L : ℤ)).comp (X + C 1)
  have hSnat : S.natDegree = L := by
    change ((Polynomial.Chebyshev.T ℂ (L : ℤ)).comp (X + C 1)).natDegree = L
    rw [Polynomial.natDegree_comp, Polynomial.Chebyshev.natDegree_T,
      Int.natAbs_natCast, Polynomial.natDegree_X_add_C, mul_one]
  have hSdeg : 0 < S.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hSnat]
    exact hL
  have hdeg : R.degree ≤ S.degree := by
    have hSdegree : S.degree = (L : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree (ne_zero_of_degree_gt hSdeg), hSnat]
    rw [hSdegree]
    exact Polynomial.degree_le_of_natDegree_le hR
  have hSroots : ∀ z : ℂ, S.eval z = 0 → z.re < 0 := by
    intro z hz
    have ht : ((1 : ℂ) + z).re < 1 := by
      apply chebyshev_root_re_lt_one hL
      simpa [S, add_comm] using hz
    simpa using ht
  have hSderiv : S.derivative.eval 0 ≠ 0 := by
    simp [S, Polynomial.derivative_comp,
      Polynomial.Chebyshev.derivative_T_eval_one]
    exact_mod_cast (Nat.ne_of_gt hL)
  have hbound := norm_eval_derivative_zero_le_of_left_half_plane_roots
    R S hSdeg hdeg hSroots hSderiv (by simpa [S, add_comm] using hvertical)
  simpa [S, Polynomial.derivative_comp,
    Polynomial.Chebyshev.derivative_T_eval_one] using hbound

/-! ## Derivative comparison from root control -/


/-- Suppose a degree-at-most-`L` real polynomial has derivative bounded by
`T_L'` at every real zero of `T_L`.  At a point `x ∈ [-1,1]`, if the complex
modulus of `T_L` on the vertical line through `x` is dominated by the vertical
line through `1`, then the polynomial's derivative at `x` is bounded by
`|T_L'(1)|`. [the stated inputs](hyp:L,hL,Q,hQ,hroots,x,hx,hvertical) establish [the stated conclusion](goal). -/
theorem abs_eval_derivative_le_chebyshev_endpoint_of_root_control
    {L : ℕ} (hL : 0 < L) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ L)
    (hroots : ∀ z : ℝ,
      (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval z = 0 →
        |Q.derivative.eval z| ≤
          |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval z|)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1)
    (hvertical : ∀ y : ℝ,
      ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
          ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
          ((1 : ℂ) + (y : ℂ) * Complex.I)‖) :
    |Q.derivative.eval x| ≤
      |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval 1| := by
  obtain ⟨R, hRdeg, hRvertical, hQderiv⟩ :=
    exists_chebyshevRootReflection hL Q hQ hroots x
  refine hQderiv.trans (norm_eval_derivative_zero_le_chebyshev_endpoint_of_vertical
    hL R hRdeg ?_)
  intro y
  rw [hRvertical y]
  exact hvertical y

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
