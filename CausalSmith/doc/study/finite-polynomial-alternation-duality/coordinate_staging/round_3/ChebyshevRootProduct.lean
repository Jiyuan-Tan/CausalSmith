/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.ChebyshevChordGeometry

/-!
# Root-product form of the Chebyshev vertical comparison

This module isolates the two finite-product facts behind the complex
vertical-line modulus bound for Chebyshev polynomials: the explicit product
factorization over the cosine roots, and the Duffin--Schaeffer rearrangement
inequality for that product.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality


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

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
