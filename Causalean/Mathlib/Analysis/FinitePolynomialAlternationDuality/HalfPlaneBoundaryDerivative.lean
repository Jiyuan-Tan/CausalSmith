/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Half-plane derivative comparison against a shifted Chebyshev polynomial

This module isolates the analytic half-plane input in the first-derivative
Duffin--Schaeffer argument.  Boundary modulus domination on the imaginary axis
propagates to derivative domination at the origin because the shifted
Chebyshev denominator has all roots in the opposite half-plane.
-/

open Polynomial Set Filter Bornology
open Asymptotics
open scoped Topology

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

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

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
