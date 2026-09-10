/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Best uniform polynomial approximation of the absolute-value function

This module defines the degree-`K` best uniform approximation error for
`x ↦ |x|` on `[-1,1]` directly from real polynomials.  It also records the
order, attainment, and compact-interval characterizations used by the measure
duality and rate modules.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality

/-- The [unit interval](goal) is the closed set of real numbers from $-1$ through $1$, inclusive. -/
def unitInterval : Set ℝ := Set.Icc (-1) 1

/-- For [a real polynomial](hyp:p), [its uniform absolute-value approximation error](goal) is the supremum, over every real number in the closed interval from $-1$ through $1$, of the absolute difference between the polynomial's value and that number's absolute value.

The uniform error of a real polynomial when approximating `x ↦ |x|` on
`[-1,1]`. -/
noncomputable def uniformApproxErrorAbs (p : Polynomial ℝ) : ℝ :=
  sSup ((fun x : ℝ => abs (abs x - p.eval x)) '' unitInterval)

/-- For [a nonnegative integer degree bound](hyp:K), [the best uniform absolute-value approximation error](goal) is the infimum of the uniform errors of all real polynomials whose degree is at most that bound.

The best uniform error `E_K` for approximating `x ↦ |x|` on `[-1,1]` by
real polynomials of degree at most `K`. -/
noncomputable def bestUniformApproxErrorAbs (K : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ p : Polynomial ℝ,
    p.natDegree ≤ K ∧ e = uniformApproxErrorAbs p}

/-- For [a real polynomial](hyp:p), [its uniform absolute-value approximation error is the supremum of its pointwise residual on the unit interval](goal).

 The uniform error is the compact-interval supremum of the pointwise
absolute residual. -/
theorem uniformApproxErrorAbs_eq_sSup (p : Polynomial ℝ) :
    uniformApproxErrorAbs p =
      sSup ((fun x : ℝ => abs (abs x - p.eval x)) '' Set.Icc (-1) 1) := by
  rfl

/-- For [a real polynomial](hyp:p) and [a proposed error bound](hyp:e), [the bound holds exactly when it bounds every residual on the unit interval](goal).

 A number bounds the uniform approximation error exactly when it bounds
every pointwise residual on `[-1,1]`. -/
theorem uniformApproxErrorAbs_le_iff {p : Polynomial ℝ} {e : ℝ} :
    uniformApproxErrorAbs p ≤ e ↔
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, abs (abs x - p.eval x) ≤ e := by
  let f : ℝ → ℝ := fun x => abs (abs x - p.eval x)
  have hf : Continuous f := by fun_prop
  have hI : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
  have hIne : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨x, hx, hmax, hge⟩ :=
    hI.exists_sSup_image_eq_and_ge hIne hf.continuousOn
  constructor
  · intro h y hy
    exact (hge y hy).trans (hmax ▸ h)
  · intro h
    exact csSup_le (hIne.image f) (by
      rintro _ ⟨x, hx, rfl⟩
      exact h x hx)

/-- For [a polynomial degree limit](hyp:K), [the best absolute-value approximation error is the infimum over all admissible polynomial errors](goal).

 The best error has its intrinsic infimum formulation over all
degree-at-most-`K` real polynomials. -/
theorem bestUniformApproxErrorAbs_eq_sInf (K : ℕ) :
    bestUniformApproxErrorAbs K =
      sInf {e : ℝ | ∃ p : Polynomial ℝ,
        p.natDegree ≤ K ∧ e = uniformApproxErrorAbs p} := by
  rfl

/-- For [a polynomial degree limit](hyp:K), [the best approximation error cannot be negative](goal).

 The best degree-`K` approximation error is nonnegative. -/
theorem bestUniformApproxErrorAbs_nonneg (K : ℕ) :
    0 ≤ bestUniformApproxErrorAbs K := by
  rw [bestUniformApproxErrorAbs_eq_sInf]
  apply le_csInf
  · exact ⟨uniformApproxErrorAbs 0, 0, by simp⟩
  · rintro e ⟨p, -, rfl⟩
    have h := (uniformApproxErrorAbs_le_iff (p := p) (e := uniformApproxErrorAbs p)).mp
      (le_refl _) 0 (by norm_num)
    exact (abs_nonneg _).trans h

/-- For [two degree limits with the first no larger than the second](hyp:K,L,hKL), [allowing the larger degree cannot increase the best error](goal).

 Increasing the allowed polynomial degree cannot increase the best uniform
approximation error. -/
theorem bestUniformApproxErrorAbs_antitone {K L : ℕ} (hKL : K ≤ L) :
    bestUniformApproxErrorAbs L ≤ bestUniformApproxErrorAbs K := by
  rw [bestUniformApproxErrorAbs_eq_sInf, bestUniformApproxErrorAbs_eq_sInf]
  apply csInf_le_csInf
  · refine ⟨0, ?_⟩
    rintro e ⟨p, -, rfl⟩
    have h := (uniformApproxErrorAbs_le_iff (p := p) (e := uniformApproxErrorAbs p)).mp
      (le_refl _) 0 (by norm_num)
    exact (abs_nonneg _).trans h
  · exact ⟨uniformApproxErrorAbs 0, 0, by simp⟩
  · rintro e ⟨p, hp, rfl⟩
    exact ⟨p, hp.trans hKL, rfl⟩

private noncomputable instance : CompactSpace unitInterval :=
  isCompact_iff_compactSpace.mp isCompact_Icc

private noncomputable instance : Nonempty unitInterval :=
  ⟨⟨0, by norm_num [unitInterval]⟩⟩

private noncomputable def absOnUnitInterval : C(unitInterval, ℝ) :=
  ⟨fun x => abs (x : ℝ), by fun_prop⟩

private noncomputable def boundedPolynomialFunctions (K : ℕ) :
    Submodule ℝ C(unitInterval, ℝ) :=
  ((Polynomial.toContinuousMapOnAlgHom unitInterval).toLinearMap.domRestrict
    (Polynomial.degreeLT ℝ (K + 1))).range

private noncomputable instance degreeLTFiniteDimensional (K : ℕ) :
    FiniteDimensional ℝ (Polynomial.degreeLT ℝ (K + 1)) :=
  (Polynomial.degreeLT.basis ℝ (K + 1)).finiteDimensional_of_finite

private noncomputable instance boundedPolynomialFunctionsFiniteDimensional (K : ℕ) :
    FiniteDimensional ℝ (boundedPolynomialFunctions K) :=
  FiniteDimensional.of_surjective
    (((Polynomial.toContinuousMapOnAlgHom unitInterval).toLinearMap.domRestrict
      (Polynomial.degreeLT ℝ (K + 1))).rangeRestrict) (by
        intro q
        obtain ⟨p, hp⟩ := q.property
        exact ⟨p, Subtype.ext hp⟩)

private theorem uniformApproxErrorAbs_eq_norm (p : Polynomial ℝ) :
    uniformApproxErrorAbs p =
      ‖absOnUnitInterval - p.toContinuousMapOn unitInterval‖ := by
  apply le_antisymm
  · apply uniformApproxErrorAbs_le_iff.mpr
    intro x hx
    have hnorm := ContinuousMap.norm_coe_le_norm
      (absOnUnitInterval - p.toContinuousMapOn unitInterval)
      ⟨x, by simpa [unitInterval] using hx⟩
    change abs (abs x - p.eval x) ≤ _ at hnorm
    exact hnorm
  · apply (ContinuousMap.norm_le_of_nonempty _).mpr
    intro x
    change abs (abs (x : ℝ) - p.eval (x : ℝ)) ≤ uniformApproxErrorAbs p
    exact ((uniformApproxErrorAbs_le_iff (p := p) (e := uniformApproxErrorAbs p)).mp
      (le_refl _)) (x : ℝ) (by simpa [unitInterval] using x.property)

set_option maxHeartbeats 2000000 in
-- Typeclass reduction for the finite-dimensional polynomial-function subspace is expensive.
/-- For [a polynomial degree limit](hyp:K), [some admissible polynomial attains the best absolute-value approximation error](goal).

 A best degree-`K` approximating polynomial exists and attains the infimum
defining `bestUniformApproxErrorAbs K`. -/
theorem exists_bestPolynomialAbs (K : ℕ) :
    ∃ p : Polynomial ℝ,
      p.natDegree ≤ K ∧
      uniformApproxErrorAbs p = bestUniformApproxErrorAbs K := by
  let V := boundedPolynomialFunctions K
  let f := absOnUnitInterval
  let R : ℝ := 2 * ‖f‖ + 1
  let B : Set V := Metric.closedBall 0 R
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hBcompact : IsCompact B := by
    exact ProperSpace.isCompact_closedBall 0 R
  have hzero : (0 : V) ∈ B := by
    simp [B, hR]
  have hcontinuous : Continuous (fun q : V => ‖f - (q : C(unitInterval, ℝ))‖) := by
    fun_prop
  obtain ⟨q, hqB, hqmin⟩ :=
    hBcompact.exists_isMinOn ⟨0, hzero⟩ hcontinuous.continuousOn
  have hqzero : ‖f - (q : C(unitInterval, ℝ))‖ ≤ ‖f‖ := by
    simpa using hqmin hzero
  have hglobal (r : V) :
      ‖f - (q : C(unitInterval, ℝ))‖ ≤ ‖f - (r : C(unitInterval, ℝ))‖ := by
    by_cases hr : r ∈ B
    · exact hqmin hr
    · have hrnorm : R < ‖r‖ := by
        simpa [B, Metric.mem_closedBall, dist_zero_left, not_le] using hr
      have hdiff := norm_sub_norm_le (r : C(unitInterval, ℝ)) f
      have hlower : ‖f‖ ≤ ‖(r : C(unitInterval, ℝ)) - f‖ := by
        dsimp [R] at hrnorm
        change ‖(r : C(unitInterval, ℝ))‖ - ‖f‖ ≤
          ‖(r : C(unitInterval, ℝ)) - f‖ at hdiff
        linarith
      rw [norm_sub_rev] at hlower
      exact hqzero.trans hlower
  obtain ⟨p, hpq⟩ := q.property
  have hpDegreeLE : (p : Polynomial ℝ) ∈ Polynomial.degreeLE ℝ K := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    exact p.property
  have hpdeg : (p : Polynomial ℝ).natDegree ≤ K :=
    Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hpDegreeLE)
  have hpq' : (p : Polynomial ℝ).toContinuousMapOn unitInterval =
      (q : C(unitInterval, ℝ)) := hpq
  have hminpoly : ∀ r : Polynomial ℝ, r.natDegree ≤ K →
      uniformApproxErrorAbs p ≤ uniformApproxErrorAbs r := by
    intro r hr
    have hrDegreeLE : r ∈ Polynomial.degreeLE ℝ K :=
      Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp hr)
    have hrDegreeLT : r ∈ Polynomial.degreeLT ℝ (K + 1) := by
      rw [Polynomial.degreeLT_succ_eq_degreeLE]
      simpa [Nat.succ_eq_add_one] using hrDegreeLE
    let rv : V := ⟨r.toContinuousMapOn unitInterval, ⟨⟨r, hrDegreeLT⟩, rfl⟩⟩
    rw [uniformApproxErrorAbs_eq_norm, uniformApproxErrorAbs_eq_norm]
    simpa [f, hpq'] using hglobal rv
  refine ⟨p, hpdeg, le_antisymm ?_ ?_⟩
  · rw [bestUniformApproxErrorAbs_eq_sInf]
    apply le_csInf
    · exact ⟨uniformApproxErrorAbs 0, 0, by simp⟩
    · rintro e ⟨r, hr, rfl⟩
      exact hminpoly r hr
  · rw [bestUniformApproxErrorAbs_eq_sInf]
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro e ⟨r, -, rfl⟩
      have h := ((uniformApproxErrorAbs_le_iff
        (p := r) (e := uniformApproxErrorAbs r)).mp (le_refl _)) 0 (by norm_num)
      exact (abs_nonneg _).trans h
    · exact ⟨p, hpdeg, rfl⟩

/-- For [a polynomial degree limit](hyp:K), [some admissible polynomial bounds every absolute-value residual by the best error on the unit interval](goal).

 The best error is equivalently the least pointwise residual bound, and a
polynomial attaining that bound exists. -/
theorem exists_bestPolynomialAbs_interval (K : ℕ) :
    ∃ p : Polynomial ℝ,
      p.natDegree ≤ K ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        abs (abs x - p.eval x) ≤ bestUniformApproxErrorAbs K) := by
  obtain ⟨p, hp, herr⟩ := exists_bestPolynomialAbs K
  refine ⟨p, hp, ?_⟩
  exact (uniformApproxErrorAbs_le_iff (p := p)
    (e := bestUniformApproxErrorAbs K)).mp herr.le

private theorem coeff_comp_neg_X (p : Polynomial ℝ) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1 : ℝ) ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq, mul_add]
  | monomial j a =>
      rw [Polynomial.monomial_comp]
      rw [show (-X : Polynomial ℝ) ^ j = (-1 : ℝ) ^ j • X ^ j by
        rw [show (-X : Polynomial ℝ) = (-1 : ℝ) • X by simp, smul_pow]]
      by_cases h : j = n
      · subst j
        simp
      · have hn : n ≠ j := Ne.symm h
        simp [Polynomial.coeff_monomial, h, hn]

private noncomputable def evenPart (p : Polynomial ℝ) : Polynomial ℝ :=
  (2 : ℝ)⁻¹ • (p + p.comp (-X))

private theorem evenPart_natDegree_le {p : Polynomial ℝ} {m : ℕ}
    (hp : p.natDegree ≤ 2 * m + 1) :
    (evenPart p).natDegree ≤ 2 * m := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases htop : n ≤ 2 * m + 1
  · have hnEq : n = 2 * m + 1 := by omega
    subst n
    simp [evenPart, coeff_comp_neg_X, pow_add, pow_mul]
  · have hpzero : p.coeff n = 0 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.mp hp n (by omega)
    simp [evenPart, coeff_comp_neg_X, hpzero]

private theorem uniformApproxErrorAbs_evenPart_le (p : Polynomial ℝ) :
    uniformApproxErrorAbs (evenPart p) ≤ uniformApproxErrorAbs p := by
  apply uniformApproxErrorAbs_le_iff.mpr
  intro x hx
  have hnegx : -x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hxerr := ((uniformApproxErrorAbs_le_iff
    (p := p) (e := uniformApproxErrorAbs p)).mp (le_refl _)) x hx
  have hnegerr := ((uniformApproxErrorAbs_le_iff
    (p := p) (e := uniformApproxErrorAbs p)).mp (le_refl _)) (-x) hnegx
  have hadd := abs_add_le (abs x - p.eval x) (abs (-x) - p.eval (-x))
  have hsum : abs ((abs x - p.eval x) + (abs (-x) - p.eval (-x))) ≤
      2 * uniformApproxErrorAbs p := by
    calc
      _ ≤ abs (abs x - p.eval x) + abs (abs (-x) - p.eval (-x)) := hadd
      _ ≤ uniformApproxErrorAbs p + uniformApproxErrorAbs p := add_le_add hxerr hnegerr
      _ = 2 * uniformApproxErrorAbs p := by ring
  rw [show (evenPart p).eval x = (p.eval x + p.eval (-x)) / 2 by
    simp [evenPart, div_eq_mul_inv]
    ring]
  rw [show abs x - (p.eval x + p.eval (-x)) / 2 =
      ((abs x - p.eval x) + (abs (-x) - p.eval (-x))) / 2 by
    rw [abs_neg]
    ring]
  rw [abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
    simpa [abs_neg, mul_comm] using hsum)

private theorem bestUniformApproxErrorAbs_le_uniform {K : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree ≤ K) :
    bestUniformApproxErrorAbs K ≤ uniformApproxErrorAbs p := by
  rw [bestUniformApproxErrorAbs_eq_sInf]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro e ⟨q, -, rfl⟩
    have h := ((uniformApproxErrorAbs_le_iff
      (p := q) (e := uniformApproxErrorAbs q)).mp (le_refl _)) 0 (by norm_num)
    exact (abs_nonneg _).trans h
  · exact ⟨p, hp, rfl⟩

/-- For [a nonnegative integer](hyp:m), [allowing the odd degree 2m+1 gives the same best error as degree 2m](goal).

 Odd degree offers no advantage for approximating the even function
`x ↦ |x|`: the best errors in degrees `2m` and `2m+1` coincide. -/
theorem bestUniformApproxErrorAbs_two_mul_add_one (m : ℕ) :
    bestUniformApproxErrorAbs (2 * m + 1) =
      bestUniformApproxErrorAbs (2 * m) := by
  apply le_antisymm
  · exact bestUniformApproxErrorAbs_antitone (by omega)
  · obtain ⟨p, hp, herr⟩ := exists_bestPolynomialAbs (2 * m + 1)
    calc
      bestUniformApproxErrorAbs (2 * m) ≤ uniformApproxErrorAbs (evenPart p) :=
        bestUniformApproxErrorAbs_le_uniform (evenPart_natDegree_le hp)
      _ ≤ uniformApproxErrorAbs p := uniformApproxErrorAbs_evenPart_le p
      _ = bestUniformApproxErrorAbs (2 * m + 1) := herr

end Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality
