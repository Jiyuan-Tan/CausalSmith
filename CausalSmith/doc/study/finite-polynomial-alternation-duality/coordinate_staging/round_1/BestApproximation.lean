/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial

/-!
# Existence of best bounded-degree uniform approximants

This module realizes bounded-degree real polynomials as a finite-dimensional
subspace of continuous functions on a compact interval and records attainment
of the best uniform approximation error.
-/

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

private noncomputable def targetOnInterval
    (f : ℝ → ℝ) (r s : ℝ) (hf : ContinuousOn f (Set.Icc r s)) :
    C(Set.Icc r s, ℝ) :=
  ⟨fun x => f x, hf.domRestrict⟩

private noncomputable def boundedPolynomialFunctions (r s : ℝ) (L : ℕ) :
    Submodule ℝ C(Set.Icc r s, ℝ) :=
  ((Polynomial.toContinuousMapOnAlgHom (Set.Icc r s)).toLinearMap.domRestrict
    (Polynomial.degreeLT ℝ (L + 1))).range

private noncomputable instance degreeLTFiniteDimensional (L : ℕ) :
    FiniteDimensional ℝ (Polynomial.degreeLT ℝ (L + 1)) :=
  (Polynomial.degreeLT.basis ℝ (L + 1)).finiteDimensional_of_finite

private noncomputable instance boundedPolynomialFunctionsFiniteDimensional
    (r s : ℝ) (L : ℕ) :
    FiniteDimensional ℝ (boundedPolynomialFunctions r s L) :=
  FiniteDimensional.of_surjective
    (((Polynomial.toContinuousMapOnAlgHom (Set.Icc r s)).toLinearMap.domRestrict
      (Polynomial.degreeLT ℝ (L + 1))).rangeRestrict) (by
        intro q
        obtain ⟨p, hp⟩ := q.property
        exact ⟨p, Subtype.ext hp⟩)

private theorem uniformApproxError_eq_norm
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r ≤ s)
    (hf : ContinuousOn f (Set.Icc r s)) (p : Polynomial ℝ) :
    uniformApproxError f r s p =
      ‖targetOnInterval f r s hf - p.toContinuousMapOn (Set.Icc r s)‖ := by
  letI : CompactSpace (Set.Icc r s) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : Nonempty (Set.Icc r s) :=
    ⟨⟨r, left_mem_Icc.mpr hrs⟩⟩
  have hcontinuous : ContinuousOn (fun x => f x - p.eval x) (Set.Icc r s) :=
    hf.sub p.continuous.continuousOn
  apply le_antisymm
  · apply (intervalSupNorm_le_iff hcontinuous hrs).mpr
    intro x hx
    have hnorm := ContinuousMap.norm_coe_le_norm
      (targetOnInterval f r s hf - p.toContinuousMapOn (Set.Icc r s)) ⟨x, hx⟩
    change |f x - p.eval x| ≤ _ at hnorm
    exact hnorm
  · apply (ContinuousMap.norm_le_of_nonempty _).mpr
    intro x
    change |f (x : ℝ) - p.eval (x : ℝ)| ≤ uniformApproxError f r s p
    exact ((intervalSupNorm_le_iff hcontinuous hrs).mp
      (le_refl _)) (x : ℝ) x.property

set_option maxHeartbeats 2000000 in
-- Typeclass reduction for the finite-dimensional polynomial-function subspace is expensive.
/-- A continuous real target on a nondegenerate compact interval has a real
polynomial of degree at most `L` attaining the best uniform error. [the stated inputs](hyp:f,r,s,hrs,hf,L) establish [the stated conclusion](goal). -/
theorem exists_bestPolynomial
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r < s)
    (hf : ContinuousOn f (Set.Icc r s)) (L : ℕ) :
    ∃ Q : Polynomial ℝ,
      Q.natDegree ≤ L ∧
      uniformApproxError f r s Q = bestUniformApproxError f r s L := by
  letI : CompactSpace (Set.Icc r s) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : Nonempty (Set.Icc r s) :=
    ⟨⟨r, left_mem_Icc.mpr hrs.le⟩⟩
  let V := boundedPolynomialFunctions r s L
  let g := targetOnInterval f r s hf
  let R : ℝ := 2 * ‖g‖ + 1
  let B : Set V := Metric.closedBall 0 R
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hBcompact : IsCompact B := by
    exact ProperSpace.isCompact_closedBall 0 R
  have hzero : (0 : V) ∈ B := by
    simp [B, hR]
  have hcontinuous : Continuous (fun q : V => ‖g - (q : C(Set.Icc r s, ℝ))‖) := by
    fun_prop
  obtain ⟨q, hqB, hqmin⟩ :=
    hBcompact.exists_isMinOn ⟨0, hzero⟩ hcontinuous.continuousOn
  have hqzero : ‖g - (q : C(Set.Icc r s, ℝ))‖ ≤ ‖g‖ := by
    simpa using hqmin hzero
  have hglobal (u : V) :
      ‖g - (q : C(Set.Icc r s, ℝ))‖ ≤
        ‖g - (u : C(Set.Icc r s, ℝ))‖ := by
    by_cases hu : u ∈ B
    · exact hqmin hu
    · have hunorm : R < ‖u‖ := by
        simpa [B, Metric.mem_closedBall, dist_zero_left, not_le] using hu
      have hdiff := norm_sub_norm_le (u : C(Set.Icc r s, ℝ)) g
      have hlower : ‖g‖ ≤ ‖(u : C(Set.Icc r s, ℝ)) - g‖ := by
        dsimp [R] at hunorm
        change ‖(u : C(Set.Icc r s, ℝ))‖ - ‖g‖ ≤
          ‖(u : C(Set.Icc r s, ℝ)) - g‖ at hdiff
        linarith
      rw [norm_sub_rev] at hlower
      exact hqzero.trans hlower
  obtain ⟨p, hpq⟩ := q.property
  have hpDegreeLE : (p : Polynomial ℝ) ∈ Polynomial.degreeLE ℝ L := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    exact p.property
  have hpdeg : (p : Polynomial ℝ).natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hpDegreeLE)
  have hpq' : (p : Polynomial ℝ).toContinuousMapOn (Set.Icc r s) =
      (q : C(Set.Icc r s, ℝ)) := hpq
  have hminpoly : ∀ u : Polynomial ℝ, u.natDegree ≤ L →
      uniformApproxError f r s p ≤ uniformApproxError f r s u := by
    intro u hu
    have huDegreeLE : u ∈ Polynomial.degreeLE ℝ L :=
      Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp hu)
    have huDegreeLT : u ∈ Polynomial.degreeLT ℝ (L + 1) := by
      rw [Polynomial.degreeLT_succ_eq_degreeLE]
      simpa [Nat.succ_eq_add_one] using huDegreeLE
    let uv : V :=
      ⟨u.toContinuousMapOn (Set.Icc r s), ⟨⟨u, huDegreeLT⟩, rfl⟩⟩
    rw [uniformApproxError_eq_norm hrs.le hf,
      uniformApproxError_eq_norm hrs.le hf]
    simpa [g, hpq'] using hglobal uv
  refine ⟨p, hpdeg, le_antisymm ?_ ?_⟩
  · unfold bestUniformApproxError
    apply le_csInf
    · exact ⟨uniformApproxError f r s 0, 0, by simp⟩
    · rintro e ⟨u, hu, rfl⟩
      exact hminpoly u hu
  · unfold bestUniformApproxError
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro e ⟨u, -, rfl⟩
      exact uniformApproxError_nonneg hrs.le u
    · exact ⟨p, hpdeg, rfl⟩

/-- Every degree-at-most-`L` polynomial has uniform error at least the best
degree-`L` error. [the stated inputs](hyp:f,r,s,hrs,hf,L,Q,hQ) establish [the stated conclusion](goal). -/
theorem bestUniformApproxError_le
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r < s) (hf : ContinuousOn f (Set.Icc r s))
    {L : ℕ} {Q : Polynomial ℝ} (hQ : Q.natDegree ≤ L) :
    bestUniformApproxError f r s L ≤ uniformApproxError f r s Q := by
  unfold bestUniformApproxError
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro e ⟨P, -, rfl⟩
    exact uniformApproxError_nonneg hrs.le P
  · exact ⟨Q, hQ, rfl⟩

/-- For a continuous target on a nondegenerate interval, the best bounded-degree
uniform approximation error is nonnegative. [the stated inputs](hyp:f,r,s,hrs,hf,L) establish [the stated conclusion](goal). -/
theorem bestUniformApproxError_nonneg
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r < s)
    (hf : ContinuousOn f (Set.Icc r s)) (L : ℕ) :
    0 ≤ bestUniformApproxError f r s L := by
  obtain ⟨Q, -, hQ⟩ := exists_bestPolynomial hrs hf L
  rw [← hQ]
  exact uniformApproxError_nonneg hrs.le Q

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
