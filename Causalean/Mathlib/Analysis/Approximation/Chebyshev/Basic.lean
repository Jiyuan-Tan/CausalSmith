/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform polynomial approximation on compact intervals

This module defines the compact-interval uniform approximation problem and proves
that a continuous target admits a best real-polynomial approximant under a degree
bound.
-/

@[expose] public section

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-! ## Core approximation quantities -/


/-- The [interval supremum norm](goal) of [a real function](hyp:g) for [endpoints r and s](hyp:r,s)
is [the supremum of the function's absolute values over the closed interval from r to s](step:1).
-/
noncomputable def intervalSupNorm (g : ℝ → ℝ) (r s : ℝ) : ℝ :=
  sSup ((fun x => |g x|) '' Set.Icc r s)

/-- The [uniform approximation error](goal) of [a real polynomial](hyp:Q) against [a real target
function](hyp:f) for [endpoints r and s](hyp:r,s) is [the interval supremum norm of the target
minus the polynomial on the closed interval from r to s](step:1). -/
noncomputable def uniformApproxError
    (f : ℝ → ℝ) (r s : ℝ) (Q : Polynomial ℝ) : ℝ :=
  intervalSupNorm (fun x => f x - Q.eval x) r s

/-- The [best uniform approximation error](goal) of [a real target function](hyp:f) for [endpoints
r and s](hyp:r,s) and [a degree bound L](hyp:L) is [the infimum of the uniform approximation errors
over all real polynomials of degree at most L](step:1). -/
noncomputable def bestUniformApproxError
    (f : ℝ → ℝ) (r s : ℝ) (L : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ Q : Polynomial ℝ,
    Q.natDegree ≤ L ∧ e = uniformApproxError f r s Q}

/-- For [a function that is continuous on the closed interval from r to s](hyp:hg) with [r at most
s](hyp:hrs), [the interval supremum norm is at most a number C exactly when the function is at most
C in absolute value at every point of the interval](goal). -/
theorem intervalSupNorm_le_iff {g : ℝ → ℝ} {r s C : ℝ}
    (hg : ContinuousOn g (Set.Icc r s)) (hrs : r ≤ s) :
    intervalSupNorm g r s ≤ C ↔ ∀ x ∈ Set.Icc r s, |g x| ≤ C := by
  -- Proof plan: apply `IsCompact.exists_sSup_image_eq_and_ge` to `x ↦ |g x|`,
  -- then unfold the image in `intervalSupNorm`.
  unfold intervalSupNorm
  constructor
  · intro h x hx
    exact (le_csSup (isCompact_Icc.bddAbove_image hg.abs) ⟨x, hx, rfl⟩).trans h
  · intro h
    apply csSup_le
    · exact ⟨|g r|, ⟨r, ⟨le_rfl, hrs⟩, rfl⟩⟩
    · rintro y ⟨x, hx, rfl⟩
      exact h x hx

/-- For [any real polynomial](hyp:Q), [the uniform approximation error against any target function
on any interval is nonnegative](goal). -/
theorem uniformApproxError_nonneg {f : ℝ → ℝ} {r s : ℝ}
    (Q : Polynomial ℝ) :
    0 ≤ uniformApproxError f r s Q := by
  -- Proof plan: split on boundedness of the residual image.  In the bounded
  -- case compare the supremum with the residual at `r`; in the unbounded case
  -- use the convention for `sSup` of an unbounded real set.
  unfold uniformApproxError intervalSupNorm
  apply Real.sSup_nonneg
  rintro y ⟨x, hx, rfl⟩
  exact abs_nonneg _

/-! ## Existence of best approximants -/


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
/-- For [endpoints with r strictly less than s](hyp:hrs), [a target function continuous on the
closed interval between them](hyp:hf), and [any degree bound L](hyp:L), [there is a real polynomial
of degree at most L whose uniform approximation error equals the best uniform approximation error
for that degree bound](goal). -/
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
      exact uniformApproxError_nonneg u
    · exact ⟨p, hpdeg, rfl⟩

/-- For [a real polynomial of degree at most L](hyp:hQ), [the
best uniform approximation error for degree bound L is at most the uniform approximation error of
that polynomial](goal). -/
theorem bestUniformApproxError_le
    {f : ℝ → ℝ} {r s : ℝ}
    {L : ℕ} {Q : Polynomial ℝ} (hQ : Q.natDegree ≤ L) :
    bestUniformApproxError f r s L ≤ uniformApproxError f r s Q := by
  unfold bestUniformApproxError
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro e ⟨P, -, rfl⟩
    exact uniformApproxError_nonneg P
  · exact ⟨Q, hQ, rfl⟩

/-- For [endpoints with r strictly less than s](hyp:hrs), [a target function continuous on the
closed interval between them](hyp:hf), and [any degree bound L](hyp:L), [the best uniform
approximation error is nonnegative](goal). -/
theorem bestUniformApproxError_nonneg
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r < s)
    (hf : ContinuousOn f (Set.Icc r s)) (L : ℕ) :
    0 ≤ bestUniformApproxError f r s L := by
  obtain ⟨Q, -, hQ⟩ := exists_bestPolynomial hrs hf L
  rw [← hQ]
  exact uniformApproxError_nonneg Q

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
