/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Null loci of real multivariate polynomials

This file proves that the zero locus of a nonzero real multivariate polynomial in finitely many
variables is Lebesgue-null.
-/

open MeasureTheory

namespace Causalean.Mathlib.MeasureTheory

/-- For [a real polynomial in finitely many numbered variables](hyp:P) that [is
nonzero](hyp:hP), [its zero locus has Lebesgue measure zero](goal). -/
lemma volume_mk_zeroLocus_mvPolynomial {d : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P ≠ 0) :
    volume {x : Fin d → ℝ | MvPolynomial.eval x P = 0} = 0 := by
  induction d with
  | zero =>
      have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x P = 0} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        apply hP
        apply MvPolynomial.funext
        intro y
        rw [Subsingleton.elim y x, hx]
        simp
      rw [hempty, measure_empty]
  | succ n ih =>
      let F : Polynomial (MvPolynomial (Fin n) ℝ) := MvPolynomial.finSuccEquiv ℝ n P
      have hF : F ≠ 0 := (MvPolynomial.finSuccEquiv ℝ n).injective.ne hP
      obtain ⟨i, hi⟩ : ∃ i, F.coeff i ≠ 0 := by
        simpa [Polynomial.ext_iff] using hF
      let Q : MvPolynomial (Fin n) ℝ := F.coeff i
      have hQ : Q ≠ 0 := hi
      have hQnull : volume {x : Fin n → ℝ | MvPolynomial.eval x Q = 0} = 0 := ih Q hQ
      let T : Set ((Fin n → ℝ) × ℝ) :=
        {z | MvPolynomial.eval (Fin.cons z.2 z.1) P = 0}
      have hTmeas : MeasurableSet T := by
        apply (measurableSet_singleton (0 : ℝ)).preimage
        have hc : Continuous (fun z : (Fin n → ℝ) × ℝ ↦
            @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) z.2 z.1) :=
          continuous_pi fun j ↦ Fin.cases
            (show Continuous (fun z : (Fin n → ℝ) × ℝ ↦ z.2) from continuous_snd)
            (fun k ↦ show Continuous (fun z : (Fin n → ℝ) × ℝ ↦ z.1 k) from
              (continuous_apply k).comp continuous_fst) j
        exact ((MvPolynomial.continuous_eval P).comp hc).measurable
      have hQae : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)), MvPolynomial.eval y Q ≠ 0 := by
        simpa only [Set.mem_setOf_eq] using measure_eq_zero_iff_ae_notMem.mp hQnull
      have hsections :
          (fun y : Fin n → ℝ ↦ volume (Prod.mk y ⁻¹' T)) =ᵐ[volume] 0 := by
        filter_upwards [hQae] with y hqy
        have hpoly : Polynomial.map (MvPolynomial.eval y) F ≠ 0 := by
          intro hz
          have hc := congrArg (fun R : Polynomial ℝ ↦ R.coeff i) hz
          simp only [Polynomial.coeff_zero, Polynomial.coeff_map] at hc
          exact hqy (by simpa [Q] using hc)
        have hfinite :
            Set.Finite {x : ℝ | (Polynomial.map (MvPolynomial.eval y) F).IsRoot x} :=
          Polynomial.finite_setOfPred_isRoot hpoly
        rw [show Prod.mk y ⁻¹' T =
            {x : ℝ | (Polynomial.map (MvPolynomial.eval y) F).IsRoot x} by
          ext x
          simp only [Set.mem_preimage, Set.mem_setOf_eq, Polynomial.IsRoot.def]
          rw [← MvPolynomial.eval_eq_eval_mv_eval']
          rfl]
        exact hfinite.measure_zero volume
      have hprodT :
          (volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ) T = 0 :=
        Measure.measure_prod_null_of_ae_null hTmeas hsections
      let S : Set (ℝ × (Fin n → ℝ)) :=
        {z | MvPolynomial.eval (Fin.cons z.1 z.2) P = 0}
      have hSmeas : MeasurableSet S := by
        apply (measurableSet_singleton (0 : ℝ)).preimage
        have hc : Continuous (fun z : ℝ × (Fin n → ℝ) ↦
            @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) z.1 z.2) :=
          continuous_pi fun j ↦ Fin.cases
            (show Continuous (fun z : ℝ × (Fin n → ℝ) ↦ z.1) from continuous_fst)
            (fun k ↦ show Continuous (fun z : ℝ × (Fin n → ℝ) ↦ z.2 k) from
              (continuous_apply k).comp continuous_snd) j
        exact ((MvPolynomial.continuous_eval P).comp hc).measurable
      have hprodS :
          (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) S = 0 := by
        rw [← Measure.prod_swap, Measure.map_apply measurable_swap hSmeas]
        simpa [T, S] using hprodT
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
      have he : MeasurePreserving e :=
        volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
      have hpre : e ⁻¹' S = {x : Fin (n + 1) → ℝ | MvPolynomial.eval x P = 0} := by
        ext x
        simp [e, S]
      rw [← hpre, ← Measure.map_apply he.measurable hSmeas, he.map_eq]
      exact hprodS

/-- For [a real polynomial indexed by an arbitrary finite variable type](hyp:P) that [is
nonzero](hyp:hP), [its zero locus has Lebesgue measure zero](goal). -/
lemma volume_zeroLocus_mvPolynomial_finite {α : Type*} [Fintype α]
    (P : MvPolynomial α ℝ) (hP : P ≠ 0) :
    volume {x : α → ℝ | MvPolynomial.eval x P = 0} = 0 := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let Q : MvPolynomial (Fin (Fintype.card α)) ℝ := MvPolynomial.rename e P
  have hQ : Q ≠ 0 := (MvPolynomial.renameEquiv ℝ e).injective.ne hP
  let S : Set (Fin (Fintype.card α) → ℝ) :=
    {y | MvPolynomial.eval y Q = 0}
  have hS : volume S = 0 := volume_mk_zeroLocus_mvPolynomial Q hQ
  have hSmeas : MeasurableSet S := by
    exact (MvPolynomial.continuous_eval Q).measurable (measurableSet_singleton 0)
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card α) ↦ ℝ) e
  have hφ : MeasurePreserving φ := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (Fintype.card α) ↦ ℝ) e
  have hpre : φ ⁻¹' S = {x : α → ℝ | MvPolynomial.eval x P = 0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    change MvPolynomial.eval (φ x) Q = 0 ↔ MvPolynomial.eval x P = 0
    rw [show Q = MvPolynomial.rename e P by rfl, MvPolynomial.eval_rename]
    have hx : (φ x) ∘ e = x := by
      funext i
      simp only [Function.comp_apply]
      rw [show φ = MeasurableEquiv.piCongrLeft
        (fun _ : Fin (Fintype.card α) ↦ ℝ) e by rfl]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rw [hx]
  rw [← hpre, ← Measure.map_apply hφ.measurable hSmeas, hφ.map_eq]
  exact hS

open scoped BigOperators

variable {σ κ : Type*}

/-- For [a real multivariate polynomial](hyp:p), its [real zero locus](goal) is the set of real
assignments at which the polynomial evaluates to zero. -/
def mvPolynomialZeroLocus (p : MvPolynomial σ ℝ) : Set (σ → ℝ) :=
  {x | MvPolynomial.eval x p = 0}

/-- For [a finite set of polynomial indices](hyp:s) and [an indexed family of real multivariate
polynomials](hyp:p), the [zero locus of their product equals the union of their zero loci](goal). -/
theorem mvPolynomialZeroLocus_finset_prod
    (s : Finset κ) (p : κ → MvPolynomial σ ℝ) :
    mvPolynomialZeroLocus (∏ i ∈ s, p i) =
      ⋃ i ∈ s, mvPolynomialZeroLocus (p i) := by
  ext x
  simp only [mvPolynomialZeroLocus, Set.mem_ofPred_eq, MvPolynomial.eval_prod,
    Finset.prod_eq_zero_iff]
  simp

/-- If [every factor in a finite indexed family of real multivariate polynomials is nonzero](hyp:h),
then [their finite product is nonzero](goal). -/
theorem mvPolynomial_finset_prod_ne_zero
    (s : Finset κ) (p : κ → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, p i ≠ 0) :
    (∏ i ∈ s, p i) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr h

/-- For [a finite-type-indexed family of real multivariate polynomials](hyp:p), the [zero locus
of the product over all indices equals the union of all factor zero loci](goal). -/
theorem mvPolynomialZeroLocus_fintype_prod [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) :
    mvPolynomialZeroLocus (∏ i, p i) = ⋃ i, mvPolynomialZeroLocus (p i) := by
  simpa using mvPolynomialZeroLocus_finset_prod (Finset.univ) p

/-- If [every member of a finite-type-indexed family of real multivariate polynomials is
nonzero](hyp:h), then [the product over the whole index type is nonzero](goal). -/
theorem mvPolynomial_fintype_prod_ne_zero [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (h : ∀ i, p i ≠ 0) :
    (∏ i, p i) ≠ 0 := by
  apply mvPolynomial_finset_prod_ne_zero Finset.univ p
  simpa using h

/-- Given [a finite set of indices](hyp:s) and [a polynomial for every member of its finite
subtype](hyp:p), the [zero locus of the subtype product equals the union of the subtype-indexed
zero loci](goal). -/
theorem mvPolynomialZeroLocus_subtype_prod
    (s : Finset κ) (p : {i // i ∈ s} → MvPolynomial σ ℝ) :
    mvPolynomialZeroLocus (∏ i, p i) = ⋃ i, mvPolynomialZeroLocus (p i) := by
  exact mvPolynomialZeroLocus_fintype_prod p

/-- Given [a finite set of indices](hyp:s), [a polynomial for every member of its finite subtype](hyp:p),
and [a proof that every factor is nonzero](hyp:h), the [product of the subtype-indexed factors is
nonzero](goal). -/
theorem mvPolynomial_subtype_prod_ne_zero
    (s : Finset κ) (p : {i // i ∈ s} → MvPolynomial σ ℝ)
    (h : ∀ i, p i ≠ 0) :
    (∏ i, p i) ≠ 0 := by
  exact mvPolynomial_fintype_prod_ne_zero p h


end Causalean.Mathlib.MeasureTheory
