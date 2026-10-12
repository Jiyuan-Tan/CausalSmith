/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Orthogonality of subset products under finite product measures

This file evaluates cross-moments of subset products built from centered coordinate functions.
The coordinate spaces, laws, functions, and second moments may all vary by coordinate.
-/

public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Causalean.Mathlib.MeasureTheory

/-- Given [a finite coordinate type](hyp:ι), [measurable coordinate spaces](hyp:Ω),
[probability measures on those spaces](hyp:μ), [real coordinate functions](hyp:w),
[zero first moments](hyp:hzero), [specified coordinate second moments](hyp:γ), and
[the corresponding second-moment identities](hyp:hsecond), for [two finite coordinate
subsets](hyp:S,T), [the cross-moment of their products vanishes unless the subsets agree, in
which case it is the product of their coordinate second moments](goal). -/
theorem subset_product_integral_orthogonality
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (w : ∀ i, Ω i → ℝ) (hzero : ∀ i, ∫ x, w i x ∂μ i = 0)
    (γ : ι → ℝ) (hsecond : ∀ i, ∫ x, w i x ^ 2 ∂μ i = γ i)
    (S T : Finset ι) :
    (∫ x : ∀ i, Ω i, (∏ i ∈ S, w i (x i)) * (∏ i ∈ T, w i (x i))
      ∂Measure.pi μ) = if S = T then ∏ i ∈ S, γ i else 0 := by
  have hprod (x : ∀ i, Ω i) :
      (∏ i ∈ S, w i (x i)) * (∏ i ∈ T, w i (x i)) =
      ∏ i : ι, (if i ∈ S then w i (x i) else 1) *
        (if i ∈ T then w i (x i) else 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod
    (fun i x => (if i ∈ S then w i x else 1) * (if i ∈ T then w i x else 1))]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl]
    have hfactor (i : ι) :
        (∫ x, (if i ∈ S then w i x else 1) * (if i ∈ S then w i x else 1) ∂μ i) =
        if i ∈ S then γ i else 1 := by
      by_cases hi : i ∈ S
      · simp only [hi, ↓reduceIte, ← sq]
        exact hsecond i
      · simp [hi]
    simp_rw [hfactor]
    rw [Finset.prod_ite_mem_eq]
  · rw [if_neg hST]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra h
      apply hST
      ext i
      exact not_not.mp (not_exists.mp h i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T
    · exact False.elim (hi (by simp [hS, hT]))
    · simpa only [hS, hT, ↓reduceIte, mul_one] using hzero i
    · simpa only [hS, hT, ↓reduceIte, one_mul] using hzero i
    · exact False.elim (hi (by simp [hS, hT]))

end Causalean.Mathlib.MeasureTheory
