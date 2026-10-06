/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Measures carried by finitely many atoms

This file provides decomposition, pointwise recovery, and integrability facts for
finite measures concentrated on a finite family of measurable atoms.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Causalean.Mathlib.MeasureTheory

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Given [a probability measure on a finite measurable space](hyp:μ), [some
singleton has nonzero probability](goal). -/
lemma exists_singleton_ne_zero_of_probability_finite
    {Z : Type*} [MeasurableSpace Z] [Finite Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] : ∃ z : Z, μ {z} ≠ 0 := by
  letI := Fintype.ofFinite Z
  by_contra h
  push Not at h
  have hu : (Set.univ : Set Z) =
      ⋃ z ∈ (Finset.univ : Finset Z), ({z} : Set Z) := by
    ext z
    simp
  have hle := measure_biUnion_finset_le (μ := μ) (Finset.univ : Finset Z)
    (fun z ↦ ({z} : Set Z))
  rw [← hu] at hle
  simp [h] at hle

/-- Given [a finite subset of indices](hyp:A), [an indexed family of probability
measures](hyp:μ), [a dominating measure](hyp:ν), [absolute continuity on the
selected indices](hyp:hac), and [pairwise mutual singularity on distinct selected
indices](hyp:hsing), [the number of selected measures is at most the number of
singletons having nonzero mass under the dominating measure](goal). -/
lemma pairwise_singular_card_le_positive_atoms
    {I Z : Type*} [MeasurableSpace Z] [Finite Z]
    (A : Finset I) (μ : I → Measure Z)
    [∀ s, IsProbabilityMeasure (μ s)] (ν : Measure Z)
    (hac : ∀ s ∈ A, μ s ≪ ν)
    (hsing : ∀ s ∈ A, ∀ u ∈ A, s ≠ u → μ s ⟂ₘ μ u) :
    (A.card : ℕ∞) ≤ Set.encard {z : Z | ν {z} ≠ 0} := by
  classical
  let z : {s // s ∈ A} → Z := fun s ↦
    Classical.choose (exists_singleton_ne_zero_of_probability_finite (μ s))
  have hz (s : {s // s ∈ A}) : μ s {z s} ≠ 0 :=
    Classical.choose_spec (exists_singleton_ne_zero_of_probability_finite (μ s))
  have hzν (s : {s // s ∈ A}) : ν {z s} ≠ 0 := by
    intro hzero
    exact hz s (hac s s.property hzero)
  have hinj : Function.Injective z := by
    intro s u hzu
    by_contra hsu
    have hms := hsing s s.property u u.property (Subtype.coe_ne_coe.mpr hsu)
    by_cases hm : z s ∈ hms.nullSet
    · have hzero : μ s {z s} = 0 :=
        nonpos_iff_eq_zero.mp
          ((measure_mono (Set.singleton_subset_iff.mpr hm)).trans_eq
            hms.measure_nullSet)
      exact hz s hzero
    · have hmem : z u ∈ hms.nullSetᶜ := by simpa [hzu] using hm
      have hzero : μ u {z u} = 0 :=
        nonpos_iff_eq_zero.mp
          ((measure_mono (Set.singleton_subset_iff.mpr hmem)).trans_eq
            hms.measure_compl_nullSet)
      exact hz u hzero
  let B : Finset Z := A.attach.image z
  have hcard : B.card = A.card := by
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hsub : (B : Set Z) ⊆ {w : Z | ν {w} ≠ 0} := by
    intro w hw
    simp only [B, Finset.mem_coe, Finset.mem_image] at hw
    obtain ⟨s, _, rfl⟩ := hw
    exact hzν s
  rw [← hcard, ← Set.encard_coe_eq_coe_finsetCard]
  exact Set.encard_le_encard hsub

/-- Let `μ` be a finite measure and `cell` an injective family of finitely many points of the
sample space, indexed by a finite type `ι`. If [every singleton `{cell i}` is
measurable](hyp:hcell) and [`μ` assigns its full mass to the range of `cell`, i.e. `μ` puts no
mass outside these finitely many points](hyp:hrange), then [`μ` equals the sum, over the index
`i`, of the point mass `μ {cell i}` scaling the Dirac measure at `cell i`](goal). -/
lemma measure_eq_fin_sum_smul_dirac_of_range
    (μ : Measure 𝒳) [IsFiniteMeasure μ] {ι : Type*} [Fintype ι]
    (cell : ι ↪ 𝒳) (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : μ (Set.range cell) = μ Set.univ) :
    μ = ∑ i, μ {cell i} • Measure.dirac (cell i) := by
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hae : ∀ᵐ x ∂μ, x ∈ Set.range cell := by
    change Set.range cell ∈ ae μ
    rw [mem_ae_iff, measure_compl hrangeMeas (measure_ne_top μ _), hrange]
    simp
  ext A hA
  rw [← Measure.measure_inter_eq_of_ae hae]
  rw [show Set.range cell ∩ A = ⋃ i, ({cell i} ∩ A) by
    ext x
    constructor
    · rintro ⟨⟨i, hix⟩, hxA⟩
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨i, hix.symm, hxA⟩
    · intro hx
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff] at hx
      obtain ⟨i, hxi, hxA⟩ := hx
      exact ⟨⟨i, hxi.symm⟩, hxA⟩]
  rw [measure_iUnion]
  · simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hA, tsum_fintype]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hmem : cell i ∈ A
    · simp [hmem]
    · have hinter : {cell i} ∩ A = ∅ := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨rfl, hxA⟩
          exact (hmem hxA).elim
        · simp
      simp [hinter, hmem]
  · intro i j hij
    change Disjoint ({cell i} ∩ A) ({cell j} ∩ A)
    rw [Set.disjoint_left]
    intro x hxi hxj
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff] at hxi hxj
    exact hij ((cell.injective (hxi.1.symm.trans hxj.1)))
  · intro i
    exact (hcell i).inter hA

/-- An almost-sure property holds at every point to which the measure assigns nonzero mass. -/
lemma property_at_of_ae_of_singleton_pos
    (μ : Measure 𝒳) (p : 𝒳 → Prop) {x : 𝒳}
    (hp : ∀ᵐ y ∂μ, p y) (hx : μ {x} ≠ 0) :
    p x := by
  by_contra hpx
  have hnull : μ {y | ¬p y} = 0 := by
    change {y | p y} ∈ ae μ at hp
    rw [mem_ae_iff] at hp
    simpa only [Set.compl_setOf] using hp
  apply hx
  exact measure_mono_null (by simpa [Set.singleton_subset_iff]) hnull

/-- Every strongly measurable normed-vector-valued function is integrable under a finite measure
concentrated on finitely many measurable points. -/
lemma integrable_of_finite_atomic_support
    (μ : Measure 𝒳) [IsFiniteMeasure μ] {ι : Type*} [Finite ι]
    (cell : ι ↪ 𝒳) (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : μ (Set.range cell) = μ Set.univ) {E : Type*} [NormedAddCommGroup E]
    (f : 𝒳 → E)
    (hf : StronglyMeasurable f) :
    Integrable f μ := by
  letI := Fintype.ofFinite ι
  rw [measure_eq_fin_sum_smul_dirac_of_range μ cell hcell hrange]
  apply integrable_finset_sum_measure.2
  intro i hi
  exact
    (integrable_dirac' hf (by simp)).smul_measure
      (measure_ne_top μ {cell i})

end Causalean.Mathlib.MeasureTheory
