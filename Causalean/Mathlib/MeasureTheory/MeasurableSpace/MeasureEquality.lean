/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.PiSystem

/-! # Measurability of measure equality

This file proves that the pointwise agreement set of two measurable measure-valued maps is
measurable when the target space is countably generated and the first family is finite.
-/

public section

namespace Causalean.Mathlib.MeasureTheory.MeasurableSpace

/-- For [measurable spaces](hyp:γ,β), [measure-valued maps `f` and `g`](hyp:f,g),
[their measurability](hyp:hf,hg), and [finiteness of every `f p`](hyp:hf_fin),
[their agreement set is measurable](goal). -/
theorem measurableSet_measure_eq
    {γ β : Type*} [MeasurableSpace γ] [MeasurableSpace β]
    [MeasurableSpace.CountablyGenerated β]
    {f g : γ → MeasureTheory.Measure β}
    (hf : Measurable f) (hg : Measurable g)
    (hf_fin : ∀ p, MeasureTheory.IsFiniteMeasure (f p)) :
    MeasurableSet {p | f p = g p} := by
  classical
  set C₀ : Set (Set β) :=
    MeasurableSpace.countableGeneratingSet β ∪ {Set.univ} with hC₀
  have hC₀_count : C₀.Countable :=
    MeasurableSpace.countable_countableGeneratingSet.union (Set.countable_singleton _)
  set C : Set (Set β) := generatePiSystem C₀ with hC
  have hC_count : C.Countable := by
    have hsub : generatePiSystem C₀ ⊆
        (fun F : Finset (Set β) => ⋂₀ (F : Set (Set β))) ''
          {F : Finset (Set β) | ↑F ⊆ C₀} := by
      intro t ht
      induction ht with
      | base h_s => exact ⟨{_}, by simpa using h_s, by simp⟩
      | inter _ _ _ ihs ihu =>
          obtain ⟨Fs, hFs, rfl⟩ := ihs
          obtain ⟨Fu, hFu, rfl⟩ := ihu
          refine ⟨Fs ∪ Fu, ?_, ?_⟩
          · simp only [Set.mem_setOf_eq, Finset.coe_union, Set.union_subset_iff]
            exact ⟨hFs, hFu⟩
          · simp [Set.sInter_union]
    refine Set.Countable.mono hsub (Set.Countable.image ?_ _)
    haveI : Countable C₀ := hC₀_count.to_subtype
    have hr : {F : Finset (Set β) | ↑F ⊆ C₀} ⊆
        Set.range (fun (G : Finset C₀) => G.map (Function.Embedding.subtype _)) := by
      intro F hF
      refine ⟨F.subtype (· ∈ C₀), ?_⟩
      ext x
      simp only [Finset.mem_map, Finset.mem_subtype, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hx; exact ⟨⟨x, hF hx⟩, by simpa using hx, rfl⟩
    exact Set.Countable.mono hr (Set.countable_range _)
  have hC_pi : IsPiSystem C := isPiSystem_generatePiSystem _
  have hC_meas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    refine generatePiSystem_measurableSet ?_ s hs
    intro t ht
    rcases ht with ht | ht
    · exact MeasurableSpace.measurableSet_countableGeneratingSet ht
    · rw [Set.mem_singleton_iff] at ht; exact ht ▸ MeasurableSet.univ
  have hUniv_C : Set.univ ∈ C :=
    subset_generatePiSystem_self _ (Or.inr rfl)
  have hgenC : (inferInstance : MeasurableSpace β) = MeasurableSpace.generateFrom C := by
    rw [hC, generateFrom_generatePiSystem_eq, hC₀,
      ← MeasurableSpace.generateFrom_sup_generateFrom,
      MeasurableSpace.generateFrom_countableGeneratingSet]
    have h1 : MeasurableSpace.generateFrom ({Set.univ} : Set (Set β)) = ⊥ :=
      MeasurableSpace.generateFrom_singleton_univ
    rw [h1, sup_bot_eq]
  have hset : {p | f p = g p} = ⋂ s ∈ C, {p | f p s = g p s} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hp s _; rw [hp]
    · intro hp
      haveI := hf_fin p
      refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion C
        (fun _ => Set.univ) hgenC hC_pi ?_ (fun _ => hUniv_C) ?_ ?_
      · rw [Set.iUnion_const]
      · intro _; exact MeasureTheory.measure_ne_top (f p) _
      · intro s hs; exact hp s hs
  rw [hset]
  refine MeasurableSet.biInter hC_count (fun s hs => ?_)
  have hfs : Measurable (fun p => f p s) :=
    (MeasureTheory.Measure.measurable_coe (hC_meas s hs)).comp hf
  have hgs : Measurable (fun p => g p s) :=
    (MeasureTheory.Measure.measurable_coe (hC_meas s hs)).comp hg
  exact measurableSet_eq_fun hfs hgs

end Causalean.Mathlib.MeasureTheory.MeasurableSpace
