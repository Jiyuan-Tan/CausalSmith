/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.CondIndep.PositiveDensityIntersection.Main

/-!
# Positive-density intersection for finite coordinate blocks

This module specializes graphoid intersection to coordinate projections on the union of four
finite index blocks.  All six pairwise-disjointness facts are explicit hypotheses; in particular,
the API cannot be applied to overlap degeneracies in which a conditioned coordinate is repeated
inside another block.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.CondIndep.PositiveDensityIntersection

universe uM uΩ

open Causalean

private theorem map_withDensity_comp_of_measurePreservingEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) {μ : Measure α} {ν : Measure β}
    (he : MeasurePreserving e μ ν) (d : β → ℝ≥0∞) (hd : Measurable d) :
    (μ.withDensity (d ∘ e)).map e = ν.withDensity d := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  have h := he.lintegral_comp (hd.indicator hs)
  convert h using 1 <;> rfl

private theorem condIndepFun_of_map
    {α β γ δ ε : Type*}
    [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [StandardBorelSpace β]
    [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    [MeasurableSpace ε]
    {φ : α → β} (hφ : Measurable φ)
    {X : β → γ} (hX : Measurable X) {Y : β → δ} (hY : Measurable Y)
    {Z : β → ε} (hZ : Measurable Z)
    {ν : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure (ν.map φ)]
    (h : CondIndepFun
      (MeasurableSpace.comap (Z ∘ φ) inferInstance)
      (hZ.comp hφ).comap_le (X ∘ φ) (Y ∘ φ) ν) :
    CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y (ν.map φ) := by
  have hcd1 : condDistrib (Y ∘ φ) (Z ∘ φ) ν = condDistrib Y Z (ν.map φ) := by
    simp only [condDistrib]
    congr 1
    exact (Measure.map_map (hZ.prodMk hY) hφ).symm
  have hcd2 : condDistrib (Y ∘ φ) (fun ω ↦ ((Z ∘ φ) ω, (X ∘ φ) ω)) ν =
      condDistrib Y (fun b ↦ (Z b, X b)) (ν.map φ) := by
    simp only [condDistrib]
    congr 1
    exact (Measure.map_map ((hZ.prodMk hX).prodMk hY) hφ).symm
  have hfilt : ν.map (fun ω ↦ ((Z ∘ φ) ω, (X ∘ φ) ω)) =
      (ν.map φ).map (fun b ↦ (Z b, X b)) :=
    (Measure.map_map (hZ.prodMk hX) hφ).symm
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ]
  have h' := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    (hY.comp hφ) (hX.comp hφ) (hZ.comp hφ)).mp h
  rw [hcd2, hcd1, hfilt] at h'
  exact h'

private theorem condIndepFun_measurableEquiv_iff
    {α β γ δ ε : Type*}
    [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [StandardBorelSpace β]
    [MeasurableSpace γ] [StandardBorelSpace γ]
    [MeasurableSpace δ] [StandardBorelSpace δ]
    [MeasurableSpace ε]
    (e : α ≃ᵐ β) {ν : Measure α} {μ : Measure β}
    [IsFiniteMeasure ν] [IsFiniteMeasure μ] (he : ν.map e = μ)
    {X : β → γ} (hX : Measurable X) {Y : β → δ} (hY : Measurable Y)
    {Z : β → ε} (hZ : Measurable Z) :
    CondIndepFun
        (MeasurableSpace.comap (Z ∘ e) inferInstance)
        (hZ.comp e.measurable).comap_le (X ∘ e) (Y ∘ e) ν ↔
      CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ := by
  cases isEmpty_or_nonempty γ with
  | inl hγ =>
      letI := hγ
      have hs : CondIndepFun
          (MeasurableSpace.comap (Z ∘ e) inferInstance)
          (hZ.comp e.measurable).comap_le (X ∘ e) (Y ∘ e) ν := by
        rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
          (hX.comp e.measurable) (hY.comp e.measurable)]
        intro s t hs ht
        exact ae_of_all _ fun a ↦ isEmptyElim (X (e a))
      have ht : CondIndepFun
          (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ := by
        rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY]
        intro s t hs ht
        exact ae_of_all _ fun b ↦ isEmptyElim (X b)
      exact ⟨fun _ ↦ ht, fun _ ↦ hs⟩
  | inr hγ =>
      letI := hγ
      cases isEmpty_or_nonempty δ with
      | inl hδ =>
          letI := hδ
          have hs : CondIndepFun
              (MeasurableSpace.comap (Z ∘ e) inferInstance)
              (hZ.comp e.measurable).comap_le (X ∘ e) (Y ∘ e) ν := by
            rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
              (hX.comp e.measurable) (hY.comp e.measurable)]
            intro s t hs ht
            exact ae_of_all _ fun a ↦ isEmptyElim (Y (e a))
          have ht : CondIndepFun
              (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ := by
            rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY]
            intro s t hs ht
            exact ae_of_all _ fun b ↦ isEmptyElim (Y b)
          exact ⟨fun _ ↦ ht, fun _ ↦ hs⟩
      | inr hδ =>
          letI := hδ
          constructor
          · intro h
            simpa only [he] using condIndepFun_of_map e.measurable hX hY hZ h
          · intro h
            have he' : μ.map e.symm = ν := by
              rw [← he, Measure.map_map e.symm.measurable e.measurable]
              simpa using congrArg (fun f ↦ Measure.map f ν) e.symm_comp_self
            have h0 : CondIndepFun
                (MeasurableSpace.comap ((Z ∘ e) ∘ e.symm) inferInstance)
                ((hZ.comp e.measurable).comp e.symm.measurable).comap_le
                ((X ∘ e) ∘ e.symm) ((Y ∘ e) ∘ e.symm) μ := by
              simpa only [Function.comp_def, e.apply_symm_apply] using h
            have h' := condIndepFun_of_map e.symm.measurable
              (hX.comp e.measurable) (hY.comp e.measurable) (hZ.comp e.measurable) h0
            simpa only [he'] using h'

private theorem comap_measurableEquiv_comp
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (f : γ → α) :
    MeasurableSpace.comap (e ∘ f) inferInstance =
      MeasurableSpace.comap f inferInstance := by
  rw [← MeasurableSpace.comap_comp, e.measurableEmbedding.comap_eq]

private theorem valuesEquivOfEq_apply
    {M : Type*} {Ω : M → Type*} [∀ i, MeasurableSpace (Ω i)]
    {A B : Finset M} (h : A = B) (x : ValuesOn A Ω)
    (i : M) (hi : i ∈ A) (hi' : i ∈ B) :
    valuesEquivOfEq h x ⟨i, hi'⟩ = x ⟨i, hi⟩ := by
  subst B
  rfl

private noncomputable def fourBlockValuesEquiv
    {M : Type uM} [DecidableEq M]
    {Ω : M → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (I J K L : Finset M)
    (hKL : Disjoint K L) (hJ_KL : Disjoint J (K ∪ L))
    (hI_JKL : Disjoint I (J ∪ (K ∪ L))) :
    FourBlock (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω) ≃ᵐ
      ValuesOn (fourBlockIndices I J K L) Ω := by
  let eKL := MeasurableEquiv.piFinsetUnion Ω hKL
  let eJKL :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ValuesOn J Ω)) eKL).trans
      (MeasurableEquiv.piFinsetUnion Ω hJ_KL)
  let e0 :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ValuesOn I Ω)) eJKL).trans
      (MeasurableEquiv.piFinsetUnion Ω hI_JKL)
  have hu : I ∪ (J ∪ (K ∪ L)) = fourBlockIndices I J K L := by
    simp only [fourBlockIndices, Finset.union_assoc]
  exact e0.trans (valuesEquivOfEq hu)

private theorem measurePreserving_fourBlockValuesEquiv
    {M : Type uM} [DecidableEq M]
    {Ω : M → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (I J K L : Finset M)
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hIL : Disjoint I L)
    (hJK : Disjoint J K) (hJL : Disjoint J L) (hKL : Disjoint K L)
    (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving
      (fourBlockValuesEquiv I J K L hKL
        (Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩)
        (Finset.disjoint_union_right.mpr
          ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩))
      (fourBlockReference
        (Measure.pi fun i : I ↦ μ i) (Measure.pi fun i : J ↦ μ i)
        (Measure.pi fun i : K ↦ μ i) (Measure.pi fun i : L ↦ μ i))
      (finiteBlockReference I J K L μ) := by
  have hJ_KL : Disjoint J (K ∪ L) :=
    Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩
  have hI_JKL : Disjoint I (J ∪ (K ∪ L)) :=
    Finset.disjoint_union_right.mpr
      ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩
  have hKL' := measurePreserving_piFinsetUnion hKL μ
  have hJKL := (measurePreserving_piFinsetUnion hJ_KL μ).comp
    ((MeasurePreserving.id (Measure.pi fun i : J ↦ μ i)).prod hKL')
  have h0 := (measurePreserving_piFinsetUnion hI_JKL μ).comp
    ((MeasurePreserving.id (Measure.pi fun i : I ↦ μ i)).prod hJKL)
  have hu : I ∪ (J ∪ (K ∪ L)) = fourBlockIndices I J K L := by
    simp only [fourBlockIndices, Finset.union_assoc]
  have hu' := measurePreserving_valuesEquivOfEq hu
    (fun i : {i // i ∈ I ∪ (J ∪ (K ∪ L))} ↦ μ i)
  change MeasurePreserving
    (fourBlockValuesEquiv I J K L hKL hJ_KL hI_JKL)
    (fourBlockReference
      (Measure.pi fun i : I ↦ μ i) (Measure.pi fun i : J ↦ μ i)
      (Measure.pi fun i : K ↦ μ i) (Measure.pi fun i : L ↦ μ i))
    (finiteBlockReference I J K L μ)
  convert hu'.comp h0 using 1 <;>
    rfl

/-- [Four finite coordinate blocks](hyp:I,J,K,L) with [all pairwise-disjointness
facts](hyp:hIJ,hIK,hIL,hJK,hJL,hKL),
[sigma-finite coordinate reference measures](hyp:μ), [a measurable density](hyp:hd), [strict
positivity almost everywhere](hyp:hpos), and [the two changing-conditioning projection
independence relations](hyp:hIJ_given_LK,hIK_given_LJ) [imply independence of the first block
from the joint second-and-third block given the fourth](goal). -/
theorem condIndep_valuesProjection_intersection_of_positiveDensity
    {M : Type uM} [DecidableEq M]
    {Ω : M → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    [∀ i, StandardBorelSpace (Ω i)]
    (I J K L : Finset M)
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hIL : Disjoint I L)
    (hJK : Disjoint J K) (hJL : Disjoint J L) (hKL : Disjoint K L)
    (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    {d : ValuesOn (fourBlockIndices I J K L) Ω → ℝ≥0∞}
    (hd : Measurable d)
    [IsFiniteMeasure ((finiteBlockReference I J K L μ).withDensity d)]
    (hpos : ∀ᵐ q ∂finiteBlockReference I J K L μ, 0 < d q)
    (hIJ_given_LK : CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (fourthThird_subset_fourBlock I J K L)) inferInstance)
      (comap_valuesProjection_le (fourthThird_subset_fourBlock I J K L))
      (valuesProjection (first_subset_fourBlock I J K L))
      (valuesProjection (second_subset_fourBlock I J K L))
      ((finiteBlockReference I J K L μ).withDensity d))
    (hIK_given_LJ : CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (fourthSecond_subset_fourBlock I J K L)) inferInstance)
      (comap_valuesProjection_le (fourthSecond_subset_fourBlock I J K L))
      (valuesProjection (first_subset_fourBlock I J K L))
      (valuesProjection (third_subset_fourBlock I J K L))
      ((finiteBlockReference I J K L μ).withDensity d)) :
    CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (fourth_subset_fourBlock I J K L)) inferInstance)
      (comap_valuesProjection_le (fourth_subset_fourBlock I J K L))
      (valuesProjection (first_subset_fourBlock I J K L))
      (valuesProjection (secondThird_subset_fourBlock I J K L))
      ((finiteBlockReference I J K L μ).withDensity d) := by
  let μI : Measure (ValuesOn I Ω) := Measure.pi fun i : I ↦ μ i
  let μJ : Measure (ValuesOn J Ω) := Measure.pi fun i : J ↦ μ i
  let μK : Measure (ValuesOn K Ω) := Measure.pi fun i : K ↦ μ i
  let μL : Measure (ValuesOn L Ω) := Measure.pi fun i : L ↦ μ i
  let e : FourBlock (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω) ≃ᵐ
      ValuesOn (fourBlockIndices I J K L) Ω :=
    fourBlockValuesEquiv I J K L hKL
      (Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩)
      (Finset.disjoint_union_right.mpr
        ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩)
  let ν := fourBlockReference μI μJ μK μL
  let d' : FourBlock (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω) →
      ℝ≥0∞ := d ∘ e
  have he : MeasurePreserving e ν (finiteBlockReference I J K L μ) := by
    simpa only [e, ν, μI, μJ, μK, μL] using
      measurePreserving_fourBlockValuesEquiv I J K L hIJ hIK hIL hJK hJL hKL μ
  have hd' : Measurable d' := hd.comp e.measurable
  have hlaw : (ν.withDensity d').map e =
      (finiteBlockReference I J K L μ).withDensity d := by
    simpa only [d'] using map_withDensity_comp_of_measurePreservingEquiv e he d hd
  have hlaw' : ((finiteBlockReference I J K L μ).withDensity d).map e.symm =
      ν.withDensity d' := by
    rw [← hlaw, Measure.map_map e.symm.measurable e.measurable]
    simpa using congrArg (fun f ↦ Measure.map f (ν.withDensity d')) e.symm_comp_self
  letI : IsFiniteMeasure (ν.withDensity d') := by
    rw [← hlaw']
    infer_instance
  have hpos' : ∀ᵐ q ∂ν, 0 < d' q := by
    rw [← he.map_eq, e.measurableEmbedding.ae_map_iff] at hpos
    simpa only [d', Function.comp_apply] using hpos

  have hJ_KL : Disjoint J (K ∪ L) :=
    Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩
  have hI_JKL : Disjoint I (J ∪ (K ∪ L)) :=
    Finset.disjoint_union_right.mpr
      ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩
  have hx : valuesProjection (first_subset_fourBlock I J K L) ∘ e =
      (@xCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω)) := by
    funext q
    ext i
    change valuesProjection (first_subset_fourBlock I J K L)
      (fourBlockValuesEquiv I J K L hKL hJ_KL hI_JKL q) i = q.1 i
    unfold fourBlockValuesEquiv
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr, valuesProjection]
    rw [valuesEquivOfEq_apply]
    change (Equiv.piFinsetUnion Ω hI_JKL)
      (q.1, (Equiv.piFinsetUnion Ω hJ_KL)
        (q.2.1, (Equiv.piFinsetUnion Ω hKL) (q.2.2.1, q.2.2.2)))
      ⟨i.val, Finset.mem_union_left _ i.property⟩ = q.1 i
    exact Equiv.piFinsetUnion_left Ω hI_JKL i.property _
  have hy : valuesProjection (second_subset_fourBlock I J K L) ∘ e =
      (@yCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω)) := by
    funext q
    ext i
    change valuesProjection (second_subset_fourBlock I J K L)
      (fourBlockValuesEquiv I J K L hKL hJ_KL hI_JKL q) i = q.2.1 i
    unfold fourBlockValuesEquiv
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr, valuesProjection]
    rw [valuesEquivOfEq_apply]
    change (Equiv.piFinsetUnion Ω hI_JKL)
      (q.1, (Equiv.piFinsetUnion Ω hJ_KL)
        (q.2.1, (Equiv.piFinsetUnion Ω hKL) (q.2.2.1, q.2.2.2)))
      ⟨i.val, Finset.mem_union_right I (Finset.mem_union_left _ i.property)⟩ = q.2.1 i
    calc
      _ = (Equiv.piFinsetUnion Ω hJ_KL)
          (q.2.1, (Equiv.piFinsetUnion Ω hKL) (q.2.2.1, q.2.2.2))
          ⟨i.val, Finset.mem_union_left _ i.property⟩ :=
        Equiv.piFinsetUnion_right Ω hI_JKL (Finset.mem_union_left _ i.property) _
      _ = q.2.1 i := Equiv.piFinsetUnion_left Ω hJ_KL i.property _
  have hv : valuesProjection (third_subset_fourBlock I J K L) ∘ e =
      (@vCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω)) := by
    funext q
    ext i
    change valuesProjection (third_subset_fourBlock I J K L)
      (fourBlockValuesEquiv I J K L hKL hJ_KL hI_JKL q) i = q.2.2.1 i
    unfold fourBlockValuesEquiv
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr, valuesProjection]
    rw [valuesEquivOfEq_apply]
    change (Equiv.piFinsetUnion Ω hI_JKL)
      (q.1, (Equiv.piFinsetUnion Ω hJ_KL)
        (q.2.1, (Equiv.piFinsetUnion Ω hKL) (q.2.2.1, q.2.2.2)))
      ⟨i.val, Finset.mem_union_right I
        (Finset.mem_union_right J (Finset.mem_union_left L i.property))⟩ = q.2.2.1 i
    calc
      _ = (Equiv.piFinsetUnion Ω hJ_KL)
          (q.2.1, (Equiv.piFinsetUnion Ω hKL) (q.2.2.1, q.2.2.2))
          ⟨i.val, Finset.mem_union_right J (Finset.mem_union_left L i.property)⟩ :=
        Equiv.piFinsetUnion_right Ω hI_JKL
          (Finset.mem_union_right J (Finset.mem_union_left L i.property)) _
      _ = (Equiv.piFinsetUnion Ω hKL) (q.2.2.1, q.2.2.2)
          ⟨i.val, Finset.mem_union_left L i.property⟩ :=
        Equiv.piFinsetUnion_right Ω hJ_KL (Finset.mem_union_left L i.property) _
      _ = q.2.2.1 i := Equiv.piFinsetUnion_left Ω hKL i.property _
  have hz : valuesProjection (fourth_subset_fourBlock I J K L) ∘ e =
      (@zCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω)) := by
    funext q
    ext i
    change valuesProjection (fourth_subset_fourBlock I J K L)
      (fourBlockValuesEquiv I J K L hKL hJ_KL hI_JKL q) i = q.2.2.2 i
    unfold fourBlockValuesEquiv
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr, valuesProjection]
    rw [valuesEquivOfEq_apply]
    change (Equiv.piFinsetUnion Ω hI_JKL)
      (q.1, (Equiv.piFinsetUnion Ω hJ_KL)
        (q.2.1, (Equiv.piFinsetUnion Ω hKL) (q.2.2.1, q.2.2.2)))
      ⟨i.val, Finset.mem_union_right I
        (Finset.mem_union_right J (Finset.mem_union_right K i.property))⟩ = q.2.2.2 i
    calc
      _ = (Equiv.piFinsetUnion Ω hJ_KL)
          (q.2.1, (Equiv.piFinsetUnion Ω hKL) (q.2.2.1, q.2.2.2))
          ⟨i.val, Finset.mem_union_right J (Finset.mem_union_right K i.property)⟩ :=
        Equiv.piFinsetUnion_right Ω hI_JKL
          (Finset.mem_union_right J (Finset.mem_union_right K i.property)) _
      _ = (Equiv.piFinsetUnion Ω hKL) (q.2.2.1, q.2.2.2)
          ⟨i.val, Finset.mem_union_right K i.property⟩ :=
        Equiv.piFinsetUnion_right Ω hJ_KL (Finset.mem_union_right K i.property) _
      _ = q.2.2.2 i := Equiv.piFinsetUnion_right Ω hKL i.property _

  let eLK : (ValuesOn L Ω × ValuesOn K Ω) ≃ᵐ ValuesOn (L ∪ K) Ω :=
    MeasurableEquiv.piFinsetUnion Ω hKL.symm
  let eLJ : (ValuesOn L Ω × ValuesOn J Ω) ≃ᵐ ValuesOn (L ∪ J) Ω :=
    MeasurableEquiv.piFinsetUnion Ω hJL.symm
  let eJK : (ValuesOn J Ω × ValuesOn K Ω) ≃ᵐ ValuesOn (J ∪ K) Ω :=
    MeasurableEquiv.piFinsetUnion Ω hJK
  have hLK : valuesProjection (fourthThird_subset_fourBlock I J K L) ∘ e =
      eLK ∘ (@zvCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω)) := by
    funext q
    ext i
    simp only [Function.comp_apply, zvCoord]
    by_cases hi : i.val ∈ L
    · have hr : eLK (q.2.2.2, q.2.2.1) i = q.2.2.2 ⟨i.val, hi⟩ := by
        change (Equiv.piFinsetUnion Ω hKL.symm) (q.2.2.2, q.2.2.1) i = _
        apply Equiv.piFinsetUnion_left Ω hKL.symm hi
      rw [hr]
      simpa only [valuesProjection, Function.comp_apply, zCoord] using
        congrFun (congrFun hz q) ⟨i.val, hi⟩
    · have hiK : i.val ∈ K := (Finset.mem_union.mp i.property).resolve_left hi
      have hr : eLK (q.2.2.2, q.2.2.1) i = q.2.2.1 ⟨i.val, hiK⟩ := by
        change (Equiv.piFinsetUnion Ω hKL.symm) (q.2.2.2, q.2.2.1) i = _
        apply Equiv.piFinsetUnion_right Ω hKL.symm hiK
      rw [hr]
      simpa only [valuesProjection, Function.comp_apply, vCoord] using
        congrFun (congrFun hv q) ⟨i.val, hiK⟩
  have hLJ : valuesProjection (fourthSecond_subset_fourBlock I J K L) ∘ e =
      eLJ ∘ (@zyCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω)) := by
    funext q
    ext i
    simp only [Function.comp_apply, zyCoord]
    by_cases hi : i.val ∈ L
    · have hr : eLJ (q.2.2.2, q.2.1) i = q.2.2.2 ⟨i.val, hi⟩ := by
        change (Equiv.piFinsetUnion Ω hJL.symm) (q.2.2.2, q.2.1) i = _
        apply Equiv.piFinsetUnion_left Ω hJL.symm hi
      rw [hr]
      simpa only [valuesProjection, Function.comp_apply, zCoord] using
        congrFun (congrFun hz q) ⟨i.val, hi⟩
    · have hiJ : i.val ∈ J := (Finset.mem_union.mp i.property).resolve_left hi
      have hr : eLJ (q.2.2.2, q.2.1) i = q.2.1 ⟨i.val, hiJ⟩ := by
        change (Equiv.piFinsetUnion Ω hJL.symm) (q.2.2.2, q.2.1) i = _
        apply Equiv.piFinsetUnion_right Ω hJL.symm hiJ
      rw [hr]
      simpa only [valuesProjection, Function.comp_apply, yCoord] using
        congrFun (congrFun hy q) ⟨i.val, hiJ⟩
  have hJK' : valuesProjection (secondThird_subset_fourBlock I J K L) ∘ e =
      eJK ∘ (@yvCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω)) := by
    funext q
    ext i
    simp only [Function.comp_apply, yvCoord]
    by_cases hi : i.val ∈ J
    · have hr : eJK (q.2.1, q.2.2.1) i = q.2.1 ⟨i.val, hi⟩ := by
        change (Equiv.piFinsetUnion Ω hJK) (q.2.1, q.2.2.1) i = _
        apply Equiv.piFinsetUnion_left Ω hJK hi
      rw [hr]
      simpa only [valuesProjection, Function.comp_apply, yCoord] using
        congrFun (congrFun hy q) ⟨i.val, hi⟩
    · have hiK : i.val ∈ K := (Finset.mem_union.mp i.property).resolve_left hi
      have hr : eJK (q.2.1, q.2.2.1) i = q.2.2.1 ⟨i.val, hiK⟩ := by
        change (Equiv.piFinsetUnion Ω hJK) (q.2.1, q.2.2.1) i = _
        apply Equiv.piFinsetUnion_right Ω hJK hiK
      rw [hr]
      simpa only [valuesProjection, Function.comp_apply, vCoord] using
        congrFun (congrFun hv q) ⟨i.val, hiK⟩

  have hXY : CondIndepFun
      (MeasurableSpace.comap
        (@zvCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω))
        inferInstance)
      measurable_zvCoord.comap_le
      (@xCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω))
      (@yCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω))
      (ν.withDensity d') := by
    have h := (condIndepFun_measurableEquiv_iff e hlaw
      (measurable_valuesProjection (first_subset_fourBlock I J K L))
      (measurable_valuesProjection (second_subset_fourBlock I J K L))
      (measurable_valuesProjection (fourthThird_subset_fourBlock I J K L))).2
      hIJ_given_LK
    simpa only [hx, hy, hLK, comap_measurableEquiv_comp] using h
  have hXV : CondIndepFun
      (MeasurableSpace.comap
        (@zyCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω))
        inferInstance)
      measurable_zyCoord.comap_le
      (@xCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω))
      (@vCoord (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω))
      (ν.withDensity d') := by
    have h := (condIndepFun_measurableEquiv_iff e hlaw
      (measurable_valuesProjection (first_subset_fourBlock I J K L))
      (measurable_valuesProjection (third_subset_fourBlock I J K L))
      (measurable_valuesProjection (fourthSecond_subset_fourBlock I J K L))).2
      hIK_given_LJ
    simpa only [hx, hv, hLJ, comap_measurableEquiv_comp] using h
  have hmain := condIndepFun_intersection_of_positiveDensity
    μI μJ μK μL hd' hpos' hXY hXV
  have hmain' := hmain.comp measurable_id eJK.measurable
  have hsource : CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (fourth_subset_fourBlock I J K L) ∘ e) inferInstance)
      ((measurable_valuesProjection (fourth_subset_fourBlock I J K L)).comp
        e.measurable).comap_le
      (valuesProjection (first_subset_fourBlock I J K L) ∘ e)
      (valuesProjection (secondThird_subset_fourBlock I J K L) ∘ e)
      (ν.withDensity d') := by
    simpa only [hx, hz, hJK', Function.id_comp] using hmain'
  exact (condIndepFun_measurableEquiv_iff e hlaw
    (measurable_valuesProjection (first_subset_fourBlock I J K L))
    (measurable_valuesProjection (secondThird_subset_fourBlock I J K L))
    (measurable_valuesProjection (fourth_subset_fourBlock I J K L))).1 hsource

/-- [Four finite coordinate blocks](hyp:I,J,K,L) with [all pairwise-disjointness
facts](hyp:hIJ,hIK,hIL,hJK,hJL,hKL), [sigma-finite coordinate reference measures](hyp:μ),
[a measurable strictly positive density](hyp:hd,hpos), and [the two changing-conditioning
projection independence relations](hyp:hIJ_given_LK,hIK_given_LJ)
[imply independence of the first and second blocks given the fourth](goal). -/
theorem condIndep_valuesProjection_decomposition_of_positiveDensity
    {M : Type uM} [DecidableEq M]
    {Ω : M → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    [∀ i, StandardBorelSpace (Ω i)]
    (I J K L : Finset M)
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hIL : Disjoint I L)
    (hJK : Disjoint J K) (hJL : Disjoint J L) (hKL : Disjoint K L)
    (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    {d : ValuesOn (fourBlockIndices I J K L) Ω → ℝ≥0∞}
    (hd : Measurable d)
    [IsFiniteMeasure ((finiteBlockReference I J K L μ).withDensity d)]
    (hpos : ∀ᵐ q ∂finiteBlockReference I J K L μ, 0 < d q)
    (hIJ_given_LK : CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (fourthThird_subset_fourBlock I J K L)) inferInstance)
      (comap_valuesProjection_le (fourthThird_subset_fourBlock I J K L))
      (valuesProjection (first_subset_fourBlock I J K L))
      (valuesProjection (second_subset_fourBlock I J K L))
      ((finiteBlockReference I J K L μ).withDensity d))
    (hIK_given_LJ : CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (fourthSecond_subset_fourBlock I J K L)) inferInstance)
      (comap_valuesProjection_le (fourthSecond_subset_fourBlock I J K L))
      (valuesProjection (first_subset_fourBlock I J K L))
      (valuesProjection (third_subset_fourBlock I J K L))
      ((finiteBlockReference I J K L μ).withDensity d)) :
    CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (fourth_subset_fourBlock I J K L)) inferInstance)
      (comap_valuesProjection_le (fourth_subset_fourBlock I J K L))
      (valuesProjection (first_subset_fourBlock I J K L))
      (valuesProjection (second_subset_fourBlock I J K L))
      ((finiteBlockReference I J K L μ).withDensity d) := by
  have h := condIndep_valuesProjection_intersection_of_positiveDensity
    I J K L hIJ hIK hIL hJK hJL hKL μ hd hpos hIJ_given_LK hIK_given_LJ
  convert h.comp measurable_id
    (measurable_valuesProjection (Ω' := Ω) Finset.subset_union_left) using 1 <;>
    rfl

end Causalean.Mathlib.CondIndep.PositiveDensityIntersection
