/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Support-local Radon--Nikodym transport

This module localizes the global measurable-embedding invariance theorem for canonical
Radon--Nikodym derivatives.  The maps need only be measurable and mutually inverse on measurable
sets carrying the two finite source measures.
-/

open Set Function MeasureTheory

noncomputable section

namespace Causalean.Mathlib.MeasureTheory

/-- A [map](hyp:f) and [a set](hyp:S) determine [the proposition that the map is measurable on
that set](goal), [by testing its restriction to the set's subtype](step:1). -/
def SupportMeasurableOn {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (S : Set X) : Prop :=
  Measurable (fun x : S ↦ f x)

/-- [A measurable support set](hyp:hS), [a measure concentrated on it](hyp:hfull), and [a map
measurable there](hyp:hf) give [a map that is almost-everywhere measurable for that
measure](goal). -/
theorem aemeasurable_of_supportMeasurableOn
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Nonempty Y]
    {m : Measure X} {S : Set X} {f : X → Y}
    (hS : MeasurableSet S) (hfull : m Sᶜ = 0) (hf : SupportMeasurableOn f S) :
    AEMeasurable f m := by
  obtain ⟨f', hf', hf'eq⟩ :=
    (MeasurableEmbedding.subtype_coe hS).exists_measurable_extend hf (fun _ ↦ inferInstance)
  refine hf'.aemeasurable.congr ?_
  filter_upwards [ae_iff.mpr hfull] with x hx
  exact congr_fun hf'eq ⟨x, hx⟩

/-- [Finite numerator and denominator measures](hyp:m,n) with [absolute continuity](hyp:hmn),
[measurable source and target supports](hyp:S,T,hS,hT), [concentration on the source support](hyp:hμS,hνS), and [forward and reverse maps measurable on their supports](hyp:f,g,hf,hg), whose
[images stay in the matching supports](hyp:hfT,hgS) and [are mutual inverses there](hyp:hgf,hfg),
give [a canonical Radon--Nikodym derivative preserved after the forward map](goal). -/
theorem rnDeriv_map_of_support_equiv
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m n : Measure X) [IsFiniteMeasure m] [IsFiniteMeasure n]
    (hmn : m ≪ n) (S : Set X) (T : Set Y)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμS : m Sᶜ = 0) (hνS : n Sᶜ = 0)
    (f : X → Y) (g : Y → X)
    (hf : SupportMeasurableOn f S) (hg : SupportMeasurableOn g T)
    (hfT : ∀ x ∈ S, f x ∈ T)
    (hgS : ∀ y ∈ T, g y ∈ S)
    (hgf : ∀ x ∈ S, g (f x) = x)
    (hfg : ∀ y ∈ T, f (g y) = y) :
    (fun x ↦ (m.map f).rnDeriv (n.map f) (f x)) =ᵐ[n] m.rnDeriv n := by
  by_cases hSne : S.Nonempty
  · letI : Nonempty Y := ⟨f hSne.some⟩
    let e : S ≃ᵐ T :=
      { toEquiv :=
          { toFun := fun x ↦ ⟨f x, hfT x x.2⟩
            invFun := fun y ↦ ⟨g y, hgS y y.2⟩
            left_inv := fun x ↦ Subtype.ext (hgf x x.2)
            right_inv := fun y ↦ Subtype.ext (hfg y y.2) }
        measurable_toFun := hf.subtype_mk
        measurable_invFun := hg.subtype_mk }
    let mS : Measure S := Measure.comap ((↑) : S → X) m
    let nS : Measure S := Measure.comap ((↑) : S → X) n
    have hmS_map : mS.map ((↑) : S → X) = m := by
      simp only [mS, map_comap_subtype_coe hS,
        Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμS)]
    have hnS_map : nS.map ((↑) : S → X) = n := by
      simp only [nS, map_comap_subtype_coe hS,
        Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hνS)]
    have hfm : AEMeasurable f m :=
      aemeasurable_of_supportMeasurableOn hS hμS hf
    have hfn : AEMeasurable f n :=
      aemeasurable_of_supportMeasurableOn hS hνS hf
    have hm_map : (mS.map e).map ((↑) : T → Y) = m.map f := by
      calc
        (mS.map e).map ((↑) : T → Y) =
            mS.map (((↑) : T → Y) ∘ e) :=
          Measure.map_map measurable_subtype_coe e.measurable
        _ = mS.map (f ∘ ((↑) : S → X)) := by rfl
        _ = (mS.map ((↑) : S → X)).map f := by
          symm
          apply AEMeasurable.map_map_of_aemeasurable
          · simpa only [hmS_map] using hfm
          · exact measurable_subtype_coe.aemeasurable
        _ = m.map f := by rw [hmS_map]
    have hn_map : (nS.map e).map ((↑) : T → Y) = n.map f := by
      calc
        (nS.map e).map ((↑) : T → Y) =
            nS.map (((↑) : T → Y) ∘ e) :=
          Measure.map_map measurable_subtype_coe e.measurable
        _ = nS.map (f ∘ ((↑) : S → X)) := by rfl
        _ = (nS.map ((↑) : S → X)).map f := by
          symm
          apply AEMeasurable.map_map_of_aemeasurable
          · simpa only [hnS_map] using hfn
          · exact measurable_subtype_coe.aemeasurable
        _ = n.map f := by rw [hnS_map]
    have hTtransport :=
      (MeasurableEmbedding.subtype_coe hT).rnDeriv_map (mS.map e) (nS.map e)
    rw [Filter.EventuallyEq, e.measurableEmbedding.ae_map_iff] at hTtransport
    have hStransport := e.measurableEmbedding.rnDeriv_map mS nS
    have hScoe := (MeasurableEmbedding.subtype_coe hS).rnDeriv_map mS nS
    have hsub := Filter.EventuallyEq.trans hTtransport
      (Filter.EventuallyEq.trans hStransport hScoe.symm)
    rw [hm_map, hn_map, hmS_map, hnS_map] at hsub
    have hlift :
        (fun x ↦ (m.map f).rnDeriv (n.map f) (f x)) =ᵐ[nS.map ((↑) : S → X)]
          m.rnDeriv n :=
      (MeasurableEmbedding.subtype_coe hS).ae_map_iff.mpr (by
        filter_upwards [hsub] with x hx
        simpa only [show ((e x : T) : Y) = f x by rfl] using hx)
    simpa only [hnS_map] using hlift
  · have hnzero : n = 0 := by
      simpa [not_nonempty_iff_eq_empty.mp hSne] using hνS
    rw [hnzero]
    rw [Filter.EventuallyEq, ae_zero]
    simp

/-- [Finite numerator and denominator measures](hyp:m,n) with [absolute continuity](hyp:hmn),
[measurable source and target supports](hyp:S,T,hS,hT), [concentration on the source support](hyp:hμS,hνS), and [forward and reverse maps measurable on their supports](hyp:f,g,hf,hg), whose
[images stay in the matching supports](hyp:hfT,hgS) and [are mutual inverses there](hyp:hgf,hfg),
give [an unchanged pushforward law for the real-valued canonical Radon--Nikodym ratio](goal). -/
theorem map_toReal_rnDeriv_eq_map_toReal_rnDeriv_map_of_support_equiv
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (m n : Measure X) [IsFiniteMeasure m] [IsFiniteMeasure n]
    (hmn : m ≪ n) (S : Set X) (T : Set Y)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμS : m Sᶜ = 0) (hνS : n Sᶜ = 0)
    (f : X → Y) (g : Y → X)
    (hf : SupportMeasurableOn f S) (hg : SupportMeasurableOn g T)
    (hfT : ∀ x ∈ S, f x ∈ T)
    (hgS : ∀ y ∈ T, g y ∈ S)
    (hgf : ∀ x ∈ S, g (f x) = x)
    (hfg : ∀ y ∈ T, f (g y) = y) :
    Measure.map (fun x ↦ (m.rnDeriv n x).toReal) n =
      Measure.map (fun y ↦ ((m.map f).rnDeriv (n.map f) y).toReal) (n.map f) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI := hX
      rw [Measure.eq_zero_of_isEmpty n]
      simp
  | inr hX =>
      letI := hX
      letI : Nonempty Y := ⟨f hX.some⟩
      have hfn : AEMeasurable f n :=
        aemeasurable_of_supportMeasurableOn hS hνS hf
      have hrn := rnDeriv_map_of_support_equiv m n hmn S T hS hT hμS hνS
        f g hf hg hfT hgS hgf hfg
      have hreal :
          (fun x ↦ ((m.map f).rnDeriv (n.map f) (f x)).toReal) =ᵐ[n]
            fun x ↦ (m.rnDeriv n x).toReal := by
        filter_upwards [hrn] with x hx
        exact congrArg ENNReal.toReal hx
      calc
        Measure.map (fun x ↦ (m.rnDeriv n x).toReal) n =
            Measure.map
              ((fun y ↦ ((m.map f).rnDeriv (n.map f) y).toReal) ∘ f) n :=
          Measure.map_congr hreal.symm
        _ = Measure.map (fun y ↦ ((m.map f).rnDeriv (n.map f) y).toReal)
            (n.map f) := by
          symm
          apply AEMeasurable.map_map_of_aemeasurable
          · exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.aemeasurable
          · exact hfn

end Causalean.Mathlib.MeasureTheory

