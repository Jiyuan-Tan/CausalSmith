/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.MeasureTheory.CondExpPreimage
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Conditional-expectation bounds and law transport

This file proves preservation of deterministic almost-everywhere bounds by conditional
expectation, a real-valued Doob--Dynkin factorization, and transport of almost-everywhere
properties, integrability, integrals, and a conditional-mean identity across equality of
pushforward measures.
-/

public section

open MeasureTheory

namespace Causalean.Mathlib.MeasureTheory

/-- If [the conditioning σ-algebra is contained in the ambient σ-algebra](hyp:hm) and [three
integrable real functions](hyp:ha,hf,hb) satisfy [almost-everywhere lower and upper
bounds](hyp:hlo,hhi), and [both bounding functions are measurable for the conditioning
σ-algebra](hyp:ha_meas,hb_meas), then [the conditional expectation satisfies the same
pointwise functional bounds almost everywhere](goal). -/
theorem condExp_ae_mem_Icc_of_stronglyMeasurable
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {a f b : Ω → ℝ}
    (ha : Integrable a μ) (hf : Integrable f μ) (hb : Integrable b μ)
    (ha_meas : StronglyMeasurable[m] a) (hb_meas : StronglyMeasurable[m] b)
    (hlo : a ≤ᵐ[μ] f) (hhi : f ≤ᵐ[μ] b) :
    ∀ᵐ ω ∂μ, a ω ≤ μ[f | m] ω ∧ μ[f | m] ω ≤ b ω := by
  have hlo' := condExp_mono (μ := μ) (m := m) ha hf hlo
  have hhi' := condExp_mono (μ := μ) (m := m) hf hb hhi
  rw [condExp_of_stronglyMeasurable hm ha_meas ha] at hlo'
  rw [condExp_of_stronglyMeasurable hm hb_meas hb] at hhi'
  filter_upwards [hlo', hhi'] with ω hωlo hωhi
  exact ⟨hωlo, hωhi⟩

/-- If [the conditioning σ-algebra is contained in the ambient σ-algebra](hyp:hm) and [an
integrable real function](hyp:hf) lies [between two constants almost everywhere](hyp:hlo,hhi),
then [its conditional expectation lies between the same constants
almost everywhere](goal). -/
theorem condExp_ae_mem_Icc
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {f : Ω → ℝ} {a b : ℝ}
    (hf : Integrable f μ)
    (hlo : (fun _ : Ω => a) ≤ᵐ[μ] f)
    (hhi : f ≤ᵐ[μ] (fun _ : Ω => b)) :
    ∀ᵐ ω ∂μ, a ≤ μ[f | m] ω ∧ μ[f | m] ω ≤ b := by
  have hlo' := condExp_mono (μ := μ) (m := m)
    (integrable_const a) hf hlo
  have hhi' := condExp_mono (μ := μ) (m := m)
    hf (integrable_const b) hhi
  rw [condExp_const hm] at hlo' hhi'
  filter_upwards [hlo', hhi'] with ω hωlo hωhi
  exact ⟨hωlo, hωhi⟩

/-- If [the conditioning σ-algebra is contained in the ambient σ-algebra](hyp:hm) and [an
integrable real function](hyp:hf) is bounded below by [a strictly positive
constant](hyp:hε,hlo), then [its conditional expectation is strictly positive almost
everywhere](goal). -/
theorem ae_pos_condExp_of_pos_const_le
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {f : Ω → ℝ} {ε : ℝ}
    (hf : Integrable f μ) (hε : 0 < ε)
    (hlo : (fun _ : Ω => ε) ≤ᵐ[μ] f) :
    ∀ᵐ ω ∂μ, 0 < μ[f | m] ω := by
  have hbound := condExp_mono (μ := μ) (m := m)
    (integrable_const ε) hf hlo
  rw [condExp_const hm] at hbound
  filter_upwards [hbound] with ω hω
  exact hε.trans_le hω

/-- A [real function strongly measurable for the pullback σ-algebra](hyp:hg) [factors
exactly through the generating map by a measurable real function](goal). -/
theorem exists_measurable_real_comp_of_stronglyMeasurable_comap
    {X Y : Type*} [mY : MeasurableSpace Y] {f : X → Y} {g : X → ℝ}
    (hg : @StronglyMeasurable X ℝ _ (MeasurableSpace.comap f mY) g) :
    ∃ h : Y → ℝ, Measurable h ∧ g = h ∘ f := by
  obtain ⟨h, hh, hcomp⟩ := hg.exists_eq_measurable_comp
  exact ⟨h, hh.measurable, hcomp⟩

/-- [A measurable predicate holds almost everywhere after either of two maps under exactly the
same conditions](goal) when [the maps are measurable](hyp:hφ,hψ), [the predicate and its truth
set are measurable](hyp:p,hp), and [their pushforward measures coincide](hyp:hmap). -/
theorem ae_comp_iff_of_map_eq
    {Ω Ω' R : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace R]
    {μ : Measure Ω} {ν : Measure Ω'} {φ : Ω → R} {ψ : Ω' → R}
    (hφ : Measurable φ) (hψ : Measurable ψ) (p : R → Prop)
    (hp : MeasurableSet {r | p r}) (hmap : μ.map φ = ν.map ψ) :
    (∀ᵐ ω ∂μ, p (φ ω)) ↔ ∀ᵐ ω' ∂ν, p (ψ ω') := by
  rw [← ae_map_iff hφ.aemeasurable hp, hmap,
    ae_map_iff hψ.aemeasurable hp]

/-- [A real function is integrable after composition with one map exactly when it is integrable
after composition with the other](goal) when [both maps are measurable](hyp:hφ,hψ), [the real
function is measurable](hyp:k,hk), and [their pushforward measures coincide](hyp:hmap). -/
theorem integrable_comp_iff_of_map_eq
    {Ω Ω' R : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace R]
    {μ : Measure Ω} {ν : Measure Ω'} {φ : Ω → R} {ψ : Ω' → R}
    (hφ : Measurable φ) (hψ : Measurable ψ) (k : R → ℝ)
    (hk : Measurable k) (hmap : μ.map φ = ν.map ψ) :
    Integrable (k ∘ φ) μ ↔ Integrable (k ∘ ψ) ν := by
  rw [← integrable_map_measure hk.aestronglyMeasurable hφ.aemeasurable,
    hmap, integrable_map_measure hk.aestronglyMeasurable hψ.aemeasurable]

/-- [Integrating a real function after either of two maps gives the same value](goal) when [both
maps are measurable](hyp:hφ,hψ), [the real function is measurable](hyp:k,hk), and [their
pushforward measures coincide](hyp:hmap). -/
theorem integral_comp_eq_of_map_eq
    {Ω Ω' R : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace R]
    {μ : Measure Ω} {ν : Measure Ω'} {φ : Ω → R} {ψ : Ω' → R}
    (hφ : Measurable φ) (hψ : Measurable ψ) (k : R → ℝ)
    (hk : Measurable k) (hmap : μ.map φ = ν.map ψ) :
    ∫ ω, k (φ ω) ∂μ = ∫ ω', k (ψ ω') ∂ν := by
  calc
    ∫ ω, k (φ ω) ∂μ = ∫ r, k r ∂μ.map φ :=
      (integral_map hφ.aemeasurable hk.aestronglyMeasurable).symm
    _ = ∫ r, k r ∂ν.map ψ := by rw [hmap]
    _ = ∫ ω', k (ψ ω') ∂ν :=
      integral_map hψ.aemeasurable hk.aestronglyMeasurable

/-- [A conditional-mean-one identity transfers between two representations with the same
pushforward measure](goal). This holds for [two measurable maps](hyp:hφ,hψ), [a measurable
conditioning map](hyp:design,hdesign), [a measurable weighting function whose first composition
is integrable](hyp:weight,hweight,hint), [the common pushforward law](hyp:hmap), and [the identity
in the first representation](hyp:hcond). -/
theorem condExp_comp_eq_one_of_map_eq
    {Ω Ω' R D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace R] [MeasurableSpace D]
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {φ : Ω → R} {ψ : Ω' → R} (hφ : Measurable φ) (hψ : Measurable ψ)
    (design : R → D) (hdesign : Measurable design)
    (weight : R → ℝ) (hweight : Measurable weight)
    (hmap : μ.map φ = ν.map ψ) (hint : Integrable (weight ∘ φ) μ)
    (hcond : μ[weight ∘ φ |
      MeasurableSpace.comap (design ∘ φ) inferInstance] =ᵐ[μ] (fun _ => 1)) :
    ν[weight ∘ ψ | MeasurableSpace.comap (design ∘ ψ) inferInstance] =ᵐ[ν]
      (fun _ => 1) := by
  have hint' : Integrable (weight ∘ ψ) ν :=
    (integrable_comp_iff_of_map_eq hφ hψ weight hweight hmap).mp hint
  apply condExp_eq_of_integral_preimage_eq ν (design ∘ ψ)
    (hdesign.comp hψ) (weight ∘ ψ) (fun _ => 1)
    hint' (integrable_const 1)
    (stronglyMeasurable_const.aestronglyMeasurable)
  intro B hB
  let k : R → ℝ := (design ⁻¹' B).indicator weight
  have hk : Measurable k :=
    hweight.indicator (hdesign hB)
  have htransport := integral_comp_eq_of_map_eq hφ hψ k hk hmap
  have hmodel :
      ∫ ω in (design ∘ φ) ⁻¹' B, weight (φ ω) ∂μ =
        ∫ ω in (design ∘ φ) ⁻¹' B, (1 : ℝ) ∂μ := by
    calc
      ∫ ω in (design ∘ φ) ⁻¹' B, weight (φ ω) ∂μ =
          ∫ ω in (design ∘ φ) ⁻¹' B,
            μ[weight ∘ φ | MeasurableSpace.comap (design ∘ φ) inferInstance] ω ∂μ :=
        (setIntegral_condExp
          (Measurable.comap_le (hdesign.comp hφ)) hint
          ⟨B, hB, rfl⟩).symm
      _ = ∫ ω in (design ∘ φ) ⁻¹' B, (1 : ℝ) ∂μ :=
        setIntegral_congr_ae ((hdesign.comp hφ) hB)
          (hcond.mono fun _ h _ => h)
  calc
    ∫ ω in (design ∘ ψ) ⁻¹' B, (weight ∘ ψ) ω ∂ν = ∫ ω, k (ψ ω) ∂ν := by
      rw [← integral_indicator ((hdesign.comp hψ) hB)]
      rfl
    _ = ∫ ω, k (φ ω) ∂μ := htransport.symm
    _ = ∫ ω in (design ∘ φ) ⁻¹' B, weight (φ ω) ∂μ := by
      rw [← integral_indicator ((hdesign.comp hφ) hB)]
      rfl
    _ = ∫ ω in (design ∘ φ) ⁻¹' B, (1 : ℝ) ∂μ := hmodel
    _ = ∫ ω, ((design ∘ φ) ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      rw [integral_indicator ((hdesign.comp hφ) hB)]
    _ = ∫ ω, (design ⁻¹' B).indicator (fun _ => (1 : ℝ)) (φ ω) ∂μ := by
      rfl
    _ = ∫ ω, (design ⁻¹' B).indicator (fun _ => (1 : ℝ)) (ψ ω) ∂ν := by
      apply integral_comp_eq_of_map_eq hφ hψ
        ((design ⁻¹' B).indicator (fun _ => (1 : ℝ)))
      · exact measurable_const.indicator (hdesign hB)
      · exact hmap
    _ = ∫ ω, ((design ∘ ψ) ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂ν := by
      rfl
    _ = ∫ ω in (design ∘ ψ) ⁻¹' B, (1 : ℝ) ∂ν := by
      rw [integral_indicator ((hdesign.comp hψ) hB)]

end Causalean.Mathlib.MeasureTheory
