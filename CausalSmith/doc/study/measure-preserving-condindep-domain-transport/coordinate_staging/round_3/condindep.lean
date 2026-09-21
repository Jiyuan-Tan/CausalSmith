/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.CondIndep.DomainTransport.CondExp

/-! # Conditional independence under sample-domain equivalences

This module transports conditional independence through a measure-preserving measurable
equivalence of sample domains, pulling both random-variable σ-algebras and the conditioning
σ-algebra back to the source domain.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean

/-- With [a measure-preserving measurable equivalence of finite standard-Borel sample
spaces](hyp:e,he) and [three target-domain σ-algebras contained in the target ambient
σ-algebra](hyp:mX,mY,mZ,hX,hY,hZ),
[conditional independence of the first two σ-algebras given the third is equivalent to conditional
independence of all three σ-algebras after pullback to the source domain](goal). -/
theorem condIndep_comap_measurableEquiv_iff
    {Ω Ω' : Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (e : Ω ≃ᵐ Ω') {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (he : MeasurePreserving e μ μ')
    (mX mY mZ : MeasurableSpace Ω')
    (hX : mX ≤ mΩ')
    (hY : mY ≤ mΩ')
    (hZ : mZ ≤ mΩ') :
    @CondIndep Ω (MeasurableSpace.comap e mZ)
        (MeasurableSpace.comap e mX) (MeasurableSpace.comap e mY)
        mΩ (by infer_instance)
        ((MeasurableSpace.comap_mono hZ).trans
          (@Measurable.comap_le Ω Ω' mΩ mΩ' e
            (@MeasurableEquiv.measurable Ω Ω' mΩ mΩ' e))) μ
        (by infer_instance) ↔
      @CondIndep Ω' mZ mX mY mΩ' (by infer_instance) hZ μ' (by infer_instance) := by
  have he_meas : @Measurable Ω Ω' mΩ mΩ' e :=
    @MeasurableEquiv.measurable Ω Ω' mΩ mΩ' e
  have he_emb : @MeasurableEmbedding Ω Ω' mΩ mΩ' e :=
    @MeasurableEquiv.measurableEmbedding Ω Ω' mΩ mΩ' e
  have hmap_eq : @Measure.map Ω Ω' mΩ mΩ' e μ = μ' :=
    @MeasurePreserving.map_eq Ω Ω' mΩ mΩ' e μ μ' he
  have hcomapX : MeasurableSpace.comap e mX ≤ mΩ :=
    (MeasurableSpace.comap_mono hX).trans he_meas.comap_le
  have hcomapY : MeasurableSpace.comap e mY ≤ mΩ :=
    (MeasurableSpace.comap_mono hY).trans he_meas.comap_le
  have transport (s : Set Ω') (hs : @MeasurableSet Ω' mΩ' s) :
      @condExp Ω ℝ (MeasurableSpace.comap e mZ) mΩ _ _ μ
          ((e ⁻¹' s).indicator fun _ ↦ (1 : ℝ)) =ᵐ[μ]
        (@condExp Ω' ℝ mZ mΩ' _ _ μ' (s.indicator fun _ ↦ (1 : ℝ))) ∘ e := by
    have h := @condExp_comp_measurableEquiv Ω Ω' ℝ mΩ mΩ' _ _ _
      e μ μ' he mZ le_rfl (s.indicator fun _ ↦ (1 : ℝ))
      ((integrable_const (1 : ℝ)).indicator hs)
    have hfun : (s.indicator fun _ ↦ (1 : ℝ)) ∘ e =
        (e ⁻¹' s).indicator fun _ ↦ (1 : ℝ) := by
      funext x
      by_cases hx : e x ∈ s <;> simp [Function.comp_apply, hx]
    simpa only [hfun] using h
  rw [ProbabilityTheory.condIndep_iff _ _ _ _
      hcomapX hcomapY,
    ProbabilityTheory.condIndep_iff _ _ _ _ hX hY]
  constructor
  · intro h s t hs ht
    have hpre := h (e ⁻¹' s) (e ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    have hs' : @MeasurableSet Ω' mΩ' s := hX s hs
    have ht' : @MeasurableSet Ω' mΩ' t := hY t ht
    have hst' : @MeasurableSet Ω' mΩ' (s ∩ t) := hs'.inter ht'
    have hinter := transport (s ∩ t) hst'
    have hleft := transport s hs'
    have hright := transport t ht'
    have hpull := hinter.symm.trans (hpre.trans (hleft.mul hright))
    let cst : Ω' → ℝ :=
      @condExp Ω' ℝ mZ mΩ' _ _ μ' ((s ∩ t).indicator fun _ ↦ (1 : ℝ))
    let cs : Ω' → ℝ := @condExp Ω' ℝ mZ mΩ' _ _ μ' (s.indicator fun _ ↦ (1 : ℝ))
    let ct : Ω' → ℝ := @condExp Ω' ℝ mZ mΩ' _ _ μ' (t.indicator fun _ ↦ (1 : ℝ))
    change ∀ᵐ x ∂μ, cst (e x) = cs (e x) * ct (e x) at hpull
    have hmap : ∀ᵐ y ∂(@Measure.map Ω Ω' mΩ mΩ' e μ), cst y = cs y * ct y :=
      (he_emb.ae_map_iff (μ := μ)).mpr hpull
    rw [hmap_eq] at hmap
    change ∀ᵐ y ∂μ', cst y = cs y * ct y
    exact hmap
  · intro h s t hs ht
    rcases hs with ⟨s, hs, rfl⟩
    rcases ht with ⟨t, ht, rfl⟩
    have hs' : @MeasurableSet Ω' mΩ' s := hX s hs
    have ht' : @MeasurableSet Ω' mΩ' t := hY t ht
    have hst' : @MeasurableSet Ω' mΩ' (s ∩ t) := hs'.inter ht'
    have htarget := h s t hs ht
    let cst : Ω' → ℝ :=
      @condExp Ω' ℝ mZ mΩ' _ _ μ' ((s ∩ t).indicator fun _ ↦ (1 : ℝ))
    let cs : Ω' → ℝ := @condExp Ω' ℝ mZ mΩ' _ _ μ' (s.indicator fun _ ↦ (1 : ℝ))
    let ct : Ω' → ℝ := @condExp Ω' ℝ mZ mΩ' _ _ μ' (t.indicator fun _ ↦ (1 : ℝ))
    change ∀ᵐ y ∂μ', cst y = cs y * ct y at htarget
    have hmap : ∀ᵐ y ∂(@Measure.map Ω Ω' mΩ mΩ' e μ), cst y = cs y * ct y := by
      rw [hmap_eq]
      exact htarget
    have htarget' : ∀ᵐ x ∂μ, cst (e x) = cs (e x) * ct (e x) :=
      (he_emb.ae_map_iff (μ := μ)).mp hmap
    have htarget_eq : (cst ∘ e) =ᵐ[μ] (cs ∘ e) * (ct ∘ e) := by
      filter_upwards [htarget'] with x hx
      exact hx
    have hinter := transport (s ∩ t) hst'
    have hleft := transport s hs'
    have hright := transport t ht'
    simpa only [cst, cs, ct, Set.preimage_inter, Pi.mul_apply, Function.comp_apply] using
      hinter.trans (htarget_eq.trans (hleft.mul hright).symm)

/-- With [a measure-preserving measurable equivalence of finite standard-Borel sample
spaces](hyp:e,he) and [three measurable target-domain random variables](hyp:X,Y,Z,hX,hY,hZ),
[conditional
independence of the first two given the third is equivalent to conditional independence of their
compositions with the equivalence given the composed conditioning variable](goal). -/
theorem condIndepFun_comp_measurableEquiv_iff
    {Ω Ω' 𝒳 𝒴 𝒵 : Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω']
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace 𝒵]
    (e : Ω ≃ᵐ Ω') {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (he : MeasurePreserving e μ μ')
    (X : Ω' → 𝒳) (Y : Ω' → 𝒴) (Z : Ω' → 𝒵)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    CondIndepFun
        (MeasurableSpace.comap (Z ∘ e) inferInstance)
        (mΩ := mΩ)
        (hZ.comp e.measurable).comap_le
        (X ∘ e) (Y ∘ e) μ ↔
      CondIndepFun
        (MeasurableSpace.comap Z inferInstance)
        (mΩ := mΩ')
        hZ.comap_le X Y μ' := by
  rw [ProbabilityTheory.condIndepFun_iff_condIndep,
    ProbabilityTheory.condIndepFun_iff_condIndep]
  simpa only [MeasurableSpace.comap_comp] using
    condIndep_comap_measurableEquiv_iff e he
      (MeasurableSpace.comap X inferInstance)
      (MeasurableSpace.comap Y inferInstance)
      (MeasurableSpace.comap Z inferInstance)
      hX.comap_le hY.comap_le hZ.comap_le

end Causalean
