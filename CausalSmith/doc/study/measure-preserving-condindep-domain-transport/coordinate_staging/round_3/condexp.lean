/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Independence.Conditional

/-! # Conditional expectations under sample-domain equivalences

This module proves that conditional expectations and conditional probabilities commute with a
measure-preserving measurable equivalence of sample domains when the conditioning σ-algebra is
pulled back along the equivalence.
-/

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

namespace Causalean

/-- With [a measure-preserving measurable equivalence of sample domains](hyp:e,he), [a target
conditioning σ-algebra contained in the target ambient σ-algebra](hyp:m,hm), and [an integrable
outcome on the target domain](hyp:hf), [the conditional expectation after pulling back both the
outcome and the conditioning information is the pulled-back target conditional expectation almost
everywhere](goal). -/
theorem condExp_comp_measurableEquiv
    {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : Ω ≃ᵐ Ω') {μ : Measure Ω} {μ' : Measure Ω'}
    (he : MeasurePreserving e μ μ')
    (m : MeasurableSpace Ω') (hm : m ≤ ‹MeasurableSpace Ω'›)
    {f : Ω' → E} (hf : Integrable f μ') :
    μ[f ∘ e | MeasurableSpace.comap e m] =ᵐ[μ] (μ'[f | m]) ∘ e := by
  rename_i mΩ mΩ' ngrp nspace cspace
  let ee : Ω ≃ Ω' := @MeasurableEquiv.toEquiv Ω Ω' mΩ mΩ' e
  let ce : Ω' → E := @condExp Ω' E m mΩ' ngrp nspace μ' f
  have hee : @MeasurePreserving Ω Ω' mΩ mΩ' ee μ μ' := by
    simpa [ee] using he
  have hee_meas : @Measurable Ω Ω' mΩ mΩ' ee :=
    @MeasurableEquiv.measurable Ω Ω' mΩ mΩ' e
  have hee_emb : @MeasurableEmbedding Ω Ω' mΩ mΩ' ee :=
    @MeasurableEquiv.measurableEmbedding Ω Ω' mΩ mΩ' e
  have hee_symm_meas : @Measurable Ω' Ω mΩ' mΩ ee.symm := by
    simpa [ee] using
      (@MeasurableEquiv.measurable Ω' Ω mΩ' mΩ
        (@MeasurableEquiv.symm Ω Ω' mΩ mΩ' e))
  have hmeasure (s : Set Ω') : μ (ee ⁻¹' s) = μ' s := by
    letI : MeasurableSpace Ω' := mΩ'
    exact hee.measure_preimage_emb hee_emb s
  have hsetIntegral (g : Ω' → E) (s : Set Ω') :
      ∫ x in ee ⁻¹' s, g (ee x) ∂μ = ∫ y in s, g y ∂μ' := by
    letI : MeasurableSpace Ω' := mΩ'
    exact hee.setIntegral_preimage_emb hee_emb g s
  have result :
      μ[f ∘ ee | MeasurableSpace.comap ee m] =ᵐ[μ] ce ∘ ee := by
    by_cases hle : m ≤ mΩ'
    · have hcm : MeasurableSpace.comap ee m ≤ mΩ :=
        (MeasurableSpace.comap_mono hle).trans hee_meas.comap_le
      let em : @MeasurableEquiv Ω Ω' (MeasurableSpace.comap ee m) m := by
        letI : MeasurableSpace Ω := MeasurableSpace.comap ee m
        letI : MeasurableSpace Ω' := m
        exact MeasurableEquiv.mk ee
          (Measurable.of_comap_le le_rfl)
          (by
            rw [measurable_iff_comap_le]
            intro s hs
            rcases hs with ⟨t, ⟨u, hu, rfl⟩, rfl⟩
            simpa [Set.preimage_preimage] using hu)
      have em_meas : @Measurable Ω Ω' (MeasurableSpace.comap ee m) m ee :=
        @MeasurableEquiv.measurable Ω Ω' (MeasurableSpace.comap ee m) m em
      have hemp : @MeasurePreserving Ω Ω' (MeasurableSpace.comap ee m) m ee
          (μ.trim hcm) (μ'.trim hle) := by
        letI : MeasurableSpace Ω := MeasurableSpace.comap ee m
        letI : MeasurableSpace Ω' := m
        refine ⟨em_meas, ?_⟩
        ext s hs
        rw [Measure.map_apply em_meas hs, trim_measurableSet_eq hcm (em_meas hs),
          trim_measurableSet_eq hle hs, hmeasure s]
      have hmap : @Measure.map Ω Ω' (MeasurableSpace.comap ee m) m ee (μ.trim hcm) =
          μ'.trim hle := by
        letI : MeasurableSpace Ω := MeasurableSpace.comap ee m
        letI : MeasurableSpace Ω' := m
        exact hemp.map_eq
      by_cases hσ : SigmaFinite (μ'.trim hle)
      · letI : SigmaFinite (μ'.trim hle) := hσ
        have hmapped : SigmaFinite
            (@Measure.map Ω Ω' (MeasurableSpace.comap ee m) m ee (μ.trim hcm)) := by
          rw [hmap]
          exact hσ
        haveI : SigmaFinite (μ.trim hcm) :=
          @SigmaFinite.of_map Ω Ω' (MeasurableSpace.comap ee m) m
            (μ.trim hcm) ee em_meas.aemeasurable hmapped
        have hfcomp : Integrable (f ∘ ee) μ := by
          letI : MeasurableSpace Ω' := mΩ'
          exact hee.integrable_comp_of_integrable hf
        have hce_int : Integrable ce μ' :=
          @integrable_condExp Ω' E m mΩ' μ' f ngrp nspace cspace
        have hg_int : Integrable (ce ∘ ee) μ := by
          letI : MeasurableSpace Ω' := mΩ'
          exact hee.integrable_comp_of_integrable hce_int
        refine (ae_eq_condExp_of_forall_setIntegral_eq hcm hfcomp
          (fun s _ _ ↦ hg_int.integrableOn) (fun s hs _ ↦ ?_) ?_).symm
        · rcases hs with ⟨t, ht, rfl⟩
          calc
            ∫ x in ee ⁻¹' t, ce (ee x) ∂μ =
                ∫ y in t, ce y ∂μ' := hsetIntegral ce t
            _ = ∫ y in t, f y ∂μ' :=
              @setIntegral_condExp Ω' E m mΩ' μ' f t ngrp nspace cspace hle hσ hf ht
            _ = ∫ x in ee ⁻¹' t, f (ee x) ∂μ := (hsetIntegral f t).symm
        · exact
            ((@stronglyMeasurable_condExp Ω' E m mΩ' μ' f ngrp nspace).comp_measurable
              em_meas).aestronglyMeasurable
      · have hσ' : ¬ SigmaFinite (μ.trim hcm) := by
          intro h
          letI : SigmaFinite (μ.trim hcm) := h
          apply hσ
          have hmapped : SigmaFinite
              (@Measure.map Ω Ω' (MeasurableSpace.comap ee m) m ee (μ.trim hcm)) :=
            @MeasurableEquiv.sigmaFinite_map Ω Ω' (MeasurableSpace.comap ee m) m
              (μ.trim hcm) em h
          rw [hmap] at hmapped
          exact hmapped
        rw [condExp_of_not_sigmaFinite hcm hσ']
        unfold ce
        rw [@condExp_of_not_sigmaFinite Ω' E m mΩ' μ' f ngrp nspace hle hσ]
        exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · have hcm : ¬ MeasurableSpace.comap ee m ≤ mΩ := by
        intro h
        apply hle
        intro s hs
        have hpre : @MeasurableSet Ω (MeasurableSpace.comap ee m) (ee ⁻¹' s) :=
          ⟨s, hs, rfl⟩
        have hs' : @MeasurableSet Ω mΩ (ee ⁻¹' s) := h _ hpre
        simpa [Set.preimage_preimage] using hee_symm_meas hs'
      rw [condExp_of_not_le hcm]
      unfold ce
      rw [@condExp_of_not_le Ω' E m mΩ' μ' f ngrp nspace hle]
      exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  simpa [ee, ce] using result

/-- With [a measure-preserving measurable equivalence of finite sample measures](hyp:e,he), [a
target conditioning σ-algebra contained in the target ambient σ-algebra](hyp:m,hm), and [a
measurable target event](hyp:s,hs), [the conditional probability of its preimage under the
pulled-back conditioning information is the pulled-back target conditional probability almost
everywhere](goal). -/
theorem condExpInd_preimage_measurableEquiv
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (e : Ω ≃ᵐ Ω') {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (he : MeasurePreserving e μ μ')
    (m : MeasurableSpace Ω') (hm : m ≤ ‹MeasurableSpace Ω'›)
    {s : Set Ω'} (hs : MeasurableSet s) :
    μ⟦e ⁻¹' s | MeasurableSpace.comap e m⟧ =ᵐ[μ]
      (μ'⟦s | m⟧) ∘ e := by
  rename_i mΩ mΩ' hμ hμ'
  by_cases hle : m ≤ mΩ'
  · have hs' : @MeasurableSet Ω' mΩ' s := hle _ hs
    have h := @condExp_comp_measurableEquiv Ω Ω' ℝ mΩ mΩ'
      _ _ _ e μ μ' he m hm (s.indicator fun _ ↦ (1 : ℝ))
      ((integrable_const (1 : ℝ)).indicator hs')
    have hfun : (s.indicator fun _ ↦ (1 : ℝ)) ∘ e =
        (e ⁻¹' s).indicator fun _ ↦ (1 : ℝ) := by
      funext x
      by_cases hx : e x ∈ s <;> simp [Function.comp_apply, hx]
    simpa only [hfun] using h
  · let ee : Ω ≃ Ω' := @MeasurableEquiv.toEquiv Ω Ω' mΩ mΩ' e
    have hee_symm_meas : @Measurable Ω' Ω mΩ' mΩ ee.symm := by
      simpa [ee] using
        (@MeasurableEquiv.measurable Ω' Ω mΩ' mΩ
          (@MeasurableEquiv.symm Ω Ω' mΩ mΩ' e))
    have hcm : ¬ MeasurableSpace.comap ee m ≤ mΩ := by
      intro h
      apply hle
      intro t ht
      have hpre : @MeasurableSet Ω (MeasurableSpace.comap ee m) (ee ⁻¹' t) :=
        ⟨t, ht, rfl⟩
      have ht' : @MeasurableSet Ω mΩ (ee ⁻¹' t) := h _ hpre
      simpa [Set.preimage_preimage] using hee_symm_meas ht'
    have hcm' : ¬ MeasurableSpace.comap e m ≤ mΩ := by
      simpa [ee] using hcm
    rw [condExp_of_not_le hcm',
      @condExp_of_not_le Ω' ℝ m mΩ' μ' (s.indicator fun _ ↦ (1 : ℝ))
        _ _ hle]
    exact Filter.Eventually.of_forall (fun _ ↦ rfl)

end Causalean
