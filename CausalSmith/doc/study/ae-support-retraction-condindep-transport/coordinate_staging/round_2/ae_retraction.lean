/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Independence.Conditional

/-! # Conditional independence under almost-everywhere domain retractions

This module transports conditional expectations and conditional independence between finite
standard-Borel sample spaces linked by measurable maps that preserve the two measures and are
mutual inverses only almost everywhere.  It therefore applies to a full-measure support embedded
non-surjectively in an ambient sample space, not only to genuine measurable equivalences.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean

/-- With [a source-to-target map](hyp:r), [a measurable return map](hyp:s,hs), [the return-map
pushforward identity](hyp:hmap_s), [an almost-everywhere right-inverse identity](hyp:hrs), and
[an equality after pullback](hyp:hfg), [the target functions agree almost everywhere](goal). -/
theorem eventuallyEq_of_comp_aeRetraction
    {Ω Ω' A : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (r : Ω → Ω') (s : Ω' → Ω) (hs : Measurable s)
    {μ : Measure Ω} {μ' : Measure Ω'}
    (hmap_s : Measure.map s μ' = μ)
    (hrs : r ∘ s =ᵐ[μ'] id)
    {f g : Ω' → A}
    (hfg : f ∘ r =ᵐ[μ] g ∘ r) :
    f =ᵐ[μ'] g := by
  have hfg_map : f ∘ r =ᵐ[Measure.map s μ'] g ∘ r := by
    rw [hmap_s]
    exact hfg
  have hfg_s : (f ∘ r) ∘ s =ᵐ[μ'] (g ∘ r) ∘ s :=
    ae_of_ae_map hs.aemeasurable hfg_map
  filter_upwards [hfg_s, hrs] with y hy hry
  change f (r (s y)) = g (r (s y)) at hy
  change r (s y) = y at hry
  simpa [hry] using hy

/-- With [a measurable source-to-target map](hyp:r,hr), [its pushforward identity](hyp:hmap_r),
[a target conditioning σ-algebra contained in the ambient σ-algebra](hyp:m,hm), and [an
integrable target outcome](hyp:hf), [conditional expectation commutes almost everywhere with
pullback along the map](goal). -/
theorem condExp_comp_of_map_eq
    {Ω Ω' E : Type*}
    [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (r : Ω → Ω') (hr : Measurable r)
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hmap_r : Measure.map r μ = μ')
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → E} (hf : Integrable f μ') :
    @condExp Ω E (MeasurableSpace.comap r m) mΩ _ _ μ (f ∘ r) =ᵐ[μ]
      (@condExp Ω' E m mΩ' _ _ μ' f) ∘ r := by
  have hcm : MeasurableSpace.comap r m ≤ mΩ :=
    (MeasurableSpace.comap_mono hm).trans hr.comap_le
  have : IsFiniteMeasure (μ.trim hcm) := isFiniteMeasure_trim hcm
  have : SigmaFinite (μ.trim hcm) := inferInstance
  have : IsFiniteMeasure (μ'.trim hm) := isFiniteMeasure_trim hm
  have : SigmaFinite (μ'.trim hm) := inferInstance
  let g : Ω' → E := @condExp Ω' E m mΩ' _ _ μ' f
  have hf_map : Integrable f (@Measure.map Ω Ω' mΩ mΩ' r μ) := by
    rw [hmap_r]
    exact hf
  have hf_comp : Integrable (f ∘ r) μ :=
    @Integrable.comp_aemeasurable Ω E mΩ μ _ _ Ω' mΩ' r f hf_map
      (@Measurable.aemeasurable Ω Ω' mΩ mΩ' r μ hr)
  have hg_mu' : Integrable g μ' := by
    exact @integrable_condExp Ω' E m mΩ' μ' f _ _ _
  have hg_map : Integrable g (@Measure.map Ω Ω' mΩ mΩ' r μ) := by
    rw [hmap_r]
    exact hg_mu'
  have hg_comp : Integrable (g ∘ r) μ :=
    @Integrable.comp_aemeasurable Ω E mΩ μ _ _ Ω' mΩ' r g hg_map
      (@Measurable.aemeasurable Ω Ω' mΩ mΩ' r μ hr)
  have hr_comap : @Measurable Ω Ω' (MeasurableSpace.comap r m) m r :=
    Measurable.of_comap_le le_rfl
  have hg_strong_comap :
      @StronglyMeasurable Ω E _ (MeasurableSpace.comap r m) (g ∘ r) :=
    (@stronglyMeasurable_condExp Ω' E m mΩ' μ' f _ _).comp_measurable hr_comap
  have hg_ae : @AEStronglyMeasurable Ω E _ (MeasurableSpace.comap r m) mΩ
      (g ∘ r) μ := hg_strong_comap.aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq hcm hf_comp
    (fun s _ _ ↦ hg_comp.integrableOn) (fun s hs _ ↦ ?_)
    hg_ae).symm
  rcases hs with ⟨t, ht, rfl⟩
  calc
    ∫ x in r ⁻¹' t, g (r x) ∂μ =
        ∫ y in t, g y ∂(@Measure.map Ω Ω' mΩ mΩ' r μ) :=
      (@setIntegral_map Ω E mΩ _ _ μ Ω' mΩ' r g t (hm _ ht)
        hg_map.aestronglyMeasurable
        (@Measurable.aemeasurable Ω Ω' mΩ mΩ' r μ hr)).symm
    _ = ∫ y in t, g y ∂μ' := by rw [hmap_r]
    _ = ∫ y in t, f y ∂μ' :=
      @setIntegral_condExp Ω' E m mΩ' μ' f t _ _ _ hm _ hf ht
    _ = ∫ y in t, f y ∂(@Measure.map Ω Ω' mΩ mΩ' r μ) := by rw [hmap_r]
    _ = ∫ x in r ⁻¹' t, f (r x) ∂μ :=
      @setIntegral_map Ω E mΩ _ _ μ Ω' mΩ' r f t (hm _ ht)
        hf_map.aestronglyMeasurable
        (@Measurable.aemeasurable Ω Ω' mΩ mΩ' r μ hr)

/-- With [a measurable source-to-target map](hyp:r,hr), [its pushforward identity](hyp:hmap_r),
[a target conditioning σ-algebra contained in the ambient σ-algebra](hyp:m,hm), and [a
measurable target event](hyp:ht), [the event's conditional probability commutes almost everywhere
with pullback along the map](goal). -/
theorem condExpInd_preimage_of_map_eq
    {Ω Ω' : Type*}
    [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (r : Ω → Ω') (hr : Measurable r)
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hmap_r : Measure.map r μ = μ')
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {t : Set Ω'} (ht : @MeasurableSet Ω' mΩ' t) :
    @condExp Ω ℝ (MeasurableSpace.comap r m) mΩ _ _ μ
        ((r ⁻¹' t).indicator fun _ ↦ (1 : ℝ)) =ᵐ[μ]
      (@condExp Ω' ℝ m mΩ' _ _ μ' (t.indicator fun _ ↦ (1 : ℝ))) ∘ r := by
  have h := @condExp_comp_of_map_eq Ω Ω' ℝ mΩ mΩ' _ _ _ r hr μ μ' _ _
    hmap_r m hm (t.indicator fun _ ↦ (1 : ℝ))
    ((integrable_const (1 : ℝ)).indicator ht)
  have hfun : (t.indicator fun _ ↦ (1 : ℝ)) ∘ r =
      (r ⁻¹' t).indicator fun _ ↦ (1 : ℝ) := by
    funext x
    by_cases hx : r x ∈ t <;> simp [Function.comp_apply, hx]
  simpa only [hfun] using h

/-- With [a measurable source-to-target map](hyp:r,hr), [its pushforward identity](hyp:hmap_r),
[three target σ-algebras contained in the target ambient σ-algebra](hyp:mX,mY,mZ,hX,hY,hZ),
[conditional independence on the target pulls back to conditional independence on the
source](goal). -/
theorem condIndep_comap_of_map_eq
    {Ω Ω' : Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (r : Ω → Ω') (hr : Measurable r)
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hmap_r : Measure.map r μ = μ')
    (mX mY mZ : MeasurableSpace Ω')
    (hX : mX ≤ mΩ') (hY : mY ≤ mΩ') (hZ : mZ ≤ mΩ') :
    @CondIndep Ω' mZ mX mY mΩ' (by infer_instance) hZ μ' (by infer_instance) →
      @CondIndep Ω (MeasurableSpace.comap r mZ)
        (MeasurableSpace.comap r mX) (MeasurableSpace.comap r mY)
        mΩ (by infer_instance)
        ((MeasurableSpace.comap_mono hZ).trans hr.comap_le) μ (by infer_instance) := by
  have hcomapX : MeasurableSpace.comap r mX ≤ mΩ :=
    (MeasurableSpace.comap_mono hX).trans hr.comap_le
  have hcomapY : MeasurableSpace.comap r mY ≤ mΩ :=
    (MeasurableSpace.comap_mono hY).trans hr.comap_le
  have hr_ae : @AEMeasurable Ω Ω' mΩ' mΩ r μ :=
    @Measurable.aemeasurable Ω Ω' mΩ mΩ' r μ hr
  have transport (u : Set Ω') (hu : @MeasurableSet Ω' mΩ' u) :
      @condExp Ω ℝ (MeasurableSpace.comap r mZ) mΩ _ _ μ
          ((r ⁻¹' u).indicator fun _ ↦ (1 : ℝ)) =ᵐ[μ]
        (@condExp Ω' ℝ mZ mΩ' _ _ μ' (u.indicator fun _ ↦ (1 : ℝ))) ∘ r :=
    @condExpInd_preimage_of_map_eq Ω Ω' mΩ mΩ' r hr μ μ' _ _
      hmap_r mZ hZ u hu
  rw [ProbabilityTheory.condIndep_iff _ _ _ _ hX hY,
    ProbabilityTheory.condIndep_iff _ _ _ _ hcomapX hcomapY]
  intro h s t hs ht
  rcases hs with ⟨s, hs, rfl⟩
  rcases ht with ⟨t, ht, rfl⟩
  have hs' : @MeasurableSet Ω' mΩ' s := hX s hs
  have ht' : @MeasurableSet Ω' mΩ' t := hY t ht
  have hst' : @MeasurableSet Ω' mΩ' (s ∩ t) := hs'.inter ht'
  have htarget := h s t hs ht
  let cst : Ω' → ℝ :=
    @condExp Ω' ℝ mZ mΩ' _ _ μ' ((s ∩ t).indicator fun _ ↦ (1 : ℝ))
  let cs : Ω' → ℝ :=
    @condExp Ω' ℝ mZ mΩ' _ _ μ' (s.indicator fun _ ↦ (1 : ℝ))
  let ct : Ω' → ℝ :=
    @condExp Ω' ℝ mZ mΩ' _ _ μ' (t.indicator fun _ ↦ (1 : ℝ))
  change ∀ᵐ y ∂μ', cst y = cs y * ct y at htarget
  have hmap : ∀ᵐ y ∂(@Measure.map Ω Ω' mΩ mΩ' r μ), cst y = cs y * ct y := by
    rw [hmap_r]
    exact htarget
  have htarget' : ∀ᵐ x ∂μ, cst (r x) = cs (r x) * ct (r x) :=
    ae_of_ae_map hr_ae hmap
  have htarget_eq : (cst ∘ r) =ᵐ[μ] (cs ∘ r) * (ct ∘ r) := by
    filter_upwards [htarget'] with x hx
    exact hx
  have hinter := transport (s ∩ t) hst'
  have hleft := transport s hs'
  have hright := transport t ht'
  simpa only [cst, cs, ct, Set.preimage_inter, Pi.mul_apply, Function.comp_apply] using
    hinter.trans (htarget_eq.trans (hleft.mul hright).symm)

/-- With [measurable maps in both directions](hyp:r,s,hr,hs), [their two pushforward
identities](hyp:hmap_r,hmap_s), [an almost-everywhere right inverse](hyp:hrs), and [three target
σ-algebras contained in the target ambient σ-algebra](hyp:mX,mY,mZ,hX,hY,hZ), [conditional
independence of the three pullback σ-algebras implies target conditional independence](goal). -/
theorem condIndep_of_comap_aeRetraction
    {Ω Ω' : Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (r : Ω → Ω') (s : Ω' → Ω) (hr : Measurable r) (hs : Measurable s)
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hmap_r : Measure.map r μ = μ') (hmap_s : Measure.map s μ' = μ)
    (hrs : r ∘ s =ᵐ[μ'] id)
    (mX mY mZ : MeasurableSpace Ω')
    (hX : mX ≤ mΩ') (hY : mY ≤ mΩ') (hZ : mZ ≤ mΩ') :
    @CondIndep Ω (MeasurableSpace.comap r mZ)
        (MeasurableSpace.comap r mX) (MeasurableSpace.comap r mY)
        mΩ (by infer_instance)
        ((MeasurableSpace.comap_mono hZ).trans hr.comap_le) μ (by infer_instance) →
      @CondIndep Ω' mZ mX mY mΩ' (by infer_instance) hZ μ' (by infer_instance) := by
  have hcomapX : MeasurableSpace.comap r mX ≤ mΩ :=
    (MeasurableSpace.comap_mono hX).trans hr.comap_le
  have hcomapY : MeasurableSpace.comap r mY ≤ mΩ :=
    (MeasurableSpace.comap_mono hY).trans hr.comap_le
  have transport (u : Set Ω') (hu : @MeasurableSet Ω' mΩ' u) :
      @condExp Ω ℝ (MeasurableSpace.comap r mZ) mΩ _ _ μ
          ((r ⁻¹' u).indicator fun _ ↦ (1 : ℝ)) =ᵐ[μ]
        (@condExp Ω' ℝ mZ mΩ' _ _ μ' (u.indicator fun _ ↦ (1 : ℝ))) ∘ r :=
    @condExpInd_preimage_of_map_eq Ω Ω' mΩ mΩ' r hr μ μ' _ _
      hmap_r mZ hZ u hu
  rw [ProbabilityTheory.condIndep_iff _ _ _ _ hcomapX hcomapY,
    ProbabilityTheory.condIndep_iff _ _ _ _ hX hY]
  intro h u v hu hv
  have hpre := h (r ⁻¹' u) (r ⁻¹' v) ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
  have hu' : @MeasurableSet Ω' mΩ' u := hX u hu
  have hv' : @MeasurableSet Ω' mΩ' v := hY v hv
  have huv' : @MeasurableSet Ω' mΩ' (u ∩ v) := hu'.inter hv'
  have hinter := transport (u ∩ v) huv'
  have hleft := transport u hu'
  have hright := transport v hv'
  have hpull := hinter.symm.trans (hpre.trans (hleft.mul hright))
  let cuv : Ω' → ℝ :=
    @condExp Ω' ℝ mZ mΩ' _ _ μ' ((u ∩ v).indicator fun _ ↦ (1 : ℝ))
  let cu : Ω' → ℝ :=
    @condExp Ω' ℝ mZ mΩ' _ _ μ' (u.indicator fun _ ↦ (1 : ℝ))
  let cv : Ω' → ℝ :=
    @condExp Ω' ℝ mZ mΩ' _ _ μ' (v.indicator fun _ ↦ (1 : ℝ))
  change (cuv ∘ r) =ᵐ[μ] ((fun y ↦ cu y * cv y) ∘ r) at hpull
  change cuv =ᵐ[μ'] fun y ↦ cu y * cv y
  exact @eventuallyEq_of_comp_aeRetraction Ω Ω' ℝ mΩ mΩ' r s hs μ μ'
    hmap_s hrs cuv (fun y ↦ cu y * cv y) hpull

/-- With [measurable maps in both directions](hyp:r,s,hr,hs), [their two pushforward
identities](hyp:hmap_r,hmap_s),
[almost-everywhere inverse identities in both directions](hyp:_hsr,hrs),
and [three target σ-algebras contained in the target ambient σ-algebra](hyp:mX,mY,mZ,hX,hY,hZ),
[target conditional independence is equivalent to conditional
independence of the three pullback σ-algebras](goal). -/
theorem condIndep_comap_aeEquiv_iff
    {Ω Ω' : Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (r : Ω → Ω') (s : Ω' → Ω) (hr : Measurable r) (hs : Measurable s)
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hmap_r : Measure.map r μ = μ') (hmap_s : Measure.map s μ' = μ)
    (_hsr : s ∘ r =ᵐ[μ] id) (hrs : r ∘ s =ᵐ[μ'] id)
    (mX mY mZ : MeasurableSpace Ω')
    (hX : mX ≤ mΩ') (hY : mY ≤ mΩ') (hZ : mZ ≤ mΩ') :
    @CondIndep Ω (MeasurableSpace.comap r mZ)
        (MeasurableSpace.comap r mX) (MeasurableSpace.comap r mY)
        mΩ (by infer_instance)
        ((MeasurableSpace.comap_mono hZ).trans hr.comap_le) μ (by infer_instance) ↔
      @CondIndep Ω' mZ mX mY mΩ' (by infer_instance) hZ μ' (by infer_instance) := by
  constructor
  · exact condIndep_of_comap_aeRetraction
      (mΩ := mΩ) (mΩ' := mΩ') (r := r) (s := s) (μ := μ) (μ' := μ')
      hr hs hmap_r hmap_s hrs
      (mX := mX) (mY := mY) (mZ := mZ) hX hY hZ
  · exact condIndep_comap_of_map_eq
      (mΩ := mΩ) (mΩ' := mΩ') (r := r) (μ := μ) (μ' := μ')
      hr hmap_r (mX := mX) (mY := mY) (mZ := mZ) hX hY hZ

/-- With [measurable maps in both directions](hyp:r,s,hr,hs), [their two pushforward
identities](hyp:hmap_r,hmap_s),
[almost-everywhere inverse identities in both directions](hyp:_hsr,hrs),
[three target random variables](hyp:X,Y,Z), and [their measurability](hyp:hX,hY,hZ),
[conditional independence of the first two variables given the third is
equivalent to conditional independence of their pullbacks given the pulled-back third
variable](goal). -/
theorem condIndepFun_comp_aeEquiv_iff
    {Ω Ω' 𝒳 𝒴 𝒵 : Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω']
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace 𝒵]
    (r : Ω → Ω') (s : Ω' → Ω) (hr : Measurable r) (hs : Measurable s)
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hmap_r : Measure.map r μ = μ') (hmap_s : Measure.map s μ' = μ)
    (_hsr : s ∘ r =ᵐ[μ] id) (hrs : r ∘ s =ᵐ[μ'] id)
    (X : Ω' → 𝒳) (Y : Ω' → 𝒴) (Z : Ω' → 𝒵)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    CondIndepFun
        (MeasurableSpace.comap (Z ∘ r) inferInstance)
        (mΩ := mΩ) (hZ.comp hr).comap_le
        (X ∘ r) (Y ∘ r) μ ↔
      CondIndepFun
      (MeasurableSpace.comap Z inferInstance)
        (mΩ := mΩ') hZ.comap_le X Y μ' := by
  rw [ProbabilityTheory.condIndepFun_iff_condIndep,
    ProbabilityTheory.condIndepFun_iff_condIndep]
  simpa only [MeasurableSpace.comap_comp] using
    condIndep_comap_aeEquiv_iff r s hr hs hmap_r hmap_s _hsr hrs
      (MeasurableSpace.comap X inferInstance)
      (MeasurableSpace.comap Y inferInstance)
      (MeasurableSpace.comap Z inferInstance)
      hX.comap_le hY.comap_le hZ.comap_le

/-- A genuine measure-preserving measurable equivalence is a special case of the
almost-everywhere transport theorem, with its pointwise inverse identities supplied as
almost-everywhere identities. -/
example
    {Ω Ω' 𝒳 𝒴 𝒵 : Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω']
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace 𝒵]
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (e : Ω ≃ᵐ Ω') (he : MeasurePreserving e μ μ')
    (X : Ω' → 𝒳) (Y : Ω' → 𝒴) (Z : Ω' → 𝒵)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    CondIndepFun
        (MeasurableSpace.comap (Z ∘ e) inferInstance)
        (mΩ := mΩ) (hZ.comp e.measurable).comap_le
        (X ∘ e) (Y ∘ e) μ ↔
      CondIndepFun
        (MeasurableSpace.comap Z inferInstance)
        (mΩ := mΩ') hZ.comap_le X Y μ' := by
  have hmap_s : Measure.map e.symm μ' = μ :=
    ((MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq e).mp he.map_eq).symm
  exact condIndepFun_comp_aeEquiv_iff e e.symm e.measurable e.symm.measurable
    he.map_eq hmap_s
    (Filter.Eventually.of_forall e.symm_apply_apply)
    (Filter.Eventually.of_forall e.apply_symm_apply)
    X Y Z hX hY hZ

/-- The support inclusion selecting `false` from `Bool` is not surjective, while the preceding
example below still transports conditional independence because the ambient Dirac measure is
concentrated on that support. -/
example :
    ¬ Function.Surjective (fun _ : Unit ↦ false : Unit → Bool) := by
  intro h
  obtain ⟨u, hu⟩ := h true
  cases u
  simp at hu

/-- A one-point full-measure support inside a Boolean ambient sample space illustrates that the
transport theorem needs almost-everywhere inverses rather than a surjective carrier equivalence. -/
example
    {𝒳 𝒴 𝒵 : Type*}
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace 𝒵]
    (X : Unit → 𝒳) (Y : Unit → 𝒴) (Z : Unit → 𝒵)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    CondIndepFun
        (MeasurableSpace.comap (Z ∘ (fun _ : Bool ↦ ())) inferInstance)
        (mΩ := inferInstance) (hZ.comp measurable_const).comap_le
        (X ∘ (fun _ : Bool ↦ ())) (Y ∘ (fun _ : Bool ↦ ()))
        (Measure.dirac false) ↔
      CondIndepFun
        (MeasurableSpace.comap Z inferInstance)
        (mΩ := inferInstance) hZ.comap_le X Y (Measure.dirac ()) := by
  let r : Bool → Unit := fun _ ↦ ()
  let s : Unit → Bool := fun _ ↦ false
  have hr : Measurable r := measurable_const
  have hs : Measurable s := measurable_const
  have hmap_r : Measure.map r (Measure.dirac false) = Measure.dirac () := by
    simp [hr, r]
  have hmap_s : Measure.map s (Measure.dirac ()) = Measure.dirac false := by
    simp [hs, s]
  have hsr : s ∘ r =ᵐ[Measure.dirac false] id := by
    simp [Filter.EventuallyEq, r, s]
  have hrs : r ∘ s =ᵐ[Measure.dirac ()] id := by
    exact Filter.Eventually.of_forall (fun u ↦ by cases u; rfl)
  simpa [r] using
    condIndepFun_comp_aeEquiv_iff r s hr hs hmap_r hmap_s hsr hrs X Y Z hX hY hZ

end Causalean
