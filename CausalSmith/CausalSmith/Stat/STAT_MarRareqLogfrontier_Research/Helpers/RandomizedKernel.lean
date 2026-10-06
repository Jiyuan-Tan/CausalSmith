module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Basic
public import Causalean.Stat.Minimax.TotalVariation
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Representation
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Barycenters, clipping and uniform-seed representations of all bounded scalar kernels,
and total-variation comparison of joint input/action experiments. Common independent seeds
and deterministic projections are constant-kernel and deterministic-kernel specializations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:Z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev BoundedKernel (Z : Type*) [MeasurableSpace Z] := BoundedRealKernel Z

/-- For [the specified inputs and assumptions](hyp:Z,κ,o), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def barycenter {Z : Type*} [MeasurableSpace Z]
    (κ : BoundedKernel Z) (o : Z) : ℝ := ∫ h, h ∂(κ.1 o)

/-- For [the specified inputs and assumptions](hyp:Z,Λ,Q,θ,κ,param), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def kernelRisk {Z Λ : Type*} [MeasurableSpace Z]
    (Q : Λ → Measure Z) (θ : Λ → ℝ) (κ : BoundedKernel Z) (param : Λ) : ℝ :=
  ∫ o, (∫ h, (h - θ param) ^ 2 ∂(κ.1 o)) ∂(Q param)

/-- For [the specified inputs and assumptions](hyp:Z,Λ,Q,θ,f,param), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def mapRisk {Z Λ : Type*} [MeasurableSpace Z]
    (Q : Λ → Measure Z) (θ : Λ → ℝ) (f : Z → ℝ) (param : Λ) : ℝ :=
  ∫ o, (f o - θ param) ^ 2 ∂(Q param)

/-- For [the specified inputs and assumptions](hyp:Z,Λ,Q,θ,κ,param), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def realKernelRisk {Z Λ : Type*} [MeasurableSpace Z]
    (Q : Λ → Measure Z) (θ : Λ → ℝ)
    (κ : Kernel Z ℝ) (param : Λ) : ℝ≥0∞ :=
  ∫⁻ o, (∫⁻ h, ENNReal.ofReal ((h - θ param) ^ 2) ∂(κ o)) ∂(Q param)

/-- For [the specified inputs and assumptions](hyp:h), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def realKernelClip (h : ℝ) : ℝ := max (-1) (min 1 h)

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev UnitSeed := Icc (0 : ℝ) 1
/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def uniformSeedLaw : Measure UnitSeed := volume.comap Subtype.val

/-- Given [the specified inputs and assumptions](hyp:Z,κ,o,c), [the stated mathematical conclusion holds](goal). -/
-- @node: kernel_barycenter_variance_identity
lemma kernel_barycenter_variance_identity {Z : Type*} [MeasurableSpace Z]
    (κ : BoundedKernel Z) (o : Z) (c : ℝ) :
    (∫ h, (h - c) ^ 2 ∂(κ.1 o)) = (barycenter κ o - c) ^ 2 +
      ∫ h, (h - barycenter κ o) ^ 2 ∂(κ.1 o) := by
  let : IsMarkovKernel κ.1 := κ.2.1
  have hbounded : ∀ᵐ h ∂(κ.1 o), h ∈ Icc (-1 : ℝ) 1 :=
    (ae_mem_iff_measure_eq (μ := κ.1 o) measurableSet_Icc.nullMeasurableSet).2
      (by simpa only [measure_univ] using κ.2.2 o)
  have hmeas : AEStronglyMeasurable (fun h : ℝ => h) (κ.1 o) := by fun_prop
  have hLp : MemLp (fun h : ℝ => h) 2 (κ.1 o) :=
    memLp_of_bounded hbounded hmeas 2
  have hshiftLp : MemLp (fun h : ℝ => h - c) 2 (κ.1 o) :=
    hLp.sub (memLp_const c)
  have hmean : (∫ h, h - c ∂(κ.1 o)) = barycenter κ o - c := by
    rw [integral_sub (hLp.integrable (by norm_num)) (integrable_const c)]
    simp [barycenter]
  have hvar := variance_eq_sub hshiftLp
  rw [variance_sub_const hmeas c, variance_eq_integral hLp.aemeasurable] at hvar
  change (∫ h, (h - ∫ x, x ∂(κ.1 o)) ^ 2 ∂(κ.1 o)) =
    (∫ h, (h - c) ^ 2 ∂(κ.1 o)) - (∫ h, h - c ∂(κ.1 o)) ^ 2 at hvar
  rw [hmean] at hvar
  dsimp only [barycenter] at *
  linarith


/-- Given [the specified inputs and assumptions](hyp:Z,κ,o), [the stated mathematical conclusion holds](goal). -/
-- @node: kernel_barycenter_mem
lemma kernel_barycenter_mem {Z : Type*} [MeasurableSpace Z]
    (κ : BoundedKernel Z) (o : Z) : barycenter κ o ∈ Icc (-1 : ℝ) 1 := by
  let : IsMarkovKernel κ.1 := κ.2.1
  have hb : ∀ᵐ h ∂(κ.1 o), h ∈ Icc (-1 : ℝ) 1 :=
    (ae_mem_iff_measure_eq (μ := κ.1 o) measurableSet_Icc.nullMeasurableSet).2
      (by simpa only [measure_univ] using κ.2.2 o)
  have hi : Integrable (fun h : ℝ => h) (κ.1 o) := by
    apply Integrable.of_mem_Icc (-1) 1
    · fun_prop
    · exact hb
  constructor
  · have h := integral_mono_ae (integrable_const (-1 : ℝ)) hi
      (hb.mono fun _ hh => hh.1)
    simpa [barycenter] using h
  · have h := integral_mono_ae hi (integrable_const (1 : ℝ))
      (hb.mono fun _ hh => hh.2)
    simpa [barycenter] using h

/-- Given [the specified inputs and assumptions](hyp:Z,κ,o,c), [the stated mathematical conclusion holds](goal). -/
-- @node: kernel_barycenter_sq_le
lemma kernel_barycenter_sq_le {Z : Type*} [MeasurableSpace Z]
    (κ : BoundedKernel Z) (o : Z) (c : ℝ) :
    (barycenter κ o - c) ^ 2 ≤ ∫ h, (h - c) ^ 2 ∂(κ.1 o) := by
  rw [kernel_barycenter_variance_identity]
  exact le_add_of_nonneg_right (integral_nonneg fun _ => sq_nonneg _)

/-- Given [the specified inputs and assumptions](hyp:Z,Λ,Q,hQ,θ,κ,param), [the stated mathematical conclusion holds](goal). -/
-- @node: kernel_barycenter_risk_le
lemma kernel_barycenter_risk_le
    {Z Λ : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Λ → Measure Z) (hQ : ∀ param, IsProbabilityMeasure (Q param))
    (θ : Λ → ℝ) (κ : BoundedKernel Z) (param : Λ) :
    mapRisk Q θ (barycenter κ) param ≤ kernelRisk Q θ κ param := by
  let : IsProbabilityMeasure (Q param) := hQ param
  exact integral_mono Integrable.of_finite Integrable.of_finite
    (fun o => kernel_barycenter_sq_le κ o (θ param))

/-- Given [the specified inputs and assumptions](hyp:Z,Λ,Q,hQ,θ,hθ,κ,param), [the stated mathematical conclusion holds](goal). -/
-- @node: bounded_kernelRisk_bounds
lemma bounded_kernelRisk_bounds
    {Z Λ : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Λ → Measure Z) (hQ : ∀ param, IsProbabilityMeasure (Q param))
    (θ : Λ → ℝ) (hθ : ∀ param, θ param ∈ Icc (-1 : ℝ) 1)
    (κ : BoundedKernel Z) (param : Λ) : kernelRisk Q θ κ param ∈ Icc (0 : ℝ) 4 := by
  let : IsProbabilityMeasure (Q param) := hQ param
  let : IsMarkovKernel κ.1 := κ.2.1
  have hinner (o : Z) : (∫ h, (h - θ param) ^ 2 ∂(κ.1 o)) ≤ 4 := by
    have hb : ∀ᵐ h ∂(κ.1 o), h ∈ Icc (-1 : ℝ) 1 :=
      (ae_mem_iff_measure_eq (μ := κ.1 o) measurableSet_Icc.nullMeasurableSet).2
        (by simpa only [measure_univ] using κ.2.2 o)
    have hs : ∀ᵐ h ∂(κ.1 o), (h - θ param) ^ 2 ∈ Icc (0 : ℝ) 4 := by
      filter_upwards [hb] with h hh
      refine ⟨sq_nonneg _, ?_⟩
      obtain ⟨hl, hu⟩ := hh
      obtain ⟨cl, cu⟩ := hθ param
      nlinarith [sq_nonneg (h - θ param + 2), sq_nonneg (h - θ param - 2),
        mul_nonneg (by linarith : 0 ≤ 2 - (h - θ param))
          (by linarith : 0 ≤ 2 + (h - θ param))]
    have hi : Integrable (fun h => (h - θ param) ^ 2) (κ.1 o) := by
      apply Integrable.of_mem_Icc 0 4
      · fun_prop
      · exact hs
    have h := integral_mono_ae hi (integrable_const (4 : ℝ))
      (hs.mono fun _ hh => hh.2)
    simpa using h
  refine ⟨integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _)), ?_⟩
  have h := integral_mono (μ := Q param) Integrable.of_finite
    (integrable_const (4 : ℝ)) hinner
  simpa [kernelRisk] using h

/-- For [the specified inputs and assumptions](hyp:Z,f,hf), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: boundedMapKernel
noncomputable def boundedMapKernel {Z : Type*} [MeasurableSpace Z]
    (f : Z → Icc (-1 : ℝ) 1) (hf : Measurable f) : BoundedKernel Z :=
  ⟨Kernel.deterministic (fun o => (f o).1) (by fun_prop), inferInstance, by
    intro o
    rw [Kernel.deterministic_apply, Measure.dirac_apply]
    rw [Set.indicator_of_mem (f o).2]
    rfl⟩

/-- Given [the specified inputs and assumptions](hyp:Z,Λ,Q,θ,f,hf,param), [the stated mathematical conclusion holds](goal). -/
-- @node: boundedMapKernel_risk
lemma boundedMapKernel_risk {Z Λ : Type*} [MeasurableSpace Z]
    (Q : Λ → Measure Z) (θ : Λ → ℝ)
    (f : Z → Icc (-1 : ℝ) 1) (hf : Measurable f) (param : Λ) :
    kernelRisk Q θ (boundedMapKernel f hf) param =
      mapRisk Q θ (fun o => (f o).1) param := by
  simp [kernelRisk, mapRisk, boundedMapKernel, Kernel.deterministic_apply]

/-- Given [the specified inputs and assumptions](hyp:Z,Λ,Q,hQ,θ,hθ), [the stated mathematical conclusion holds](goal). -/
-- @node: bounded_kernel_minimax_eq_deterministic
lemma bounded_kernel_minimax_eq_deterministic
    {Z Λ : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Λ → Measure Z) (hQ : ∀ param, IsProbabilityMeasure (Q param))
    (θ : Λ → ℝ) (hθ : ∀ param, θ param ∈ Icc (-1 : ℝ) 1) :
    Causalean.Stat.minimaxValueReal (kernelRisk Q θ) =
      Causalean.Stat.minimaxValueReal
        (fun (f : Z → Icc (-1 : ℝ) 1) param => mapRisk Q θ (fun o => (f o).1) param) := by
  let D : (Z → Icc (-1 : ℝ) 1) → Λ → ℝ :=
    fun f param => mapRisk Q θ (fun o => (f o).1) param
  let z : Z → Icc (-1 : ℝ) 1 := fun _ => ⟨0, by norm_num⟩
  let : Nonempty (Z → Icc (-1 : ℝ) 1) := ⟨z⟩
  let : Nonempty (BoundedKernel Z) := ⟨boundedMapKernel z (by fun_prop)⟩
  have hknonneg : ∀ κ param, 0 ≤ kernelRisk Q θ κ param :=
    fun κ param => (bounded_kernelRisk_bounds Q hQ θ hθ κ param).1
  have hdnonneg : ∀ f param, 0 ≤ D f param :=
    fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  have hkbdd : ∀ κ, BddAbove (range (kernelRisk Q θ κ)) := by
    intro κ
    refine ⟨4, ?_⟩
    rintro _ ⟨param, rfl⟩
    exact (bounded_kernelRisk_bounds Q hQ θ hθ κ param).2
  apply le_antisymm
  · apply Causalean.Stat.minimaxValue_le_minimaxValue
      (Causalean.Stat.bddBelow_range_worstCaseRisk hknonneg)
    intro f
    have hf : Measurable f := by fun_prop
    refine ⟨boundedMapKernel f hf, le_of_eq ?_⟩
    unfold Causalean.Stat.worstCaseRiskReal
    simp_rw [boundedMapKernel_risk]
  · apply Causalean.Stat.minimaxValue_le_minimaxValue
      (Causalean.Stat.bddBelow_range_worstCaseRisk hdnonneg)
    intro κ
    let f : Z → Icc (-1 : ℝ) 1 := fun o => ⟨barycenter κ o, kernel_barycenter_mem κ o⟩
    refine ⟨f, ?_⟩
    exact Causalean.Stat.worstCaseRisk_mono_class_of_nonneg
      (risk := fun (_ : Unit) param => D f param)
      (risk' := fun (_ : Unit) param => kernelRisk Q θ κ param) (e := ())
      id (hkbdd κ) (hknonneg κ) (kernel_barycenter_risk_le Q hQ θ κ)

/-- Given [the specified inputs and assumptions](hyp:h,c,hc), [the stated mathematical conclusion holds](goal). -/
-- @node: realKernelClip_sq_le
lemma realKernelClip_sq_le (h c : ℝ) (hc : c ∈ Icc (-1 : ℝ) 1) :
    (realKernelClip h - c) ^ 2 ≤ (h - c) ^ 2 := by
  obtain ⟨hcl, hcu⟩ := hc
  unfold realKernelClip
  rcases le_total h 1 with hu | hu
  · rw [min_eq_right hu]
    rcases le_total (-1 : ℝ) h with hl | hl
    · rw [max_eq_right hl]
    · rw [max_eq_left hl]
      nlinarith
  · rw [min_eq_left hu, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
    nlinarith

/-- [the stated mathematical conclusion holds](goal). -/
-- @node: measurable_realKernelClip
@[fun_prop] lemma measurable_realKernelClip : Measurable realKernelClip := by
  unfold realKernelClip
  fun_prop

/-- Given [the specified inputs and assumptions](hyp:Z,Λ,Q,θ,hθ,κ,param), [the stated mathematical conclusion holds](goal). -/
-- @node: realKernelClip_risk_le
lemma realKernelClip_risk_le {Z Λ : Type*} [MeasurableSpace Z]
    (Q : Λ → Measure Z) (θ : Λ → ℝ)
    (hθ : ∀ param, θ param ∈ Icc (-1 : ℝ) 1)
    (κ : Kernel Z ℝ) (param : Λ) :
    realKernelRisk Q θ (κ.map realKernelClip) param ≤ realKernelRisk Q θ κ param := by
  apply lintegral_mono
  intro o
  dsimp only
  rw [Kernel.map_apply κ measurable_realKernelClip,
    lintegral_map (by fun_prop) measurable_realKernelClip]
  apply lintegral_mono
  intro h
  exact ENNReal.ofReal_le_ofReal (realKernelClip_sq_le h (θ param) (hθ param))

/-- [the stated mathematical conclusion holds](goal). -/
-- @node: uniformSeedLaw_probability
lemma uniformSeedLaw_probability : IsProbabilityMeasure uniformSeedLaw := by
  constructor
  rw [uniformSeedLaw, Measure.comap_apply Subtype.val Subtype.val_injective
    (fun s hs => (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image.mpr hs)
    _ MeasurableSet.univ]
  rw [image_univ, Subtype.range_coe]
  change volume (Icc (0 : ℝ) 1) = 1
  simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

/-- Given [the specified inputs and assumptions](hyp:Z,f,hf), [the stated mathematical conclusion holds](goal). -/
-- @node: boundedKernel_of_uniformSeed
lemma boundedKernel_of_uniformSeed
    {Z : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (f : Z × UnitSeed → Icc (-1 : ℝ) 1) (hf : Measurable f) :
    ∃ κ : BoundedKernel Z, ∀ o,
      κ.1 o = uniformSeedLaw.map (fun v => (f (o, v)).1) := by
  letI : IsProbabilityMeasure uniformSeedLaw := uniformSeedLaw_probability
  have hm (o : Z) : Measurable (fun v => (f (o, v)).1) := by fun_prop
  let κ : Kernel Z ℝ := ⟨fun o => uniformSeedLaw.map (fun v => (f (o, v)).1),
    measurable_of_finite _⟩
  have hk : IsMarkovKernel κ := ⟨fun o => Measure.isProbabilityMeasure_map (hm o).aemeasurable⟩
  refine ⟨⟨κ, hk, ?_⟩, fun _ => rfl⟩
  intro o
  change uniformSeedLaw.map (fun v => (f (o, v)).1) (Icc (-1 : ℝ) 1) = 1
  rw [Measure.map_apply (hm o) measurableSet_Icc]
  have hpre : (fun v => (f (o, v)).1) ⁻¹' Icc (-1 : ℝ) 1 = univ := by
    ext v
    simp only [mem_preimage, mem_univ, iff_true]
    exact (f (o, v)).2
  rw [hpre, measure_univ]

/-- Given [the specified inputs and assumptions](hyp:h), [the stated mathematical conclusion holds](goal). -/
-- @node: realKernelClip_mem
lemma realKernelClip_mem (h : ℝ) : realKernelClip h ∈ Icc (-1 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Given [the specified inputs and assumptions](hyp:h,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: realKernelClip_eq_self
lemma realKernelClip_eq_self {h : ℝ} (hh : h ∈ Icc (-1 : ℝ) 1) :
    realKernelClip h = h := by
  exact (congrArg (max (-1)) (min_eq_right hh.2)).trans (max_eq_right hh.1)

/-- Given [the specified inputs and assumptions](hyp:Z,κ,o), [the stated mathematical conclusion holds](goal). -/
-- @node: boundedKernel_map_clip
lemma boundedKernel_map_clip {Z : Type*} [MeasurableSpace Z]
    (κ : BoundedKernel Z) (o : Z) : (κ.1 o).map realKernelClip = κ.1 o := by
  letI : IsMarkovKernel κ.1 := κ.2.1
  have hb : ∀ᵐ h ∂(κ.1 o), h ∈ Icc (-1 : ℝ) 1 :=
    (ae_mem_iff_measure_eq (μ := κ.1 o) measurableSet_Icc.nullMeasurableSet).2
      (by simpa only [measure_univ] using κ.2.2 o)
  calc
    (κ.1 o).map realKernelClip = (κ.1 o).map id :=
      Measure.map_congr (hb.mono fun _ hh => realKernelClip_eq_self hh)
    _ = κ.1 o := Measure.map_id

/-- Given [the specified inputs and assumptions](hyp:Z,κ), [the stated mathematical conclusion holds](goal). -/
-- @node: boundedKernel_uniformSeed_representation
lemma boundedKernel_uniformSeed_representation
    {Z : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (κ : BoundedKernel Z) :
    ∃ f : Z × UnitSeed → Icc (-1 : ℝ) 1,
      Measurable f ∧ ∀ o, κ.1 o = uniformSeedLaw.map (fun v => (f (o, v)).1) := by
  letI : IsMarkovKernel κ.1 := κ.2.1
  obtain ⟨g, hg, hmap⟩ := κ.1.exists_measurable_map_eq_unitInterval
  let f : Z × UnitSeed → Icc (-1 : ℝ) 1 :=
    fun p => ⟨realKernelClip (g p.1 p.2), realKernelClip_mem _⟩
  have hf : Measurable f := by fun_prop
  refine ⟨f, hf, fun o => ?_⟩
  have hgo : Measurable (g o) := by fun_prop
  change κ.1 o = (volume : Measure UnitSeed).map (realKernelClip ∘ g o)
  rw [← Measure.map_map measurable_realKernelClip hgo, hmap o,
    boundedKernel_map_clip]

/-- For [the specified inputs and assumptions](hyp:Z,κ,hk), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: clippedRealKernel
noncomputable def clippedRealKernel {Z : Type*} [MeasurableSpace Z]
    (κ : Kernel Z ℝ) (hk : IsMarkovKernel κ) : BoundedKernel Z := by
  letI : IsMarkovKernel κ := hk
  refine ⟨κ.map realKernelClip, Kernel.IsMarkovKernel.map κ measurable_realKernelClip, fun o => ?_⟩
  rw [Kernel.map_apply κ measurable_realKernelClip,
    Measure.map_apply measurable_realKernelClip measurableSet_Icc]
  have hpre : realKernelClip ⁻¹' Icc (-1 : ℝ) 1 = univ := by
    ext h
    simp only [mem_preimage, mem_univ, iff_true]
    exact realKernelClip_mem h
  rw [hpre, measure_univ]

/-- Given [the specified inputs and assumptions](hyp:Z,Λ,Q,hQ,θ,κ,param), [the stated mathematical conclusion holds](goal). -/
-- @node: bounded_realKernelRisk_eq_ofReal
lemma bounded_realKernelRisk_eq_ofReal
    {Z Λ : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Λ → Measure Z) (hQ : ∀ param, IsProbabilityMeasure (Q param))
    (θ : Λ → ℝ) (κ : BoundedKernel Z) (param : Λ) :
    realKernelRisk Q θ κ.1 param = ENNReal.ofReal (kernelRisk Q θ κ param) := by
  letI : IsProbabilityMeasure (Q param) := hQ param
  letI : IsMarkovKernel κ.1 := κ.2.1
  have hi (o : Z) : Integrable (fun h => (h - θ param) ^ 2) (κ.1 o) := by
    have hb : ∀ᵐ h ∂(κ.1 o), h ∈ Icc (-1 : ℝ) 1 :=
      (ae_mem_iff_measure_eq (μ := κ.1 o) measurableSet_Icc.nullMeasurableSet).2
        (by simpa only [measure_univ] using κ.2.2 o)
    have hm : AEStronglyMeasurable (fun h : ℝ => h) (κ.1 o) := by fun_prop
    exact ((memLp_of_bounded hb hm 2).sub (memLp_const (θ param))).integrable_sq
  unfold realKernelRisk kernelRisk
  rw [ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (Filter.Eventually.of_forall fun o => integral_nonneg fun h => sq_nonneg _)]
  apply lintegral_congr
  intro o
  exact (ofReal_integral_eq_lintegral_ofReal (hi o)
    (Filter.Eventually.of_forall fun h => sq_nonneg (h - θ param))).symm

/-- Given [the specified inputs and assumptions](hyp:Z,Λ,Q,hQ,θ,hθ), [the stated mathematical conclusion holds](goal). -/
-- @node: real_kernel_minimax_eq_bounded
lemma real_kernel_minimax_eq_bounded
    {Z Λ : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Λ → Measure Z) (hQ : ∀ param, IsProbabilityMeasure (Q param))
    (θ : Λ → ℝ) (hθ : ∀ param, θ param ∈ Icc (-1 : ℝ) 1) :
    (⨅ κ : {κ : Kernel Z ℝ // IsMarkovKernel κ},
      ⨆ param : Λ, realKernelRisk Q θ κ.1 param).toReal =
        Causalean.Stat.minimaxValueReal (kernelRisk Q θ) := by
  have heq : (⨅ κ : {κ : Kernel Z ℝ // IsMarkovKernel κ},
      ⨆ param : Λ, realKernelRisk Q θ κ.1 param) =
      Causalean.Stat.minimaxValueENNRealOfReal (kernelRisk Q θ) := by
    apply le_antisymm
    · apply le_iInf
      intro κ
      refine (iInf_le _ ⟨κ.1, κ.2.1⟩).trans ?_
      apply iSup_le
      intro param
      rw [bounded_realKernelRisk_eq_ofReal Q hQ]
      exact le_iSup (fun param => ENNReal.ofReal (kernelRisk Q θ κ param)) param
    · apply le_iInf
      intro κ
      let b := clippedRealKernel κ.1 κ.2
      change (⨅ b : BoundedKernel Z, ⨆ param, ENNReal.ofReal (kernelRisk Q θ b param)) ≤ _
      refine (iInf_le _ b).trans ?_
      apply iSup_le
      intro param
      rw [← bounded_realKernelRisk_eq_ofReal Q hQ]
      exact (realKernelClip_risk_le Q θ hθ κ.1 param).trans
        (le_iSup (realKernelRisk Q θ κ.1) param)
  rw [heq]
  apply Causalean.Stat.minimaxValueENNRealOfReal_toReal_of_nonneg_of_bddAbove
  · exact fun κ param => (bounded_kernelRisk_bounds Q hQ θ hθ κ param).1
  · intro κ
    refine ⟨4, ?_⟩
    rintro _ ⟨param, rfl⟩
    exact (bounded_kernelRisk_bounds Q hQ θ hθ κ param).2

/-- Given [the specified inputs and assumptions](hyp:Z,Λ,Q,hQ,θ,hθ), [the stated mathematical conclusion holds](goal). -/
-- @node: lem:randomized-kernel-barycenter
lemma randomized_kernel_barycenter
    {Z Λ : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : Λ → Measure Z) (hQ : ∀ param, IsProbabilityMeasure (Q param))
    (θ : Λ → ℝ) (hθ : ∀ param, θ param ∈ Icc (-1 : ℝ) 1) :
    (∀ κ : BoundedKernel Z, ∀ o, barycenter κ o ∈ Icc (-1 : ℝ) 1) ∧
    (∀ (κ : BoundedKernel Z) (param : Λ),
      mapRisk Q θ (barycenter κ) param ≤ kernelRisk Q θ κ param) ∧
    Causalean.Stat.minimaxValueReal (kernelRisk Q θ) =
      Causalean.Stat.minimaxValueReal
        (fun (f : Z → Icc (-1 : ℝ) 1) param => mapRisk Q θ (fun o => (f o).1) param) ∧
    (∀ (κ : Kernel Z ℝ), IsMarkovKernel κ → ∀ param,
      realKernelRisk Q θ (κ.map realKernelClip) param ≤ realKernelRisk Q θ κ param) ∧
    (⨅ κ : {κ : Kernel Z ℝ // IsMarkovKernel κ},
      ⨆ param : Λ, realKernelRisk Q θ κ.1 param).toReal =
        Causalean.Stat.minimaxValueReal (kernelRisk Q θ) ∧
    IsProbabilityMeasure uniformSeedLaw ∧
    (∀ κ : BoundedKernel Z, ∃ f : Z × UnitSeed → Icc (-1 : ℝ) 1,
      Measurable f ∧ ∀ o, κ.1 o = uniformSeedLaw.map (fun v => (f (o, v)).1)) ∧
    (∀ f : Z × UnitSeed → Icc (-1 : ℝ) 1, Measurable f →
      ∃ κ : BoundedKernel Z, ∀ o,
        κ.1 o = uniformSeedLaw.map (fun v => (f (o, v)).1)) := by
  refine ⟨kernel_barycenter_mem, kernel_barycenter_risk_le Q hQ θ,
    bounded_kernel_minimax_eq_deterministic Q hQ θ hθ, ?_⟩
  refine ⟨fun κ _ param => realKernelClip_risk_le Q θ hθ κ param, ?_,
    uniformSeedLaw_probability, ?_, ?_⟩
  · exact real_kernel_minimax_eq_bounded Q hQ θ hθ
  · exact boundedKernel_uniformSeed_representation
  · exact boundedKernel_of_uniformSeed

/-- Given [the specified inputs and assumptions](hyp:Z,H,Q₀,Q₁,κ), [the stated mathematical conclusion holds](goal). -/
-- @node: lem:randomized-kernel-tv-comparison
lemma randomized_kernel_tv_comparison
    {Z H : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace H] (Q₀ Q₁ : Measure Z)
    [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (κ : Kernel Z H) [IsMarkovKernel κ] :
    Causalean.Stat.tvDist (κ ∘ₘ Q₀) (κ ∘ₘ Q₁) ≤
      Causalean.Stat.tvDist (Q₀ ⊗ₘ κ) (Q₁ ⊗ₘ κ) ∧
    Causalean.Stat.tvDist (Q₀ ⊗ₘ κ) (Q₁ ⊗ₘ κ) = Causalean.Stat.tvDist Q₀ Q₁ ∧
    (∀ T : Set (Z × H), MeasurableSet T →
      1 - Causalean.Stat.tvDist Q₀ Q₁ ≤ (Q₀ ⊗ₘ κ).real T + (Q₁ ⊗ₘ κ).real Tᶜ) ∧
    (∀ T : Set H, MeasurableSet T →
      1 - Causalean.Stat.tvDist Q₀ Q₁ ≤ (κ ∘ₘ Q₀).real T + (κ ∘ₘ Q₁).real Tᶜ) := by
  exact ⟨Causalean.Stat.tvDist_bind_le_compProd Q₀ Q₁ κ,
    Causalean.Stat.tvDist_compProd_eq Q₀ Q₁ κ,
    Causalean.Stat.one_sub_tvDist_le_compProd_test Q₀ Q₁ κ,
    Causalean.Stat.one_sub_tvDist_le_bind_test Q₀ Q₁ κ⟩


end CausalSmith.Stat.MarRareqLogfrontier
