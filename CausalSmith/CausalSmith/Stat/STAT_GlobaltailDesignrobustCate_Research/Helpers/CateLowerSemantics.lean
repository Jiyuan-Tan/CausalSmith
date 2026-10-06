module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CateLowerSampling
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairSemantics

/-! # Conditional means of the compatible CATE witnesses

Roadmap (C27): the normalized binary outcome channel and independent treatment
channel give the prescribed treated mean and propensity conditional on covariates.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory

variable (d : ℕ) (β q s h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool)
include hd hq hs hs1 hβ hδ hh hh1 hM hsmall

-- @node: cateLowerPair_fiber_xLaw
lemma cateLowerPair_fiber_xLaw (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1)))).map Prod.fst = Measure.dirac x := by
  let ν (a : Bool) : Measure (Full d) :=
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun y1 => (x, a, (0 : ℝ), y1))
  have hν : Measurable ν := by
    simpa only [Function.comp_def] using
      (lowerPair_outcomeMap_measurable d β δ h M sign).comp
        (show Measurable (fun a : Bool => (x, a, (0 : ℝ))) from by fun_prop)
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  haveI : IsProbabilityMeasure (binaryMeasure M
      (treatedPlusProbability d β δ h M sign x)) :=
    binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have he := cateLowerPropensity_bounds d q s hd hq hs x hx
  haveI : IsProbabilityMeasure (treatmentMeasure (cateLowerPropensity d q s x)) :=
    treatmentMeasure_isProbabilityMeasure _ ⟨he.1, he.2.trans hs1⟩
  change ((treatmentMeasure (cateLowerPropensity d q s x)).bind ν).map Prod.fst = _
  rw [map_bind_channel _ _ _ hν (by fun_prop)]
  have hlast (a : Bool) : (ν a).map Prod.fst = Measure.dirac x := by
    dsimp [ν]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, Prod.fst, Prod.snd]
    rw [Measure.map_const, measure_univ, one_smul]
  simp_rw [hlast]
  rw [Measure.bind_const, measure_univ, one_smul]

-- @node: cateLowerPair_fiber_treatedLaw
lemma cateLowerPair_fiber_treatedLaw (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1)))).map (fun u : Full d => u.2.2.2) = binaryMeasure M (treatedPlusProbability d β δ h M sign x) := by
  let ν (a : Bool) : Measure (Full d) :=
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun y1 => (x, a, (0 : ℝ), y1))
  have hν : Measurable ν := by
    simpa only [Function.comp_def] using
      (lowerPair_outcomeMap_measurable d β δ h M sign).comp
        (show Measurable (fun a : Bool => (x, a, (0 : ℝ))) from by fun_prop)
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  haveI : IsProbabilityMeasure (binaryMeasure M
      (treatedPlusProbability d β δ h M sign x)) :=
    binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have he := cateLowerPropensity_bounds d q s hd hq hs x hx
  haveI : IsProbabilityMeasure (treatmentMeasure (cateLowerPropensity d q s x)) :=
    treatmentMeasure_isProbabilityMeasure _ ⟨he.1, he.2.trans hs1⟩
  change ((treatmentMeasure (cateLowerPropensity d q s x)).bind ν).map (fun u : Full d => u.2.2.2) = _
  rw [map_bind_channel _ _ _ hν (by fun_prop)]
  have hlast (a : Bool) : (ν a).map (fun u : Full d => u.2.2.2) = binaryMeasure M (treatedPlusProbability d β δ h M sign x) := by
    dsimp [ν]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id
  simp_rw [hlast]
  rw [Measure.bind_const, measure_univ, one_smul]

-- @node: cateLowerPair_fiber_treatmentLaw
lemma cateLowerPair_fiber_treatmentLaw (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1)))).map (fun u : Full d => u.2.1) = treatmentMeasure (cateLowerPropensity d q s x) := by
  let ν (a : Bool) : Measure (Full d) :=
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun y1 => (x, a, (0 : ℝ), y1))
  have hν : Measurable ν := by
    simpa only [Function.comp_def] using
      (lowerPair_outcomeMap_measurable d β δ h M sign).comp
        (show Measurable (fun a : Bool => (x, a, (0 : ℝ))) from by fun_prop)
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  haveI : IsProbabilityMeasure (binaryMeasure M
      (treatedPlusProbability d β δ h M sign x)) :=
    binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have he := cateLowerPropensity_bounds d q s hd hq hs x hx
  haveI : IsProbabilityMeasure (treatmentMeasure (cateLowerPropensity d q s x)) :=
    treatmentMeasure_isProbabilityMeasure _ ⟨he.1, he.2.trans hs1⟩
  change ((treatmentMeasure (cateLowerPropensity d q s x)).bind ν).map (fun u : Full d => u.2.1) = _
  rw [map_bind_channel _ _ _ hν (by fun_prop)]
  have hlast (a : Bool) : (ν a).map (fun u : Full d => u.2.1) = Measure.dirac a := by
    dsimp [ν]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, Prod.fst, Prod.snd]
    rw [Measure.map_const, measure_univ, one_smul]
  simp_rw [hlast]
  exact Measure.bind_dirac

-- @node: cateLowerPair_fiber_treated_mean
lemma cateLowerPair_fiber_treated_mean (x : Fin d → ℝ) (hx : x ∈ cube d) :
    (∫ u : Full d, u.2.2.2 ∂((treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1))))) =
      witnessMean d β δ h sign x := by
  have hm : StronglyMeasurable (fun y : ℝ => y) := by
    fun_prop
  rw [← integral_map_of_stronglyMeasurable (φ := (fun u : Full d => u.2.2.2)) (by fun_prop) hm]
  rw [cateLowerPair_fiber_treatedLaw d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign x hx]
  exact treatedBinary_mean d β δ h M hβ hδ hh hh1 hM hsmall sign x hx

-- @node: cateLowerPair_fiber_treatment_mean
lemma cateLowerPair_fiber_treatment_mean (x : Fin d → ℝ) (hx : x ∈ cube d) :
    (∫ u : Full d, if u.2.1 then (1 : ℝ) else 0 ∂((treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1))))) =
      cateLowerPropensity d q s x := by
  have hm : StronglyMeasurable (fun a : Bool => if a then (1 : ℝ) else 0) := by
    apply Measurable.stronglyMeasurable
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_singleton true
  rw [← integral_map_of_stronglyMeasurable (φ := (fun u : Full d => u.2.1)) (by fun_prop) hm]
  rw [cateLowerPair_fiber_treatmentLaw d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign x hx]
  have he := cateLowerPropensity_bounds d q s hd hq hs x hx
  exact treatmentMeasure_integral_indicator _ ⟨he.1, he.2.trans hs1⟩

-- @node: cateLowerPair_condExp_treated
lemma cateLowerPair_condExp_treated :
    (cateLowerPair d β q s h δ M sign).full[(fun u : Full d => u.2.2.2) |
      MeasurableSpace.comap (fun u : Full d => u.1) inferInstance] =ᵐ[
        (cateLowerPair d β q s h δ M sign).full]
      fun u => witnessMean d β δ h sign u.1 := by
  let κ (x : Fin d → ℝ) : Measure (Full d) := (treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, (0 : ℝ), y1)))
  have hκ : Measurable κ := cateLowerPair_fullKernel_measurable d β q s h δ M hq sign
  have hr : ∀ᵐ x ∂volume.restrict (cube d), (κ x).map Prod.fst = Measure.dirac x := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact cateLowerPair_fiber_xLaw d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure ((volume.restrict (cube d)).bind κ) :=
    cateLowerPair_isProbabilityMeasure d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  have : IsProbabilityMeasure (cateLowerPair d β q s h δ M sign).full :=
    cateLowerPair_isProbabilityMeasure d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  have hf := cateLowerPair_integrable_treated d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  have hg : Measurable (witnessMean d β δ h sign) := by fun_prop
  have hgi : Integrable (fun u : Full d => (witnessMean d β δ h sign) u.1)
      (cateLowerPair d β q s h δ M sign).full := by
    apply Integrable.of_bound (hg.comp measurable_fst).aestronglyMeasurable M
    have hu := cateLowerPair_uniformDesign d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
    have hc : ∀ᵐ x ∂(cateLowerPair d β q s h δ M sign).xLaw, x ∈ cube d := by
      rw [hu]
      exact ae_restrict_mem (by simp [cube])
    have hc' := ae_of_ae_map measurable_fst.aemeasurable hc
    filter_upwards [hc'] with u hu
    have hrange := (cateLowerPair_regression_ranges d β q s h δ M hβ hδ hh hh1 hM hsmall sign).1 u.1 hu
    exact (abs_le.mpr hrange : |witnessMean d β δ h sign u.1| ≤ M)
  change ((volume.restrict (cube d)).bind κ)[(fun u : Full d => u.2.2.2) | _] =ᵐ[_] _
  apply condExp_bind_recording (volume.restrict (cube d)) κ Prod.fst hκ measurable_fst hr
    (fun u : Full d => u.2.2.2) hf (witnessMean d β δ h sign) hg hgi
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact cateLowerPair_fiber_treated_mean d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign x hx


-- @node: cateLowerPair_condExp_treatment
lemma cateLowerPair_condExp_treatment :
    (cateLowerPair d β q s h δ M sign).full[
      (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) |
      MeasurableSpace.comap (fun u : Full d => u.1) inferInstance] =ᵐ[
        (cateLowerPair d β q s h δ M sign).full] fun u => (cateLowerPropensity d q s) u.1 := by
  let κ (x : Fin d → ℝ) : Measure (Full d) := (treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, (0 : ℝ), y1)))
  have hκ : Measurable κ := cateLowerPair_fullKernel_measurable d β q s h δ M hq sign
  have hr : ∀ᵐ x ∂volume.restrict (cube d), (κ x).map Prod.fst = Measure.dirac x := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact cateLowerPair_fiber_xLaw d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure ((volume.restrict (cube d)).bind κ) :=
    cateLowerPair_isProbabilityMeasure d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  have : IsProbabilityMeasure (cateLowerPair d β q s h δ M sign).full :=
    cateLowerPair_isProbabilityMeasure d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  have hf := cateLowerPair_integrable_treatment d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  have hg : Measurable (cateLowerPropensity d q s) := cateLowerPropensity_measurable d q s hq
  have hgi : Integrable (fun u : Full d => (cateLowerPropensity d q s) u.1)
      (cateLowerPair d β q s h δ M sign).full := by
    apply Integrable.of_bound (hg.comp measurable_fst).aestronglyMeasurable 1
    have hu := cateLowerPair_uniformDesign d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
    have hc : ∀ᵐ x ∂(cateLowerPair d β q s h δ M sign).xLaw, x ∈ cube d := by
      rw [hu]
      exact ae_restrict_mem (by simp [cube])
    have hc' := ae_of_ae_map measurable_fst.aemeasurable hc
    filter_upwards [hc'] with u hu
    have hrange := cateLowerPropensity_bounds d q s hd hq hs u.1 hu
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hrange.1] using hrange.2.trans hs1
  change ((volume.restrict (cube d)).bind κ)[
    (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) | _] =ᵐ[_] _
  apply condExp_bind_recording (volume.restrict (cube d)) κ Prod.fst hκ measurable_fst hr
    (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) hf (cateLowerPropensity d q s) hg hgi
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact cateLowerPair_fiber_treatment_mean d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign x hx


/-- All selected nuisance versions agree with the conditional law in (C27). -/
-- @node: cateLowerPair_lawSemantics
lemma cateLowerPair_lawSemantics : LawSemantics (cateLowerPair d β q s h δ M sign) M := by
  have hranges := cateLowerPair_regression_ranges d β q s h δ M hβ hδ hh hh1 hM hsmall sign
  refine ⟨cateLowerPair_condExp_treatment d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign,
    cateLowerPair_condExp_treated d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign,
    cateLowerPair_condExp_control d β q s h δ M sign, ?_, hranges.1, hranges.2⟩
  intro x hx
  have he := cateLowerPropensity_bounds d q s hd hq hs x hx
  exact ⟨he.1, he.2.trans hs1⟩

/-- The calibrated propensity is measurable and takes valid probability values. -/
-- @node: cateLowerPair_measurablePropensity
lemma cateLowerPair_measurablePropensity :
    MeasurablePropensity (cateLowerPair d β q s h δ M sign) := by
  constructor
  · change Measurable (fun x : cube d => cateLowerPropensity d q s x)
    exact (cateLowerPropensity_measurable d q s hq).comp measurable_subtype_coe
  · intro x hx
    have he := cateLowerPropensity_bounds d q s hd hq hs x hx
    exact ⟨he.1, he.2.trans hs1⟩

end CausalSmith.Stat.GlobalTailDesignRobustCate
