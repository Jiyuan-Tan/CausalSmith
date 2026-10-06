module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairFiberMeans
public import Causalean.Mathlib.MeasureTheory.IntegralBind

/-! # Conditional nuisance versions of the binary witness

Recording the covariate in every fibre lets the pointwise means in (15)--(16)
of the membership roadmap identify the conditional expectations of the full law.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory

/-- A recorded-base mixture has the prescribed mean on every measurable base event. -/
-- @node: setIntegral_bind_recording
lemma setIntegral_bind_recording {X Y : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) (base : Y → X)
    (hκ : Measurable κ) (hb : Measurable base)
    (hr : ∀ᵐ x ∂μ, (κ x).map base = Measure.dirac x)
    (f : Y → ℝ) (hf : Integrable f (μ.bind κ))
    (B : Set X) (hB : MeasurableSet B) :
    (∫ y in base ⁻¹' B, f y ∂μ.bind κ) =
      ∫ x in B, (∫ y, f y ∂κ x) ∂μ := by
  rw [← integral_indicator (hB.preimage hb)]
  rw [Causalean.Mathlib.MeasureTheory.integral_bind hκ (hf.indicator (hB.preimage hb))]
  rw [← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [hr] with x hx
  have hbase : ∀ᵐ y ∂κ x, base y = x := by
    apply ae_of_ae_map (μ := κ x) (p := fun z => z = x) hb.aemeasurable
    rw [hx]
    simp
  calc
    (∫ y, (base ⁻¹' B).indicator f y ∂κ x) =
        ∫ y, B.indicator (fun _ => f y) x ∂κ x := by
      apply integral_congr_ae
      filter_upwards [hbase] with y hy
      by_cases hxB : x ∈ B
      · have hyB : y ∈ base ⁻¹' B := by
          change base y ∈ B
          rw [hy]
          exact hxB
        rw [Set.indicator_of_mem hyB,
          Set.indicator_of_mem hxB]
      · rw [Set.indicator_of_notMem (show y ∉ base ⁻¹' B from fun h => hxB (hy ▸ h)),
          Set.indicator_of_notMem hxB]
    _ = B.indicator (fun x => ∫ y, f y ∂κ x) x := by
      by_cases hxB : x ∈ B <;> simp [Set.indicator, hxB]

/-- A measurable fibre mean in a recorded-base mixture is its conditional expectation. -/
-- @node: condExp_bind_recording
lemma condExp_bind_recording {X Y : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) (base : Y → X)
    [IsFiniteMeasure (μ.bind κ)]
    (hκ : Measurable κ) (hb : Measurable base)
    (hr : ∀ᵐ x ∂μ, (κ x).map base = Measure.dirac x)
    (f : Y → ℝ) (hf : Integrable f (μ.bind κ))
    (g : X → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun y => g (base y)) (μ.bind κ))
    (hmean : ∀ᵐ x ∂μ, (∫ y, f y ∂κ x) = g x) :
    (μ.bind κ)[f | MeasurableSpace.comap base inferInstance] =ᵐ[μ.bind κ]
      fun y => g (base y) := by
  have hm := hb.comap_le
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
  · intro s hs hfin
    exact hgi.integrableOn
  · intro s hs hfin
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [setIntegral_bind_recording μ κ base hκ hb hr _ hgi B hB,
      setIntegral_bind_recording μ κ base hκ hb hr _ hf B hB]
    apply setIntegral_congr_ae hB
    filter_upwards [hr, hmean] with x hx hmx hxB
    rw [← integral_map_of_stronglyMeasurable hb hg.stronglyMeasurable, hx,
      integral_dirac]
    exact hmx.symm
  · exact (hg.comp (comap_measurable base)).stronglyMeasurable.aestronglyMeasurable

/-- Each normalized witness fibre records its input covariate exactly. -/
-- @node: lowerPair_fiber_xLaw
lemma lowerPair_fiber_xLaw (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))).map Prod.fst = Measure.dirac x := by
  let ν : Measure (Full d) := (treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure (binaryMeasure M
      (treatedPlusProbability d β δ h M sign x)) :=
    binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have heq := lowerPair_fiber_jointTreated d β q h δ M hd hq sign x hx
  have hm := congrArg (fun μ : Measure ((Fin d → ℝ) × ℝ) => μ.map Prod.fst) heq
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hm
  change ν.map Prod.fst = _ at hm
  change ν.map Prod.fst = _
  rw [hm]
  change (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
    (fun _ => x) = _
  rw [Measure.map_const, measure_univ, one_smul]

variable (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool)
include hd hq hβ hδ hh hh1 hM hsmall


/-- The recorded treated version is the conditional mean under the full witness law. -/
-- @node: lowerPair_condExp_treated
lemma lowerPair_condExp_treated :
    (lowerPair d β q h δ M sign).full[(fun u : Full d => u.2.2.2) |
      MeasurableSpace.comap (fun u : Full d => u.1) inferInstance] =ᵐ[
        (lowerPair d β q h δ M sign).full]
      fun u => witnessMean d β δ h sign u.1 := by
  let κ (x : Fin d → ℝ) : Measure (Full d) := (treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))
  have hκ : Measurable κ := lowerPair_fullKernel_measurable d β q h δ M hq sign
  have hr : ∀ᵐ x ∂volume.restrict (cube d), (κ x).map Prod.fst = Measure.dirac x := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact lowerPair_fiber_xLaw d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure ((volume.restrict (cube d)).bind κ) :=
    lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have : IsProbabilityMeasure (lowerPair d β q h δ M sign).full :=
    lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have hf := lowerPair_integrable_treated d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have hg : Measurable (witnessMean d β δ h sign) := by fun_prop
  have hgi : Integrable (fun u : Full d => (witnessMean d β δ h sign) u.1)
      (lowerPair d β q h δ M sign).full := by
    apply Integrable.of_bound (hg.comp measurable_fst).aestronglyMeasurable M
    have hu := lowerPair_uniformDesign d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
    have hc : ∀ᵐ x ∂(lowerPair d β q h δ M sign).xLaw, x ∈ cube d := by
      rw [hu]
      exact ae_restrict_mem (by simp [cube])
    have hc' := ae_of_ae_map measurable_fst.aemeasurable hc
    filter_upwards [hc'] with u hu
    have hrange := (lowerPair_regression_ranges d β q h δ M hβ hδ hh hh1 hM hsmall sign).1 u.1 hu
    exact (abs_le.mpr hrange : |witnessMean d β δ h sign u.1| ≤ M)
  change ((volume.restrict (cube d)).bind κ)[(fun u : Full d => u.2.2.2) | _] =ᵐ[_] _
  apply condExp_bind_recording (volume.restrict (cube d)) κ Prod.fst hκ measurable_fst hr
    (fun u : Full d => u.2.2.2) hf (witnessMean d β δ h sign) hg hgi
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact lowerPair_fiber_treated_mean d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx

/-- The recorded control version is the conditional mean under the full witness law. -/
-- @node: lowerPair_condExp_control
lemma lowerPair_condExp_control :
    (lowerPair d β q h δ M sign).full[(fun u : Full d => u.2.2.1) |
      MeasurableSpace.comap (fun u : Full d => u.1) inferInstance] =ᵐ[
        (lowerPair d β q h δ M sign).full] fun _ => (0 : ℝ) := by
  let κ (x : Fin d → ℝ) : Measure (Full d) := (treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))
  have hκ : Measurable κ := lowerPair_fullKernel_measurable d β q h δ M hq sign
  have hr : ∀ᵐ x ∂volume.restrict (cube d), (κ x).map Prod.fst = Measure.dirac x := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact lowerPair_fiber_xLaw d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure ((volume.restrict (cube d)).bind κ) :=
    lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have : IsProbabilityMeasure (lowerPair d β q h δ M sign).full :=
    lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have hf := lowerPair_integrable_control d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have hg : Measurable (fun _ : Fin d → ℝ => (0 : ℝ)) := by fun_prop
  have hgi : Integrable (fun u : Full d => (fun _ : Fin d → ℝ => (0 : ℝ)) u.1)
      (lowerPair d β q h δ M sign).full := by
    apply Integrable.of_bound (hg.comp measurable_fst).aestronglyMeasurable 0
    exact Filter.Eventually.of_forall (fun _ => by simp)
  change ((volume.restrict (cube d)).bind κ)[(fun u : Full d => u.2.2.1) | _] =ᵐ[_] _
  apply condExp_bind_recording (volume.restrict (cube d)) κ Prod.fst hκ measurable_fst hr
    (fun u : Full d => u.2.2.1) hf (fun _ : Fin d → ℝ => (0 : ℝ)) hg hgi
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact lowerPair_fiber_control_mean d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx

/-- The recorded treatment version is the conditional mean under the full witness law. -/
-- @node: lowerPair_condExp_treatment
lemma lowerPair_condExp_treatment :
    (lowerPair d β q h δ M sign).full[
      (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) |
      MeasurableSpace.comap (fun u : Full d => u.1) inferInstance] =ᵐ[
        (lowerPair d β q h δ M sign).full] fun u => (baselinePropensity d q) u.1 := by
  let κ (x : Fin d → ℝ) : Measure (Full d) := (treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))
  have hκ : Measurable κ := lowerPair_fullKernel_measurable d β q h δ M hq sign
  have hr : ∀ᵐ x ∂volume.restrict (cube d), (κ x).map Prod.fst = Measure.dirac x := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact lowerPair_fiber_xLaw d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure ((volume.restrict (cube d)).bind κ) :=
    lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have : IsProbabilityMeasure (lowerPair d β q h δ M sign).full :=
    lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have hf := lowerPair_integrable_treatment d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have hg : Measurable (baselinePropensity d q) := baselinePropensity_measurable d q hq
  have hgi : Integrable (fun u : Full d => (baselinePropensity d q) u.1)
      (lowerPair d β q h δ M sign).full := by
    apply Integrable.of_bound (hg.comp measurable_fst).aestronglyMeasurable 1
    have hu := lowerPair_uniformDesign d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
    have hc : ∀ᵐ x ∂(lowerPair d β q h δ M sign).xLaw, x ∈ cube d := by
      rw [hu]
      exact ae_restrict_mem (by simp [cube])
    have hc' := ae_of_ae_map measurable_fst.aemeasurable hc
    filter_upwards [hc'] with u hu
    have hrange := baselinePropensity_unit_interval d q hd hq u.1 hu
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hrange.1] using hrange.2
  change ((volume.restrict (cube d)).bind κ)[
    (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) | _] =ᵐ[_] _
  apply condExp_bind_recording (volume.restrict (cube d)) κ Prod.fst hκ measurable_fst hr
    (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) hf (baselinePropensity d q) hg hgi
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact lowerPair_fiber_treatment_mean d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx

/-- Both outcome regressions and the propensity are the conditional-law versions
required by the model class, with their stipulated cube ranges. -/
-- @node: lowerPair_lawSemantics
lemma lowerPair_lawSemantics : LawSemantics (lowerPair d β q h δ M sign) M := by
  have hranges := lowerPair_regression_ranges d β q h δ M hβ hδ hh hh1 hM hsmall sign
  refine ⟨lowerPair_condExp_treatment d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign,
    lowerPair_condExp_treated d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign,
    lowerPair_condExp_control d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign,
    ?_, hranges.1, hranges.2⟩
  intro x hx
  exact baselinePropensity_unit_interval d q hd hq x hx

end CausalSmith.Stat.GlobalTailDesignRobustCate
