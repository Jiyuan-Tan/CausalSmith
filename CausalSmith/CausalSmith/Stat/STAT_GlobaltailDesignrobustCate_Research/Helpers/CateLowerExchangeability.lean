module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CateLowerSemantics
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairExchangeability

/-! # Exchangeability of the compatible zero-control witnesses

Roadmap (C27): each covariate fibre records independent treatment and treated
outcome draws, with deterministic zero control. Fibre independence lifts to
joint conditional exchangeability under the uniform mixture. Together with
the existing regularity and tail checks, this proves zero-control CATE-class
membership for a uniform positive amplitude threshold.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory ProbabilityTheory

/-- Each compatible fibre is a recorded product of its two random draws. -/
-- @node: cateLowerPair_fiber_eq_product
lemma cateLowerPair_fiber_eq_product (d : ℕ) (β q s h δ M : ℝ)
    (sign : Bool) (x : Fin d → ℝ) :
    (treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1))) =
    ((treatmentMeasure (cateLowerPropensity d q s x)).prod
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x))).map
        (fun z => (x, z.1, (0 : ℝ), z.2)) := by
  have : IsFiniteMeasure
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)) := by
    constructor
    simp [binaryMeasure, ENNReal.add_lt_top]
  exact bind_map_eq_recorded_product (treatmentMeasure (cateLowerPropensity d q s x))
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x))
    (fun z : Bool × ℝ => (x, z.1, (0 : ℝ), z.2)) (by fun_prop)

section
variable (d : ℕ) (β q s h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool)
include hd hq hs hs1 hβ hδ hh hh1 hM hsmall

/-- The recorded independent draws give a probability measure in each cube fibre. -/
-- @node: cateLowerPair_fiber_isProbabilityMeasure
lemma cateLowerPair_fiber_isProbabilityMeasure (x : Fin d → ℝ) (hx : x ∈ cube d) :
    IsProbabilityMeasure ((treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1)))) := by
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  haveI := binaryMeasure_isProbabilityMeasure M
    (treatedPlusProbability d β δ h M sign x) ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have he := cateLowerPropensity_bounds d q s hd hq hs x hx
  haveI := treatmentMeasure_isProbabilityMeasure _ ⟨he.1, he.2.trans hs1⟩
  rw [cateLowerPair_fiber_eq_product]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The joint pair of potential outcomes is independent of treatment in each fibre. -/
-- @node: cateLowerPair_fiber_indepFun
lemma cateLowerPair_fiber_indepFun (x : Fin d → ℝ) (hx : x ∈ cube d) :
    IndepFun (fun u : Full d => u.2.2) (fun u : Full d => u.2.1)
      ((treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, (0 : ℝ), y1)))) := by
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  haveI := binaryMeasure_isProbabilityMeasure M
    (treatedPlusProbability d β δ h M sign x) ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have he := cateLowerPropensity_bounds d q s hd hq hs x hx
  haveI := treatmentMeasure_isProbabilityMeasure _ ⟨he.1, he.2.trans hs1⟩
  rw [cateLowerPair_fiber_eq_product]
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro a b ha hb
  rw [Measure.map_apply (by fun_prop) (ha.preimage (by fun_prop)),
    Measure.map_apply (by fun_prop) (hb.preimage (by fun_prop)),
    Measure.map_apply (by fun_prop)
      ((ha.preimage (by fun_prop)).inter (hb.preimage (by fun_prop)))]
  exact ((indepFun_prod (μ := treatmentMeasure (cateLowerPropensity d q s x))
    (ν := binaryMeasure M (treatedPlusProbability d β δ h M sign x))
    measurable_id (show Measurable (fun y : ℝ => ((0 : ℝ), y)) from by fun_prop)).symm).measure_inter_preimage_eq_mul a b ha hb

/-- Independent draws conditional on covariates establish joint exchangeability. -/
-- @node: cateLowerPair_exchangeability
lemma cateLowerPair_exchangeability : Exchangeability (cateLowerPair d β q s h δ M sign) := by
  intro hfinite
  let κ (x : Fin d → ℝ) : Measure (Full d) :=
    (treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1)))
  have hκ : Measurable κ := cateLowerPair_fullKernel_measurable d β q s h δ M hq sign
  have hr : ∀ᵐ x ∂volume.restrict (cube d), (κ x).map Prod.fst = Measure.dirac x := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact cateLowerPair_fiber_xLaw d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign x hx
  have hp : ∀ᵐ x ∂volume.restrict (cube d), IsProbabilityMeasure (κ x) := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact cateLowerPair_fiber_isProbabilityMeasure d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign x hx
  have hi : ∀ᵐ x ∂volume.restrict (cube d),
      IndepFun (fun u : Full d => u.2.2) (fun u : Full d => u.2.1) (κ x) := by
    filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
    exact cateLowerPair_fiber_indepFun d β q s h δ M hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign x hx
  have : IsFiniteMeasure ((volume.restrict (cube d)).bind κ) := hfinite
  change CondIndepFun _ _ _ _ ((volume.restrict (cube d)).bind κ)
  exact condIndepFun_bind_recording (volume.restrict (cube d)) κ Prod.fst
    hκ measurable_fst hr hp (fun u : Full d => u.2.2)
    (fun u : Full d => u.2.1) (by fun_prop) (by fun_prop) hi

end

/-- A single amplitude threshold puts both compatible zero-control witnesses
in the CATE class at every bandwidth, as required before (C28). -/
-- @node: cateLowerPair_uniform_cateClass
lemma cateLowerPair_uniform_cateClass (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hκ : 0 < κ ∧ κ < 1)
    (hcompat : 1 ≤ C * (1 - κ) ^ tailExponent γ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ M / 4 ∧
      ∀ (h δ : ℝ), 0 ≤ δ → δ ≤ δ₀ → 0 < h → h ≤ 1 →
        ∀ sign : Bool,
          CATEClass d β γ C L M κ
            (cateLowerPair d β (tailExponent γ) (C ^ (-1 / tailExponent γ)) h δ M sign) := by
  rcases hparam with ⟨hd, hβ, hγ, hC, hL, hM⟩
  have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hs : 0 < C ^ (-1 / tailExponent γ) := Real.rpow_pos_of_pos hCpos _
  have hsκ := cateLowerScale_compatible (tailExponent γ) C κ hq hCpos hκ.2 hcompat
  have hs1 : C ^ (-1 / tailExponent γ) ≤ 1 := by linarith [hκ.1]
  obtain ⟨δ₀, hδ₀, hδM, hholder⟩ :=
    cateLowerPair_uniform_treatedHolder d β L M hβ hL hM
  refine ⟨δ₀, hδ₀, hδM, ?_⟩
  intro h δ hδ hδsmall hh hh1 sign
  have hsmall : δ ≤ M / 4 := hδsmall.trans hδM
  have hu := cateLowerPair_uniformDesign d β (tailExponent γ) _ h δ M
    hd hq hs.le hs1 hβ hδ hh hh1 hM hsmall sign
  exact {
    parameters := ⟨hd, hβ, hγ, hC, hL, hM⟩
    semantics := cateLowerPair_lawSemantics d β (tailExponent γ) _ h δ M
      hd hq hs.le hs1 hβ hδ hh hh1 hM hsmall sign
    iid := cateLowerPair_iidSampling d β (tailExponent γ) _ h δ M
      hd hq hs.le hs1 hβ hδ hh hh1 hM hsmall sign
    uniformDesign := hu
    boundedOutcomes := cateLowerPair_boundedOutcomes d β (tailExponent γ) _ h δ M hM.le sign
    consistency := cateLowerPair_consistency d β (tailExponent γ) _ h δ M sign
    exchangeability := cateLowerPair_exchangeability d β (tailExponent γ) _ h δ M
      hd hq hs.le hs1 hβ hδ hh hh1 hM hsmall sign
    measurablePropensity := cateLowerPair_measurablePropensity d β (tailExponent γ) _ h δ M
      hd hq hs.le hs1 hβ hδ hh hh1 hM hsmall sign
    globalTail := cateLowerPair_globalTail_of_uniformDesign d β γ C _ h δ M
      hd hγ (le_trans zero_le_one hC) hs
      (cateLowerScale_calibration (tailExponent γ) C hq hCpos) sign hu
    treatedHolder := hholder (tailExponent γ) _ h δ hδ hδsmall hh hh1 sign
    controlHolder := cateLowerPair_controlHolder d β (tailExponent γ) _ h δ M L hL.le sign
    controlOverlap := cateLowerPair_controlOverlap_of_uniformDesign d β (tailExponent γ) _ h δ M κ
      hd hq hs.le hsκ sign hu
    controlParameter := hκ }

/-- The compatible witnesses belong to the zero-control subclass used in the
CATE minimax converse, rather than merely to the larger primary class. -/
-- @node: cateLowerPair_uniform_zeroControlCATEClass
lemma cateLowerPair_uniform_zeroControlCATEClass (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hκ : 0 < κ ∧ κ < 1)
    (hcompat : 1 ≤ C * (1 - κ) ^ tailExponent γ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ M / 4 ∧
      ∀ (h δ : ℝ), 0 ≤ δ → δ ≤ δ₀ → 0 < h → h ≤ 1 →
        ∀ sign : Bool,
          let P := cateLowerPair d β (tailExponent γ) (C ^ (-1 / tailExponent γ)) h δ M sign
          CATEClass d β γ C L M κ P ∧ ∀ x ∈ cube d, P.mu0 x = 0 := by
  obtain ⟨δ₀, hδ₀, hδM, hclass⟩ :=
    cateLowerPair_uniform_cateClass d β γ C L M κ hparam hκ hcompat
  refine ⟨δ₀, hδ₀, hδM, ?_⟩
  intro h δ hδ hδsmall hh hh1 sign
  exact ⟨hclass h δ hδ hδsmall hh hh1 sign, fun _ _ => rfl⟩

end CausalSmith.Stat.GlobalTailDesignRobustCate
