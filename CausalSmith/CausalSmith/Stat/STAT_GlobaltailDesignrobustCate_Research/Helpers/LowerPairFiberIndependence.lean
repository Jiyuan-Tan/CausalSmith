module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairSemantics
public import Mathlib.Probability.Independence.Basic

/-! # Independent treatment and potential outcomes in each witness fibre

The conditional sampling in equations (14)--(16) of the membership roadmap
is a product of the treatment law and the joint potential-outcome law.
These identities retain both outcomes together, as required by exchangeability.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory

/-- Independent sequential draws, followed by a measurable recording, are the
recorded product measure. -/
-- @node: bind_map_eq_recorded_product
lemma bind_map_eq_recorded_product {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (f : X × Y → Z) (hf : Measurable f) :
    μ.bind (fun x => ν.map (fun y => f (x, y))) = (μ.prod ν).map f := by
  rw [Measure.prod, map_bind_channel _ _ _ Measurable.map_prodMk_left hf]
  congr 1
  funext x
  rw [Measure.map_map hf (by fun_prop)]
  rfl

/-- At a fixed covariate, the entire witness fibre is a recorded product of
treatment and the two independent potential outcomes. -/
-- @node: lowerPair_fiber_eq_product
lemma lowerPair_fiber_eq_product (d : ℕ) (β q h δ M : ℝ)
    (sign : Bool) (x : Fin d → ℝ) :
    (treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))) =
    ((treatmentMeasure (baselinePropensity d q x)).prod
      ((binaryMeasure M (1 / 2)).prod
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)))).map
      (fun z => (x, z.1, z.2)) := by
  have : IsFiniteMeasure (binaryMeasure M (1 / 2)) := by
    constructor
    simp [binaryMeasure, ENNReal.add_lt_top]
  have : IsFiniteMeasure
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)) := by
    constructor
    simp [binaryMeasure, ENNReal.add_lt_top]
  have hinner (a : Bool) :
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))) =
      ((binaryMeasure M (1 / 2)).prod
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x))).map
        (fun y => (x, a, y)) :=
    bind_map_eq_recorded_product (binaryMeasure M (1 / 2))
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x))
      (fun y : ℝ × ℝ => (x, a, y)) (by fun_prop)
  simp_rw [hinner]
  exact bind_map_eq_recorded_product (treatmentMeasure (baselinePropensity d q x))
    ((binaryMeasure M (1 / 2)).prod
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)))
    (fun z : Bool × (ℝ × ℝ) => (x, z.1, z.2)) (by fun_prop)

/-- Forgetting the recorded covariate recovers the product law of treatment
and the joint pair of potential outcomes. -/
-- @node: lowerPair_fiber_jointOutcomesTreatment
lemma lowerPair_fiber_jointOutcomesTreatment (d : ℕ) (β q h δ M : ℝ)
    (sign : Bool) (x : Fin d → ℝ) :
    ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))).map
      (fun u : Full d => (u.2.1, u.2.2)) =
    (treatmentMeasure (baselinePropensity d q x)).prod
      ((binaryMeasure M (1 / 2)).prod
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x))) := by
  rw [lowerPair_fiber_eq_product, Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

/-- Treatment is independent of the joint potential-outcome pair in every
normalized covariate fibre, for either sign of the witness. -/
-- @node: lowerPair_fiber_indepFun
lemma lowerPair_fiber_indepFun (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ProbabilityTheory.IndepFun (fun u : Full d => u.2.2)
      (fun u : Full d => u.2.1)
      ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
        (binaryMeasure M (1 / 2)).bind (fun y0 =>
          (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
            (fun y1 => (x, a, y0, y1))))) := by
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  have := baselineTreatment_isProbabilityMeasure d q hd hq x hx
  have := binaryMeasure_isProbabilityMeasure M (1 / 2) (by norm_num)
  have := binaryMeasure_isProbabilityMeasure M
    (treatedPlusProbability d β δ h M sign x) ⟨by linarith [hp.1], by linarith [hp.2]⟩
  rw [lowerPair_fiber_eq_product]
  apply ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  rw [Measure.map_apply (by fun_prop) (hs.preimage (by fun_prop)),
    Measure.map_apply (by fun_prop) (ht.preimage (by fun_prop)),
    Measure.map_apply (by fun_prop)
      ((hs.preimage (by fun_prop)).inter (ht.preimage (by fun_prop)))]
  exact ((ProbabilityTheory.indepFun_prod (μ := treatmentMeasure (baselinePropensity d q x))
    (ν := (binaryMeasure M (1 / 2)).prod
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)))
    measurable_id measurable_id).symm).measure_inter_preimage_eq_mul s t hs ht

/-- The latent witness's joint law of covariate, treatment, and potential-outcome
pair is the uniform mixture of the recorded independent product fibres. -/
-- @node: lowerPair_jointOutcomesTreatment
lemma lowerPair_jointOutcomesTreatment (d : ℕ) (β q h δ M : ℝ)
    (hq : 0 < q) (sign : Bool) :
    (lowerPair d β q h δ M sign).full.map
      (fun u : Full d => (u.1, u.2.1, u.2.2)) =
    (volume.restrict (cube d)).bind (fun x =>
      ((treatmentMeasure (baselinePropensity d q x)).prod
        ((binaryMeasure M (1 / 2)).prod
          (binaryMeasure M (treatedPlusProbability d β δ h M sign x)))).map
        (fun z => (x, z.1, z.2))) := by
  change ((volume.restrict (cube d)).bind _).map _ = _
  rw [map_bind_channel _ _ _ (lowerPair_fullKernel_measurable d β q h δ M hq sign)
    (by fun_prop)]
  congr 1
  funext x
  rw [lowerPair_fiber_eq_product, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Removing treatment leaves the recorded product of the two potential-outcome
channels at each covariate value. -/
-- @node: lowerPair_fiber_jointOutcomes
lemma lowerPair_fiber_jointOutcomes (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (sign : Bool)
    (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))).map
      (fun u : Full d => (u.1, u.2.2)) =
    ((binaryMeasure M (1 / 2)).prod
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x))).map
      (fun y => (x, y)) := by
  have := baselineTreatment_isProbabilityMeasure d q hd hq x hx
  have : IsFiniteMeasure (binaryMeasure M (1 / 2)) := by
    constructor
    simp [binaryMeasure, ENNReal.add_lt_top]
  have : IsFiniteMeasure
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)) := by
    constructor
    simp [binaryMeasure, ENNReal.add_lt_top]
  rw [lowerPair_fiber_eq_product, Measure.map_map (by fun_prop) (by fun_prop)]
  change (((treatmentMeasure (baselinePropensity d q x)).prod
    ((binaryMeasure M (1 / 2)).prod
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)))).map
      ((fun y => (x, y)) ∘ Prod.snd)) = _
  rw [← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul]

/-- The joint latent covariate and potential-outcome law mixes the independent
outcome channels over uniform covariates, without a treatment weight. -/
-- @node: lowerPair_jointOutcomes
lemma lowerPair_jointOutcomes (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (sign : Bool) :
    (lowerPair d β q h δ M sign).full.map
      (fun u : Full d => (u.1, u.2.2)) =
    (volume.restrict (cube d)).bind (fun x =>
      ((binaryMeasure M (1 / 2)).prod
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x))).map
        (fun y => (x, y))) := by
  change ((volume.restrict (cube d)).bind _).map _ = _
  rw [map_bind_channel _ _ _ (lowerPair_fullKernel_measurable d β q h δ M hq sign)
    (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact lowerPair_fiber_jointOutcomes d β q h δ M hd hq sign x hx

end CausalSmith.Stat.GlobalTailDesignRobustCate
