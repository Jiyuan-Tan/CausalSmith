module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairRegularity

/-! # Conditional-fibre means of the binary witness

The joint marginal identities reduce the means of all three latent coordinates
on each covariate fibre to the binary calculations in (15)--(16) of the
lower-pair membership roadmap. These are pointwise kernel calculations;
conditional-expectation versions still require disintegration.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory
open scoped ENNReal

/-- The treated coordinate has its prescribed mean on every cube fibre. -/
-- @node: lowerPair_fiber_treated_mean
lemma lowerPair_fiber_treated_mean (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    (∫ u : Full d, u.2.2.2 ∂((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))) =
      witnessMean d β δ h sign x := by
  let ν : Measure (Full d) := ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))
  have hm : StronglyMeasurable (Prod.snd : (Fin d → ℝ) × ℝ → ℝ) := by fun_prop
  have heq := integral_map_of_stronglyMeasurable
    (μ := ν) (φ := (fun u : Full d => (u.1, u.2.2.2))) (by fun_prop) hm
  change (∫ u : Full d, u.2.2.2 ∂ν) = _
  rw [← heq]
  change (∫ z, Prod.snd z ∂(ν.map (fun u : Full d => (u.1, u.2.2.2)))) = _
  rw [lowerPair_fiber_jointTreated d β q h δ M hd hq sign x hx]
  rw [integral_map_of_stronglyMeasurable (by fun_prop) hm]
  exact treatedBinary_mean d β δ h M hβ hδ hh hh1 hM hsmall sign x hx

/-- The control coordinate has its prescribed mean on every cube fibre. -/
-- @node: lowerPair_fiber_control_mean
lemma lowerPair_fiber_control_mean (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    (∫ u : Full d, u.2.2.1 ∂((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))) =
      0 := by
  let ν : Measure (Full d) := ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))
  have hm : StronglyMeasurable (Prod.snd : (Fin d → ℝ) × ℝ → ℝ) := by fun_prop
  have heq := integral_map_of_stronglyMeasurable
    (μ := ν) (φ := (fun u : Full d => (u.1, u.2.2.1))) (by fun_prop) hm
  change (∫ u : Full d, u.2.2.1 ∂ν) = _
  rw [← heq]
  change (∫ z, Prod.snd z ∂(ν.map (fun u : Full d => (u.1, u.2.2.1)))) = _
  rw [lowerPair_fiber_jointControl d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx]
  rw [integral_map_of_stronglyMeasurable (by fun_prop) hm]
  exact binaryMeasure_symmetric_mean M hM

/-- The treatment coordinate has its prescribed mean on every cube fibre. -/
-- @node: lowerPair_fiber_treatment_mean
lemma lowerPair_fiber_treatment_mean (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    (∫ u : Full d, if u.2.1 then (1 : ℝ) else 0 ∂((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))) =
      baselinePropensity d q x := by
  let ν : Measure (Full d) := ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))
  have hm : StronglyMeasurable (fun z : (Fin d → ℝ) × Bool => if z.2 then (1 : ℝ) else 0) := by
    apply Measurable.stronglyMeasurable
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_singleton true).preimage measurable_snd
  have heq := integral_map_of_stronglyMeasurable
    (μ := ν) (φ := (fun u : Full d => (u.1, u.2.1))) (by fun_prop) hm
  change (∫ u : Full d, if u.2.1 then (1 : ℝ) else 0 ∂ν) = _
  rw [← heq]
  change (∫ z, (fun z : (Fin d → ℝ) × Bool => if z.2 then (1 : ℝ) else 0) z ∂(ν.map (fun u : Full d => (u.1, u.2.1)))) = _
  rw [lowerPair_fiber_jointTreatment d β q h δ M hβ hδ hh hh1 hM hsmall sign x hx]
  rw [integral_map_of_stronglyMeasurable (by fun_prop) hm]
  have hp := baselinePropensity_unit_interval d q hd hq x hx
  rw [treatmentMeasure, integral_add_measure, integral_smul_measure,
    integral_smul_measure]
  · simp [ENNReal.toReal_ofReal hp.1]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- Each cube fibre is a normalized probability law, rather than a formal mixture. -/
-- @node: lowerPair_fiber_isProbabilityMeasure
lemma lowerPair_fiber_isProbabilityMeasure (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    IsProbabilityMeasure ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))) := by
  let ν : Measure (Full d) := ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  haveI : IsProbabilityMeasure (binaryMeasure M
      (treatedPlusProbability d β δ h M sign x)) :=
    binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  haveI : IsProbabilityMeasure (ν.map (fun u : Full d => (u.1, u.2.2.2))) := by
    rw [show ν.map (fun u : Full d => (u.1, u.2.2.2)) = _ from
      lowerPair_fiber_jointTreated d β q h δ M hd hq sign x hx]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  exact Measure.isProbabilityMeasure_of_map (μ := ν)
    (fun u : Full d => (u.1, u.2.2.2))

/-- A real-valued binary draw is integrable for every finite pair of weights. -/
-- @node: binaryMeasure_integrable_id
lemma binaryMeasure_integrable_id (M p : ℝ) :
    Integrable (fun y : ℝ => y) (binaryMeasure M p) := by
  unfold binaryMeasure
  apply Integrable.add_measure
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- The treated potential outcome is integrable on every cube fibre. -/
-- @node: lowerPair_fiber_integrable_treated
lemma lowerPair_fiber_integrable_treated (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    Integrable (fun u : Full d => u.2.2.2) ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))) := by
  let ν : Measure (Full d) := ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))
  have hm : StronglyMeasurable (Prod.snd : (Fin d → ℝ) × ℝ → ℝ) := by fun_prop
  have hi : Integrable Prod.snd (ν.map (fun u : Full d => (u.1, u.2.2.2))) := by
    rw [show ν.map (fun u : Full d => (u.1, u.2.2.2)) = _ from
      lowerPair_fiber_jointTreated d β q h δ M hd hq sign x hx]
    apply (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).2
    exact binaryMeasure_integrable_id M _
  exact (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).1 hi

/-- The control potential outcome is integrable on every cube fibre. -/
-- @node: lowerPair_fiber_integrable_control
lemma lowerPair_fiber_integrable_control (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    Integrable (fun u : Full d => u.2.2.1) ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))) := by
  let ν : Measure (Full d) := ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))
  have hm : StronglyMeasurable (Prod.snd : (Fin d → ℝ) × ℝ → ℝ) := by fun_prop
  have hi : Integrable Prod.snd (ν.map (fun u : Full d => (u.1, u.2.2.1))) := by
    rw [show ν.map (fun u : Full d => (u.1, u.2.2.1)) = _ from
      lowerPair_fiber_jointControl d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx]
    apply (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).2
    exact binaryMeasure_integrable_id M _
  exact (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).1 hi

/-- The bounded treatment indicator is integrable on every normalized cube fibre. -/
-- @node: lowerPair_fiber_integrable_treatment
lemma lowerPair_fiber_integrable_treatment (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    Integrable (fun u : Full d => if u.2.1 then (1 : ℝ) else 0)
      ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
        (binaryMeasure M (1 / 2)).bind (fun y0 =>
          (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
            (fun y1 => (x, a, y0, y1))))) := by
  haveI := lowerPair_fiber_isProbabilityMeasure d β q h δ M
    hd hq hβ hδ hh hh1 hM hsmall sign x hx
  have hm : Measurable (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_singleton true).preimage (by fun_prop)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun u => by cases u.2.1 <;> norm_num)

end CausalSmith.Stat.GlobalTailDesignRobustCate
