module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairObservation

/-! # Joint marginal laws of the binary witness

Integrating out the normalized independent draws identifies the joint laws of
covariates with treatment and with each potential outcome. These identities
supply the law-side input for checking the conditional nuisance versions.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory
open scoped ENNReal

/-- At a fixed covariate value, removing treatment and the control draw leaves
exactly the signed treated-outcome channel. -/
-- @node: lowerPair_fiber_jointTreated
lemma lowerPair_fiber_jointTreated (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))).map
      (fun u : Full d => (u.1, u.2.2.2)) =
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, y1)) := by
  let ν (a : Bool) (y0 : ℝ) : Measure (Full d) :=
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun y1 => (x, a, y0, y1))
  let η (a : Bool) := (binaryMeasure M (1 / 2)).bind (ν a)
  have hν (a : Bool) : Measurable (ν a) := by
    simpa only [Function.comp_def] using (lowerPair_outcomeMap_measurable d β δ h M sign).comp
      (show Measurable (fun y0 : ℝ => (x, a, y0)) from by fun_prop)
  have hη : Measurable η := by
    simpa only [Function.comp_def] using (lowerPair_controlMap_measurable d β δ h M sign).comp
      (show Measurable (fun a : Bool => (x, a)) from by fun_prop)
  have : IsProbabilityMeasure (binaryMeasure M (1 / 2)) :=
    binaryMeasure_isProbabilityMeasure M _ (by norm_num)
  have := baselineTreatment_isProbabilityMeasure d q hd hq x hx
  have hlast (a : Bool) (y0 : ℝ) :
      (ν a y0).map (fun u : Full d => (u.1, u.2.2.2)) =
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, y1)) := by
    dsimp [ν]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hmiddle (a : Bool) :
      (η a).map (fun u : Full d => (u.1, u.2.2.2)) =
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, y1)) := by
    rw [show η a = (binaryMeasure M (1 / 2)).bind (ν a) from rfl,
      map_bind_channel _ _ _ (hν a) (by fun_prop)]
    simp_rw [hlast]
    rw [Measure.bind_const, measure_univ, one_smul]
  change ((treatmentMeasure (baselinePropensity d q x)).bind η).map _ = _
  rw [map_bind_channel _ _ _ hη (by fun_prop)]
  simp_rw [hmiddle]
  rw [Measure.bind_const, measure_univ, one_smul]

/-- At a fixed covariate value, removing treatment and the treated draw leaves
the common symmetric control-outcome channel. -/
-- @node: lowerPair_fiber_jointControl
lemma lowerPair_fiber_jointControl (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))).map
      (fun u : Full d => (u.1, u.2.2.1)) =
      (binaryMeasure M (1 / 2)).map (fun y0 => (x, y0)) := by
  let ν (a : Bool) (y0 : ℝ) : Measure (Full d) :=
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun y1 => (x, a, y0, y1))
  let η (a : Bool) := (binaryMeasure M (1 / 2)).bind (ν a)
  have hν (a : Bool) : Measurable (ν a) := by
    simpa only [Function.comp_def] using (lowerPair_outcomeMap_measurable d β δ h M sign).comp
      (show Measurable (fun y0 : ℝ => (x, a, y0)) from by fun_prop)
  have hη : Measurable η := by
    simpa only [Function.comp_def] using (lowerPair_controlMap_measurable d β δ h M sign).comp
      (show Measurable (fun a : Bool => (x, a)) from by fun_prop)
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure (binaryMeasure M
      (treatedPlusProbability d β δ h M sign x)) :=
    binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have := baselineTreatment_isProbabilityMeasure d q hd hq x hx
  have hlast (a : Bool) (y0 : ℝ) :
      (ν a y0).map (fun u : Full d => (u.1, u.2.2.1)) = Measure.dirac (x, y0) := by
    dsimp [ν]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    change (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun _ => (x, y0)) = _
    rw [Measure.map_const, measure_univ, one_smul]
  have hmiddle (a : Bool) :
      (η a).map (fun u : Full d => (u.1, u.2.2.1)) =
      (binaryMeasure M (1 / 2)).map (fun y0 => (x, y0)) := by
    rw [show η a = (binaryMeasure M (1 / 2)).bind (ν a) from rfl,
      map_bind_channel _ _ _ (hν a) (by fun_prop)]
    simp_rw [hlast]
    exact Measure.bind_dirac_eq_map _ (by fun_prop)
  change ((treatmentMeasure (baselinePropensity d q x)).bind η).map _ = _
  rw [map_bind_channel _ _ _ hη (by fun_prop)]
  simp_rw [hmiddle]
  rw [Measure.bind_const, measure_univ, one_smul]

/-- At a fixed covariate value, integrating out both normalized outcome draws
leaves the prescribed Bernoulli treatment channel. -/
-- @node: lowerPair_fiber_jointTreatment
lemma lowerPair_fiber_jointTreatment (d : ℕ) (β q h δ M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))).map
      (fun u : Full d => (u.1, u.2.1)) =
      (treatmentMeasure (baselinePropensity d q x)).map (fun a => (x, a)) := by
  let ν (a : Bool) (y0 : ℝ) : Measure (Full d) :=
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun y1 => (x, a, y0, y1))
  let η (a : Bool) := (binaryMeasure M (1 / 2)).bind (ν a)
  have hν (a : Bool) : Measurable (ν a) := by
    simpa only [Function.comp_def] using (lowerPair_outcomeMap_measurable d β δ h M sign).comp
      (show Measurable (fun y0 : ℝ => (x, a, y0)) from by fun_prop)
  have hη : Measurable η := by
    simpa only [Function.comp_def] using (lowerPair_controlMap_measurable d β δ h M sign).comp
      (show Measurable (fun a : Bool => (x, a)) from by fun_prop)
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure (binaryMeasure M
      (treatedPlusProbability d β δ h M sign x)) :=
    binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have : IsProbabilityMeasure (binaryMeasure M (1 / 2)) :=
    binaryMeasure_isProbabilityMeasure M _ (by norm_num)
  have hlast (a : Bool) (y0 : ℝ) :
      (ν a y0).map (fun u : Full d => (u.1, u.2.1)) = Measure.dirac (x, a) := by
    dsimp [ν]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    change (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun _ => (x, a)) = _
    rw [Measure.map_const, measure_univ, one_smul]
  have hmiddle (a : Bool) :
      (η a).map (fun u : Full d => (u.1, u.2.1)) = Measure.dirac (x, a) := by
    rw [show η a = (binaryMeasure M (1 / 2)).bind (ν a) from rfl,
      map_bind_channel _ _ _ (hν a) (by fun_prop)]
    simp_rw [hlast]
    rw [Measure.bind_const, measure_univ, one_smul]
  change ((treatmentMeasure (baselinePropensity d q x)).bind η).map _ = _
  rw [map_bind_channel _ _ _ hη (by fun_prop)]
  simp_rw [hmiddle]
  exact Measure.bind_dirac_eq_map _ (by fun_prop)

/-- The joint covariate and treated-potential-outcome law is the uniform mixture
of the prescribed signed binary channel. -/
-- @node: lowerPair_jointTreated
lemma lowerPair_jointTreated (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q)
    (sign : Bool) :
    (lowerPair d β q h δ M sign).full.map
      (fun u : Full d => (u.1, u.2.2.2)) =
      (volume.restrict (cube d)).bind (fun x =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, y1))) := by
  change ((volume.restrict (cube d)).bind _).map _ = _
  rw [map_bind_channel _ _ _ (lowerPair_fullKernel_measurable d β q h δ M hq sign)
    (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact lowerPair_fiber_jointTreated d β q h δ M hd hq sign x hx

/-- The joint covariate and control-potential-outcome law is the uniform mixture
of the same symmetric binary channel under both signs. -/
-- @node: lowerPair_jointControl
lemma lowerPair_jointControl (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) :
    (lowerPair d β q h δ M sign).full.map
      (fun u : Full d => (u.1, u.2.2.1)) =
      (volume.restrict (cube d)).bind (fun x =>
        (binaryMeasure M (1 / 2)).map (fun y0 => (x, y0))) := by
  change ((volume.restrict (cube d)).bind _).map _ = _
  rw [map_bind_channel _ _ _ (lowerPair_fullKernel_measurable d β q h δ M hq sign)
    (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact lowerPair_fiber_jointControl d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign x hx

/-- The joint covariate and treatment law is precisely the uniform mixture of
the baseline propensity channel. -/
-- @node: lowerPair_jointTreatment
lemma lowerPair_jointTreatment (d : ℕ) (β q h δ M : ℝ)
    (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) :
    (lowerPair d β q h δ M sign).full.map
      (fun u : Full d => (u.1, u.2.1)) =
      (volume.restrict (cube d)).bind (fun x =>
        (treatmentMeasure (baselinePropensity d q x)).map (fun a => (x, a))) := by
  change ((volume.restrict (cube d)).bind _).map _ = _
  rw [map_bind_channel _ _ _ (lowerPair_fullKernel_measurable d β q h δ M hq sign)
    (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact lowerPair_fiber_jointTreatment d β q h δ M hβ hδ hh hh1 hM hsmall sign x hx

end CausalSmith.Stat.GlobalTailDesignRobustCate
