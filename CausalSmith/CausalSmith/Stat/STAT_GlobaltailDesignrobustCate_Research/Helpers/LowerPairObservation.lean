module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairSampling

/-! # Conditional outcome means and the observed binary experiment

These identities implement the direct binary-mean calculation and eliminate the
unobserved potential outcome from each treatment arm in the lower-pair roadmap.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory
open scoped ENNReal

/-- The symmetric control draw has zero mean. -/
-- @node: binaryMeasure_symmetric_mean
lemma binaryMeasure_symmetric_mean (M : ℝ) (hM : 0 < M) :
    (∫ y, y ∂binaryMeasure M (1 / 2)) = 0 := by
  have heq := binaryMeasure_eq_twoPointMean M 0
  simp only [mul_zero, zero_div, add_zero] at heq
  rw [heq]
  exact Causalean.Mathlib.Probability.twoPointMean_mean
    (by positivity) (by simp only [abs_zero]; positivity)

/-- The signed treated draw has exactly the chosen witness mean on each cube fibre. -/
-- @node: treatedBinary_mean
lemma treatedBinary_mean (d : ℕ) (β δ h M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    (∫ y, y ∂binaryMeasure M (treatedPlusProbability d β δ h M sign x)) =
      witnessMean d β δ h sign x := by
  unfold treatedPlusProbability
  rw [binaryMeasure_eq_twoPointMean]
  apply Causalean.Mathlib.Probability.twoPointMean_mean (by positivity)
  have hm := witnessMean_abs_le_delta_on_cube d β δ h hβ hδ hh hh1 sign x hx
  linarith

/-- An arbitrary test function integrates against the two treated atoms with their
specified conditional probabilities. -/
-- @node: treatedBinary_integral
lemma treatedBinary_integral (d : ℕ) (β δ h M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) (f : ℝ → ℝ) :
    (∫ y, f y ∂binaryMeasure M (treatedPlusProbability d β δ h M sign x)) =
      treatedPlusProbability d β δ h M sign x * f (M / 2) +
        (1 - treatedPlusProbability d β δ h M sign x) * f (-M / 2) := by
  unfold treatedPlusProbability
  rw [binaryMeasure_eq_twoPointMean]
  have hm : |witnessMean d β δ h sign x| ≤ M / 2 := by
    have hb := witnessMean_abs_le_delta_on_cube d β δ h hβ hδ hh hh1 sign x hx
    linarith
  rw [Causalean.Mathlib.Probability.twoPointMean_integral (by positivity) hm]
  congr 2 <;> congr 1 <;> ring

/-- After observation, only the treated binary draw contributes on treatment,
and only the common symmetric control draw contributes off treatment. -/
-- @node: lowerPair_observedFiber
lemma lowerPair_observedFiber (d : ℕ) (β q h δ M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1))))).map observe =
      ENNReal.ofReal (baselinePropensity d q x) •
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y => (x, true, y)) +
      ENNReal.ofReal (1 - baselinePropensity d q x) •
        (binaryMeasure M (1 / 2)).map (fun y => (x, false, y)) := by
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
  have ho : Measurable (observe (d := d)) := by
    unfold observe
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.ite _ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton true).preimage (by fun_prop)
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure (binaryMeasure M
      (treatedPlusProbability d β δ h M sign x)) :=
    binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have : IsProbabilityMeasure (binaryMeasure M (1 / 2)) :=
    binaryMeasure_isProbabilityMeasure M _ (by norm_num)
  have htrue : (η true).map observe =
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y => (x, true, y)) := by
    rw [show η true = (binaryMeasure M (1 / 2)).bind (ν true) from rfl,
      map_bind_channel _ _ _ (hν true) ho]
    have heq (y0 : ℝ) : (ν true y0).map observe =
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y => (x, true, y)) := by
      dsimp [ν]
      rw [Measure.map_map ho (by fun_prop)]
      rfl
    simp_rw [heq]
    rw [Measure.bind_const, measure_univ, one_smul]
  have hfalse : (η false).map observe =
      (binaryMeasure M (1 / 2)).map (fun y => (x, false, y)) := by
    rw [show η false = (binaryMeasure M (1 / 2)).bind (ν false) from rfl,
      map_bind_channel _ _ _ (hν false) ho]
    have heq (y0 : ℝ) : (ν false y0).map observe = Measure.dirac (x, false, y0) := by
      dsimp [ν]
      rw [Measure.map_map ho (by fun_prop)]
      change (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun _ => (x, false, y0)) = _
      rw [Measure.map_const, measure_univ, one_smul]
    simp_rw [heq]
    exact Measure.bind_dirac_eq_map _ (by fun_prop)
  change ((treatmentMeasure (baselinePropensity d q x)).bind η).map observe = _
  rw [treatmentMeasure, twoAtom_bind _ _ _ _ _ hη,
    Measure.map_add _ _ ho, Measure.map_smul, Measure.map_smul, htrue, hfalse]

/-- The actual observed law is the uniform mixture of the treated and control
binary channels. This removes both latent outcome coordinates before KL assembly. -/
-- @node: lowerPair_obs_eq_bind_binary
lemma lowerPair_obs_eq_bind_binary (d : ℕ) (β q h δ M : ℝ)
    (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool) :
    (lowerPair d β q h δ M sign).obs =
      (volume.restrict (cube d)).bind (fun x =>
        ENNReal.ofReal (baselinePropensity d q x) •
          (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
            (fun y => (x, true, y)) +
        ENNReal.ofReal (1 - baselinePropensity d q x) •
          (binaryMeasure M (1 / 2)).map (fun y => (x, false, y))) := by
  have ho : Measurable (observe (d := d)) := by
    unfold observe
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.ite _ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton true).preimage (by fun_prop)
  change ((volume.restrict (cube d)).bind (fun x =>
    (treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))))).map observe = _
  rw [map_bind_channel _ _ _ (lowerPair_fullKernel_measurable d β q h δ M hq sign) ho]
  apply Measure.bind_congr_right
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact lowerPair_observedFiber d β q h δ M hβ hδ hh hh1 hM hsmall sign x hx

/-- The observed experiment has four atoms at each covariate value; its control
weights are common to both signs, and its treated weights contain the bump. -/
-- @node: lowerPair_obs_eq_bind_fourAtoms
lemma lowerPair_obs_eq_bind_fourAtoms (d : ℕ) (β q h δ M : ℝ)
    (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool) :
    (lowerPair d β q h δ M sign).obs =
      (volume.restrict (cube d)).bind (fun x =>
        ENNReal.ofReal (baselinePropensity d q x) •
          (ENNReal.ofReal (treatedPlusProbability d β δ h M sign x) •
            Measure.dirac (x, true, M / 2) +
           ENNReal.ofReal (1 - treatedPlusProbability d β δ h M sign x) •
            Measure.dirac (x, true, -M / 2)) +
        ENNReal.ofReal (1 - baselinePropensity d q x) •
          (ENNReal.ofReal (1 / 2) • Measure.dirac (x, false, M / 2) +
           ENNReal.ofReal (1 / 2) • Measure.dirac (x, false, -M / 2))) := by
  rw [lowerPair_obs_eq_bind_binary d β q h δ M hq hβ hδ hh hh1 hM hsmall sign]
  congr 1
  funext x
  have ht : Measurable (fun y : ℝ => (x, true, y)) := by fun_prop
  have hc : Measurable (fun y : ℝ => (x, false, y)) := by fun_prop
  simp only [binaryMeasure, Measure.map_add _ _ ht, Measure.map_add _ _ hc,
    Measure.map_smul, Measure.map_dirac' ht, Measure.map_dirac' hc]
  norm_num

end CausalSmith.Stat.GlobalTailDesignRobustCate
