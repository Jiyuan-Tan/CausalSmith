module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ReferenceDeathLaw

/-!
# Density of the shifted exponential continuation

This module identifies the translated unit-rate exponential continuation as
a Lebesgue density.  It is the tail-density component of the global reference
death law.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Translating a unit exponential by one translates its Lebesgue density. -/
lemma shiftedUnitExpLaw_eq_withDensity :
    shiftedUnitExpLaw =
      volume.withDensity (fun s : ℝ => gammaPDF 1 1 (s - 1)) := by
  ext E hE
  rw [shiftedUnitExpLaw, expMeasure, gammaMeasure,
    Measure.map_apply (by fun_prop) hE,
    withDensity_apply _ (hE.preimage (by fun_prop)),
    withDensity_apply _ hE]
  have hg : Measurable (fun y : ℝ => gammaPDF 1 1 (y - 1)) := by
    change Measurable (fun y : ℝ => ENNReal.ofReal (gammaPDFReal 1 1 (y - 1)))
    exact (measurable_gammaPDFReal 1 1).ennreal_ofReal.comp (by fun_prop)
  have hmeas : Measurable (fun s : ℝ =>
      E.indicator (fun y => gammaPDF 1 1 (y - 1)) s) :=
    hg.indicator hE
  have htranslate := (measurePreserving_add_left volume (1 : ℝ)).lintegral_comp hmeas
  calc
    (∫⁻ x in (fun x : ℝ => 1 + x) ⁻¹' E, gammaPDF 1 1 x) =
        ∫⁻ x, ((fun x : ℝ => 1 + x) ⁻¹' E).indicator
          (fun x => gammaPDF 1 1 x) x :=
      ((lintegral_indicator (μ := volume) (hE.preimage (by fun_prop))) _).symm
    _ = ∫⁻ x, E.indicator (fun y => gammaPDF 1 1 (y - 1)) (1 + x) := by
      apply lintegral_congr
      intro x
      by_cases hx : 1 + x ∈ E
      · have hxpre : x ∈ (fun x : ℝ => 1 + x) ⁻¹' E := hx
        rw [Set.indicator_of_mem hxpre]
        rw [Set.indicator_of_mem hx]
        congr 2
        ring
      · have hxpre : x ∉ (fun x : ℝ => 1 + x) ⁻¹' E := hx
        simp [hx, hxpre]
    _ = ∫⁻ y, E.indicator (fun y => gammaPDF 1 1 (y - 1)) y := htranslate
    _ = ∫⁻ y in E, gammaPDF 1 1 (y - 1) :=
      (lintegral_indicator (μ := volume) hE) _

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
