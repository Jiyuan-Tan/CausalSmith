module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Weighted-measure transport under measurable equivalences

This module shows that weighting a source measure by a density pulled back along a
measure-preserving measurable equivalence commutes with pushing that measure forward.
-/

public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.MeasureTheory

/-- With [a measurable equivalence](hyp:e), [a certificate that it preserves the two
measures](hyp:he), and [a target-domain density](hyp:d), [pushing forward the source measure
weighted by the pulled-back density yields the target measure weighted by that density](goal). -/
theorem map_withDensity_comp_measurableEquiv
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (e : Ω ≃ᵐ Ω') {μ : Measure Ω} {μ' : Measure Ω'}
    (he : MeasurePreserving e μ μ') (d : Ω' → ℝ≥0∞) :
    Measure.map e (μ.withDensity (d ∘ e)) = μ'.withDensity d := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  rw [he.lintegral_map_equiv (s.indicator d) e]
  congr 1

end Causalean.Mathlib.MeasureTheory
