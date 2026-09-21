import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Transport of weighted measures across sample-domain equivalences

This module proves that weighting a measure by a density pulled back along a
measure-preserving measurable equivalence commutes with pushing the measure forward through that
equivalence.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Causalean

/-- With [a measure-preserving measurable equivalence of sample domains](hyp:e,he) and [a
nonnegative extended-real density on its target domain](hyp:d), [pushing forward the source measure
weighted by the pulled-back density gives the target measure weighted by the original density](goal).
No measurability or integrability condition on the density is needed. -/
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

end Causalean
