import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Transport of weighted measures across sample-domain equivalences

This module proves that weighting a measure by a density pulled back along a
measure-preserving measurable equivalence commutes with pushing the measure
forward through that equivalence.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport

/-- If a measurable equivalence preserves the reference measures, then pushing forward the source
measure weighted by the pulled-back density gives the target measure weighted by the original
density. No measurability or integrability hypothesis on the extended-nonnegative density is needed
because integration along a measurable equivalence is valid for arbitrary such functions. -/
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

end CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport
