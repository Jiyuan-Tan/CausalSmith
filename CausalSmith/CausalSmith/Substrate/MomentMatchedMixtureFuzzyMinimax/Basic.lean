import Causalean.Mathlib.MeasureTheory.IntegralBind
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Prior-predictive mixtures

This module defines the mixture of a measurable experiment kernel over a prior and records
the probability and integration interfaces used by moment-matching and fuzzy-hypothesis
arguments.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

/-- The prior-predictive law is obtained by first drawing a parameter from the prior and then
drawing an observation from the experiment kernel at that parameter. -/
noncomputable def priorPredictive (π : Measure Θ) (K : Kernel Θ X) : Measure X :=
  π.bind fun θ => K θ

/-- Mixing probability experiment fibres against a probability prior produces a probability
measure on observations. -/
theorem priorPredictive_isProbability (π : Measure Θ) (K : Kernel Θ X)
    [IsProbabilityMeasure π] (hK : ∀ θ, IsProbabilityMeasure (K θ)) :
    IsProbabilityMeasure (priorPredictive π K) := by
  rw [priorPredictive]
  apply isProbabilityMeasure_iff.mpr
  rw [Measure.bind_apply MeasurableSet.univ K.aemeasurable]
  simp_rw [isProbabilityMeasure_iff.mp (hK _)]
  simp

/-- The mass assigned by a prior-predictive law to a measurable event is the prior average of
the fibrewise event probabilities. -/
theorem priorPredictive_apply (π : Measure Θ) (K : Kernel Θ X) {A : Set X}
    (hA : MeasurableSet A) :
    priorPredictive π K A = ∫⁻ θ, K θ A ∂π := by
  exact Measure.bind_apply hA K.aemeasurable

/-- A nonnegative measurable loss integrated under the prior-predictive law equals its iterated
prior-then-experiment lower integral. -/
theorem lintegral_priorPredictive (π : Measure Θ) (K : Kernel Θ X) (f : X → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂priorPredictive π K = ∫⁻ θ, ∫⁻ x, f x ∂K θ ∂π := by
  exact Measure.lintegral_bind K.aemeasurable hf.aemeasurable

/-- An integrable real-valued statistic under the prior-predictive law has expectation equal to
the prior average of its fibrewise expectations. -/
theorem integral_priorPredictive (π : Measure Θ) (K : Kernel Θ X) (f : X → ℝ)
    (hf : Integrable f (priorPredictive π K)) :
    ∫ x, f x ∂priorPredictive π K = ∫ θ, ∫ x, f x ∂K θ ∂π := by
  exact Causalean.Mathlib.MeasureTheory.integral_bind K.measurable hf

end CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax
