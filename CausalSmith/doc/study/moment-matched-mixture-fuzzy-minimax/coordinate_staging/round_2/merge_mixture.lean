
/-! ## Continuous prior-predictive mixtures

This section complements finite weighted mixtures with mixtures obtained by integrating a
measurable experiment kernel against an arbitrary prior.  It records probability and integration
interfaces used by moment-matching and fuzzy-hypothesis lower bounds.
-/

namespace Causalean.Stat.Minimax.MomentMatchedMixture

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

/-- Given [a prior measure](hyp:π) and [a measurable experiment kernel](hyp:K), the
[prior-predictive law](goal) first draws a parameter from the prior and then draws an observation
from the experiment at that parameter. -/
noncomputable def priorPredictive (π : Measure Θ) (K : Kernel Θ X) : Measure X :=
  π.bind fun θ => K θ

/-- Mixing [probability experiment laws](hyp:hK) from [a measurable kernel](hyp:K) against
[a probability prior](hyp:π) [produces a probability law on observations](goal). -/
theorem priorPredictive_isProbability (π : Measure Θ) (K : Kernel Θ X)
    [IsProbabilityMeasure π] (hK : ∀ θ, IsProbabilityMeasure (K θ)) :
    IsProbabilityMeasure (priorPredictive π K) := by
  rw [priorPredictive]
  apply isProbabilityMeasure_iff.mpr
  rw [Measure.bind_apply MeasurableSet.univ K.aemeasurable]
  simp_rw [isProbabilityMeasure_iff.mp (hK _)]
  simp

/-- The mass that [a prior](hyp:π) and [experiment kernel](hyp:K) assign to
[a measurable observation event](hyp:hA) [equals the prior average of its conditional event
probabilities](goal). -/
theorem priorPredictive_apply (π : Measure Θ) (K : Kernel Θ X) {A : Set X}
    (hA : MeasurableSet A) :
    priorPredictive π K A = ∫⁻ θ, K θ A ∂π := by
  exact Measure.bind_apply hA K.aemeasurable

/-- The lower integral of [a nonnegative measurable statistic](hyp:f,hf) under the mixture from
[a prior](hyp:π) and [experiment kernel](hyp:K) [equals the iterated prior-then-experiment lower
integral](goal). -/
theorem lintegral_priorPredictive (π : Measure Θ) (K : Kernel Θ X) (f : X → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂priorPredictive π K = ∫⁻ θ, ∫⁻ x, f x ∂K θ ∂π := by
  exact Measure.lintegral_bind K.aemeasurable hf.aemeasurable

/-- The expectation of [an integrable real-valued statistic](hyp:f,hf) under the mixture from
[a prior](hyp:π) and [experiment kernel](hyp:K) [equals the prior average of its conditional
expectations](goal). -/
theorem integral_priorPredictive (π : Measure Θ) (K : Kernel Θ X) (f : X → ℝ)
    (hf : Integrable f (priorPredictive π K)) :
    ∫ x, f x ∂priorPredictive π K = ∫ θ, ∫ x, f x ∂K θ ∂π := by
  exact Causalean.Mathlib.MeasureTheory.integral_bind K.measurable hf

end Causalean.Stat.Minimax.MomentMatchedMixture
