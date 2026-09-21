module
public import CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.CompactContinuousDetermination

/-!
# Compact-support determination by Gaussian-weighted moments

This module isolates the approximation-theoretic core of Gaussian mean
embedding injectivity.  On a common compact interval, equality against every
Gaussian-weighted monomial determines finite Borel measures.
-/

public section

open MeasureTheory Set

noncomputable section

namespace CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery

/-- Finite real Borel measures concentrated on one bounded closed interval are equal when all
their Gaussian-weighted monomial integrals agree. -/
theorem measure_eq_of_gaussianWeightedMoments_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hmom : ∀ m : ℕ,
      ∫ r, gaussianWeightedMonomial m r ∂μ =
        ∫ r, gaussianWeightedMonomial m r ∂ν) :
    μ = ν := by
  apply measure_eq_of_continuousIntegral_eq μ ν
  intro f hf
  exact continuousIntegral_eq_of_gaussianWeightedMoments_eq μ ν B hB hμ hν hmom f hf

end CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery
