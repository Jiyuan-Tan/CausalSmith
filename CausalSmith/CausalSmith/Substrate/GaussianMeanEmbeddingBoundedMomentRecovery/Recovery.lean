import CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.WeightedMomentDetermination

/-!
# Recovery from bounded-support Gaussian mean embeddings

This module connects equality of the explicit Hilbert-valued Gaussian mean
embeddings to equality of all weighted moments, equality of compactly
supported finite laws, and hence equality of raw second moments.  It also
packages the contrapositive as a strict norm-separation theorem.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery

/-- Equality of explicit Gaussian mean embeddings forces equality of every
Gaussian-weighted monomial integral. -/
lemma gaussianWeightedMoments_eq_of_meanEmbedding_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hemb : meanEmbedding gaussianFeatureMap μ = meanEmbedding gaussianFeatureMap ν)
    (m : ℕ) :
    ∫ r, gaussianWeightedMonomial m r ∂μ =
      ∫ r, gaussianWeightedMonomial m r ∂ν := by
  have hcoord := congrArg (gaussianCoordinate m) hemb
  rw [gaussianCoordinate_meanEmbedding, gaussianCoordinate_meanEmbedding] at hcoord
  have hscaled :
      gaussianFeatureNormalization m * ∫ r, gaussianWeightedMonomial m r ∂μ =
        gaussianFeatureNormalization m * ∫ r, gaussianWeightedMonomial m r ∂ν := by
    simpa only [gaussianFeatureCoefficient, gaussianWeightedMonomial, gaussianWeight,
      mul_assoc, integral_const_mul] using hcoord
  exact mul_left_cancel₀ (ne_of_gt (gaussianFeatureNormalization_pos m)) hscaled

/-- Equal explicit Gaussian mean embeddings determine finite real measures supported on a
common bounded closed interval. -/
theorem measure_eq_of_meanEmbedding_eq_of_boundedSupport
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hemb : meanEmbedding gaussianFeatureMap μ = meanEmbedding gaussianFeatureMap ν) :
    μ = ν := by
  apply measure_eq_of_gaussianWeightedMoments_eq μ ν B hB hμ hν
  exact gaussianWeightedMoments_eq_of_meanEmbedding_eq μ ν hemb

/-- Equal explicit Gaussian mean embeddings give equal raw second moments for finite laws
supported on a common bounded closed interval. -/
theorem secondMoment_eq_of_meanEmbedding_eq_of_boundedSupport
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hemb : meanEmbedding gaussianFeatureMap μ = meanEmbedding gaussianFeatureMap ν) :
    (∫ r, r ^ 2 ∂μ) = ∫ r, r ^ 2 ∂ν := by
  rw [measure_eq_of_meanEmbedding_eq_of_boundedSupport μ ν B hB hμ hν hemb]

/-- Unequal raw second moments force a strictly positive distance between the explicit Gaussian
mean embeddings of two finite laws with common bounded support. -/
theorem norm_meanEmbedding_sub_pos_of_secondMoment_ne_of_boundedSupport
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hmom : (∫ r, r ^ 2 ∂μ) ≠ ∫ r, r ^ 2 ∂ν) :
    0 < ‖meanEmbedding gaussianFeatureMap μ - meanEmbedding gaussianFeatureMap ν‖ := by
  rw [norm_pos_iff]
  intro hzero
  apply hmom
  apply secondMoment_eq_of_meanEmbedding_eq_of_boundedSupport μ ν B hB hμ hν
  exact sub_eq_zero.mp hzero

end CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery
