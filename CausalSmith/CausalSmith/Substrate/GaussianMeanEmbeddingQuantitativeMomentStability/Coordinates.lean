import CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.Recovery

/-!
# Quantitative Gaussian-feature coordinate bounds

This module turns norm control of the explicit Gaussian mean embedding into
simultaneous control of finitely many Gaussian-weighted monomial moments.  It
reuses the neutral explicit `ℓ²` feature realization rather than duplicating it.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability

open CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery

/-- The difference of the Gaussian-weighted moment of order `m` is at most the
embedding distance divided by the positive normalization of coordinate `m`. -/
theorem abs_gaussianWeightedMoment_sub_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m : ℕ) :
    |(∫ r, gaussianWeightedMonomial m r ∂μ) -
        ∫ r, gaussianWeightedMonomial m r ∂ν| ≤
      ‖meanEmbedding gaussianFeatureMap μ -
          meanEmbedding gaussianFeatureMap ν‖ /
        gaussianFeatureNormalization m := by
  -- Read coordinate `m` through `gaussianCoordinate_meanEmbedding`, factor out
  -- the positive normalization, and use `lp.norm_apply_le_norm` on the
  -- difference of the two embedding vectors before dividing.
  have hcoord :
      gaussianCoordinate m
          (meanEmbedding gaussianFeatureMap μ -
            meanEmbedding gaussianFeatureMap ν) =
        gaussianFeatureNormalization m *
          ((∫ r, gaussianWeightedMonomial m r ∂μ) -
            ∫ r, gaussianWeightedMonomial m r ∂ν) := by
    rw [map_sub, gaussianCoordinate_meanEmbedding,
      gaussianCoordinate_meanEmbedding]
    simp only [gaussianFeatureCoefficient, gaussianWeightedMonomial,
      gaussianWeight, mul_assoc, integral_const_mul]
    ring
  have hbound :
      |gaussianFeatureNormalization m *
          ((∫ r, gaussianWeightedMonomial m r ∂μ) -
            ∫ r, gaussianWeightedMonomial m r ∂ν)| ≤
        ‖meanEmbedding gaussianFeatureMap μ -
          meanEmbedding gaussianFeatureMap ν‖ := by
    rw [← hcoord, ← Real.norm_eq_abs]
    exact lp.norm_apply_le_norm (by norm_num)
      (meanEmbedding gaussianFeatureMap μ -
        meanEmbedding gaussianFeatureMap ν) m
  apply (le_div_iff₀ (gaussianFeatureNormalization_pos m)).2
  simpa only [abs_mul, abs_of_pos (gaussianFeatureNormalization_pos m),
    mul_comm] using hbound

/-- A finite linear combination of Gaussian-weighted moment differences is at
most the embedding distance times the sum of the absolute, normalization-adjusted
coefficients. -/
theorem abs_sum_gaussianWeightedMoment_sub_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ι : Type*} (s : Finset ι) (degree : ι → ℕ) (coefficient : ι → ℝ) :
    |∑ i ∈ s, coefficient i *
        ((∫ r, gaussianWeightedMonomial (degree i) r ∂μ) -
          ∫ r, gaussianWeightedMonomial (degree i) r ∂ν)| ≤
      (∑ i ∈ s, |coefficient i| /
          gaussianFeatureNormalization (degree i)) *
        ‖meanEmbedding gaussianFeatureMap μ -
          meanEmbedding gaussianFeatureMap ν‖ := by
  -- Apply `abs_sum_le_sum_abs`, use the one-coordinate estimate termwise,
  -- and factor the common nonnegative embedding norm out of the finite sum.
  calc
    |∑ i ∈ s, coefficient i *
        ((∫ r, gaussianWeightedMonomial (degree i) r ∂μ) -
          ∫ r, gaussianWeightedMonomial (degree i) r ∂ν)|
        ≤ ∑ i ∈ s, |coefficient i *
            ((∫ r, gaussianWeightedMonomial (degree i) r ∂μ) -
              ∫ r, gaussianWeightedMonomial (degree i) r ∂ν)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |coefficient i| *
          |(∫ r, gaussianWeightedMonomial (degree i) r ∂μ) -
            ∫ r, gaussianWeightedMonomial (degree i) r ∂ν| := by
          simp only [abs_mul]
    _ ≤ ∑ i ∈ s, (|coefficient i| /
          gaussianFeatureNormalization (degree i)) *
        ‖meanEmbedding gaussianFeatureMap μ -
          meanEmbedding gaussianFeatureMap ν‖ := by
          apply Finset.sum_le_sum
          intro i hi
          simpa only [div_eq_mul_inv, mul_assoc, mul_comm] using
            mul_le_mul_of_nonneg_left
              (abs_gaussianWeightedMoment_sub_le μ ν (degree i))
              (abs_nonneg (coefficient i))
    _ = (∑ i ∈ s, |coefficient i| /
          gaussianFeatureNormalization (degree i)) *
        ‖meanEmbedding gaussianFeatureMap μ -
          meanEmbedding gaussianFeatureMap ν‖ := by
          rw [Finset.sum_mul]

end CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability
