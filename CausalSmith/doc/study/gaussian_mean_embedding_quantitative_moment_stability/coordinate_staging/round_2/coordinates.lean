import Causalean.Mathlib.Probability.GaussianMeanEmbedding.Basic

/-!
# Quantitative Gaussian-feature coordinate bounds

This module turns norm control of the explicit Gaussian mean embedding into
simultaneous control of finitely many Gaussian-weighted monomial moments.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Causalean.Mathlib.Probability.GaussianMeanEmbedding

open Causalean.Mathlib.Probability.GaussianMeanEmbedding

/-- [Two finite real measures `μ` and `ν`](hyp:μ,ν) and [a coordinate order `m`](hyp:m)
have [a Gaussian-weighted moment gap no larger than their explicit Gaussian mean-embedding
distance divided by that coordinate's positive normalization](goal). -/
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

/-- [Two finite real measures `μ` and `ν`](hyp:μ,ν), [a finite index set `s`](hyp:s),
[a degree assigned to each index](hyp:degree), and [a real coefficient assigned to each
index](hyp:coefficient) have [their finite Gaussian-weighted-moment combination bounded
by mean-embedding distance times the sum of absolute normalized coefficients](goal). -/
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

end Causalean.Mathlib.Probability.GaussianMeanEmbedding
