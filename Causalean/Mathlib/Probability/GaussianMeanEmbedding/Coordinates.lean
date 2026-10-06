module
public import Causalean.Mathlib.Probability.GaussianMeanEmbedding

/-!
# Quantitative Gaussian-feature coordinate bounds

This module turns norm control of the explicit Gaussian mean embedding into
simultaneous control of finitely many Gaussian-weighted monomial moments.  It
also supplies the normalization-adjusted finite coefficient bound used for
second-moment recovery.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Causalean.Mathlib.Probability.GaussianMeanEmbedding

/-- Given [two finite real measures](hyp:μ,ν) and [a natural-number degree](hyp:m),
[the difference between their Gaussian-weighted moments is bounded by the
Gaussian embedding distance divided by that coordinate's normalization](goal). -/
theorem abs_gaussianWeightedMoment_sub_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m : ℕ) :
    |(∫ r, gaussianWeightedMonomial m r ∂μ) -
        ∫ r, gaussianWeightedMonomial m r ∂ν| ≤
      ‖meanEmbedding gaussianFeatureMap μ -
          meanEmbedding gaussianFeatureMap ν‖ /
        gaussianFeatureNormalization m := by
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

/-- Given [two finite real measures](hyp:μ,ν), [a finite index set](hyp:s),
[a degree assigned to each index](hyp:degree), and [real coefficients](hyp:coefficient),
[the associated finite weighted-moment sum is bounded by the embedding distance
times the sum of absolute normalization-adjusted coefficients](goal). -/
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

/-- Given [a truncation order](hyp:N), [the second-moment recovery coefficient](goal)
is [the finite sum of reciprocal factorials divided by their Gaussian coordinate
normalizations](step:1). -/
def secondMomentRecoveryCoefficient (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    (1 / (k.factorial : ℝ)) /
      gaussianFeatureNormalization (2 * k + 2)

/-- Given [two finite real measures](hyp:μ,ν) and [a truncation order](hyp:N),
[the first N + 1 even Gaussian-weighted moment differences with exponential-series
coefficients are bounded by the recovery coefficient times their embedding distance](goal). -/
theorem abs_secondMomentWeightedSum_sub_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N : ℕ) :
    |∑ k ∈ Finset.range (N + 1), (1 / (k.factorial : ℝ)) *
        ((∫ r, gaussianWeightedMonomial (2 * k + 2) r ∂μ) -
          ∫ r, gaussianWeightedMonomial (2 * k + 2) r ∂ν)| ≤
      secondMomentRecoveryCoefficient N *
        ‖meanEmbedding gaussianFeatureMap μ -
          meanEmbedding gaussianFeatureMap ν‖ := by
  simpa [secondMomentRecoveryCoefficient] using
    (abs_sum_gaussianWeightedMoment_sub_le μ ν
      (Finset.range (N + 1)) (fun k => 2 * k + 2)
      (fun k => 1 / (k.factorial : ℝ)))

/-- Given [a natural-number Taylor index](hyp:k), [the normalization-adjusted
Taylor coefficient is at most its one-based index](goal). -/
theorem secondMomentRecoveryCoefficient_term_le (k : ℕ) :
    (1 / (k.factorial : ℝ)) /
        gaussianFeatureNormalization (2 * k + 2) ≤ (k + 1 : ℕ) := by
  have hchoose : (2 * (k + 1)).choose (k + 1) ≤ 2 ^ (2 * (k + 1)) :=
    Nat.choose_le_two_pow _ _
  have hfac_nat :
      (2 * (k + 1)).factorial ≤
        2 ^ (2 * (k + 1)) * (k + 1).factorial * (k + 1).factorial := by
    calc
      (2 * (k + 1)).factorial =
          (2 * (k + 1)).choose (k + 1) *
            (k + 1).factorial * (k + 1).factorial := by
              rw [show 2 * (k + 1) = (k + 1) + (k + 1) by omega]
              exact (Nat.add_choose_mul_factorial_mul_factorial
                (k + 1) (k + 1)).symm
      _ ≤ 2 ^ (2 * (k + 1)) *
            (k + 1).factorial * (k + 1).factorial := by
          gcongr
  have hfac :
      ((2 * (k + 1)).factorial : ℝ) ≤
        (2 : ℝ) ^ (2 * (k + 1)) *
          ((k + 1).factorial : ℝ) * ((k + 1).factorial : ℝ) := by
    exact_mod_cast hfac_nat
  have hnorm_pos :
      0 < gaussianFeatureNormalization (2 * k + 2) :=
    gaussianFeatureNormalization_pos _
  have hkfac_pos : 0 < (k.factorial : ℝ) := by positivity
  have hnorm_sq :
      gaussianFeatureNormalization (2 * k + 2) ^ 2 =
        (2 : ℝ) ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) := by
    unfold gaussianFeatureNormalization
    rw [Real.sq_sqrt]
    positivity
  have hsquare :
      ((1 / (k.factorial : ℝ)) /
          gaussianFeatureNormalization (2 * k + 2)) ^ 2 ≤
        ((k + 1 : ℕ) : ℝ) ^ 2 := by
    rw [Nat.factorial_succ] at hfac
    rw [div_pow, div_pow, one_pow, hnorm_sq]
    field_simp
    norm_num [Nat.cast_add, Nat.cast_one] at hfac ⊢
    convert hfac using 1 <;> ring_nf
  have hlhs_nonneg :
      0 ≤ (1 / (k.factorial : ℝ)) /
          gaussianFeatureNormalization (2 * k + 2) := by
    positivity
  simp only [Nat.cast_add, Nat.cast_one] at hsquare ⊢
  nlinarith

/-- [The sum of the 101 normalization-adjusted Taylor coefficients is at most
5151](goal). -/
theorem secondMomentRecoveryCoefficient_oneHundred_le :
    secondMomentRecoveryCoefficient 100 ≤ 5151 := by
  unfold secondMomentRecoveryCoefficient
  calc
    ∑ k ∈ Finset.range (100 + 1),
        (1 / (k.factorial : ℝ)) /
          gaussianFeatureNormalization (2 * k + 2)
      ≤ ∑ k ∈ Finset.range (100 + 1), ((k + 1 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact secondMomentRecoveryCoefficient_term_le k
    _ = 5151 := by norm_num

end Causalean.Mathlib.Probability.GaussianMeanEmbedding
