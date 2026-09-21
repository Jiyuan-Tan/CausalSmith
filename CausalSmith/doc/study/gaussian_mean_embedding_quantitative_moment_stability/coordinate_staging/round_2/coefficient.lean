import Causalean.Mathlib.Probability.GaussianMeanEmbedding.Coordinates

/-!
# Finite recovery coefficient for the second moment

This module specializes the generic finite-coordinate inequality to the even
Taylor moments and certifies the normalization-adjusted coefficient `5151`.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Causalean.Mathlib.Probability.GaussianMeanEmbedding

open Causalean.Mathlib.Probability.GaussianMeanEmbedding

/-- [A truncation index `N`](hyp:N) determines [the normalization-adjusted coefficient
sum](goal) used to recover a raw second moment from its Taylor terms. -/
def secondMomentRecoveryCoefficient (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    (1 / (k.factorial : ℝ)) /
      gaussianFeatureNormalization (2 * k + 2)

/-- [Two finite real measures `μ` and `ν`](hyp:μ,ν) and [a truncation index `N`](hyp:N)
have [their first `N + 1` even Gaussian-weighted Taylor moments bounded by the recovery
coefficient times Gaussian mean-embedding distance](goal). -/
theorem abs_secondMomentWeightedSum_sub_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N : ℕ) :
    |∑ k ∈ Finset.range (N + 1), (1 / (k.factorial : ℝ)) *
        ((∫ r, gaussianWeightedMonomial (2 * k + 2) r ∂μ) -
          ∫ r, gaussianWeightedMonomial (2 * k + 2) r ∂ν)| ≤
      secondMomentRecoveryCoefficient N *
        ‖meanEmbedding gaussianFeatureMap μ -
          meanEmbedding gaussianFeatureMap ν‖ := by
  -- Specialize `abs_sum_gaussianWeightedMoment_sub_le` with degree `2*k+2`
  -- and coefficient `1/k!`; positivity removes the coefficient absolute value.
  simpa [secondMomentRecoveryCoefficient] using
    (abs_sum_gaussianWeightedMoment_sub_le μ ν
      (Finset.range (N + 1)) (fun k => 2 * k + 2)
      (fun k => 1 / (k.factorial : ℝ)))

/-- [A Taylor index `k`](hyp:k) has [a normalization-adjusted coefficient no greater
than its one-based index](goal), the termwise central-binomial estimate behind 5151. -/
theorem secondMomentRecoveryCoefficient_term_le (k : ℕ) :
    (1 / (k.factorial : ℝ)) /
        gaussianFeatureNormalization (2 * k + 2) ≤ (k + 1 : ℕ) := by
  -- Square both nonnegative sides.  After rewriting the factorial quotient,
  -- the claim is `choose (2*(k+1)) (k+1) ≤ 2^(2*(k+1))`, exactly
  -- `Nat.choose_le_two_pow`; `Nat.add_choose_mul_factorial_mul_factorial`
  -- supplies the factorial identity without natural-number division.
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

/-- [The 101-term normalization-adjusted recovery coefficient is at most 5151](goal). -/
theorem secondMomentRecoveryCoefficient_oneHundred_le :
    secondMomentRecoveryCoefficient 100 ≤ 5151 := by
  -- Sum `secondMomentRecoveryCoefficient_term_le` for `k < 101`, then
  -- normalize the closed finite arithmetic sum with `norm_num`.
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
