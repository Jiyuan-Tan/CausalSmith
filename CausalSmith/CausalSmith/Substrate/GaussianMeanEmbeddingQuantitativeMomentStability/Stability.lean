import CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability.Taylor

/-!
# Quantitative second-moment stability from Gaussian mean embeddings

This module combines finite coordinate control with a uniform approximation
remainder.  It exports the `[0,5]`, degree-202, coefficient-`5151` theorem and
its explicit contrapositive lower bound.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability

open CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery

/-- A finite Taylor approximation with uniform error `ε` on a common support
turns coordinate control into a second-moment bound with coefficient
`secondMomentRecoveryCoefficient N` and total remainder `2ε`. -/
theorem secondMoment_sub_le_of_taylor_error
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hμ : μ (Icc (0 : ℝ) R)ᶜ = 0) (hν : ν (Icc (0 : ℝ) R)ᶜ = 0)
    (happrox : ∀ r ∈ Icc (0 : ℝ) R,
      |r ^ 2 - gaussianWeight r *
          (secondMomentTaylorPolynomial N).eval r| ≤ ε) :
    |(∫ r, r ^ 2 ∂μ) - ∫ r, r ^ 2 ∂ν| ≤
      secondMomentRecoveryCoefficient N *
          ‖meanEmbedding gaussianFeatureMap μ -
            meanEmbedding gaussianFeatureMap ν‖ +
        2 * ε := by
  -- Restrict both laws to the compact interval.  Bound each integral of the
  -- pointwise approximation error by `ε` using probability mass one; expand
  -- the polynomial integral into weighted moments and invoke the finite-sum
  -- coordinate inequality from `Coordinates`.  Concretely, obtain support-a.e.
  -- facts with `ae_iff`, use `Measure.restrict_eq_self_of_ae_mem` plus
  -- `Continuous.integrableOn_Icc` for the raw square and the weighted
  -- polynomial, and apply `norm_integral_le_of_norm_le_const` to each error.
  -- Rewrite the weighted-polynomial integrals with
  -- `secondMomentTaylorPolynomial_eval`, `integral_finset_sum`, and
  -- `integrable_gaussianWeightedMonomial`; the resulting middle difference is
  -- exactly the sum bounded by `abs_secondMomentWeightedSum_sub_le`.
  let S : Set ℝ := Icc 0 R
  let q : ℝ → ℝ := fun r =>
    gaussianWeight r * (secondMomentTaylorPolynomial N).eval r
  have hμS : ∀ᵐ r ∂μ, r ∈ S := by
    rw [ae_iff]
    exact hμ
  have hνS : ∀ᵐ r ∂ν, r ∈ S := by
    rw [ae_iff]
    exact hν
  have hμrestrict : μ.restrict S = μ :=
    Measure.restrict_eq_self_of_ae_mem hμS
  have hνrestrict : ν.restrict S = ν :=
    Measure.restrict_eq_self_of_ae_mem hνS
  have hsquare_cont : Continuous (fun r : ℝ => r ^ 2) := by fun_prop
  have hq_cont : Continuous q := by
    dsimp [q]
    unfold gaussianWeight
    fun_prop
  have hsquareμ : Integrable (fun r : ℝ => r ^ 2) μ := by
    have h := hsquare_cont.integrableOn_Icc (a := (0 : ℝ)) (b := R) (μ := μ)
    change Integrable (fun r : ℝ => r ^ 2) (μ.restrict S) at h
    rwa [hμrestrict] at h
  have hsquareν : Integrable (fun r : ℝ => r ^ 2) ν := by
    have h := hsquare_cont.integrableOn_Icc (a := (0 : ℝ)) (b := R) (μ := ν)
    change Integrable (fun r : ℝ => r ^ 2) (ν.restrict S) at h
    rwa [hνrestrict] at h
  have hqμ : Integrable q μ := by
    have h := hq_cont.integrableOn_Icc (a := (0 : ℝ)) (b := R) (μ := μ)
    change Integrable q (μ.restrict S) at h
    rwa [hμrestrict] at h
  have hqν : Integrable q ν := by
    have h := hq_cont.integrableOn_Icc (a := (0 : ℝ)) (b := R) (μ := ν)
    change Integrable q (ν.restrict S) at h
    rwa [hνrestrict] at h
  have herrorμ :
      |(∫ r, r ^ 2 ∂μ) - ∫ r, q r ∂μ| ≤ ε := by
    have hbound : ∀ᵐ r ∂μ, ‖r ^ 2 - q r‖ ≤ ε :=
      hμS.mono fun r hr => by
        simpa only [S, q, Real.norm_eq_abs] using happrox r hr
    rw [← integral_sub hsquareμ hqμ, ← Real.norm_eq_abs]
    simpa using norm_integral_le_of_norm_le_const hbound
  have herrorν :
      |(∫ r, r ^ 2 ∂ν) - ∫ r, q r ∂ν| ≤ ε := by
    have hbound : ∀ᵐ r ∂ν, ‖r ^ 2 - q r‖ ≤ ε :=
      hνS.mono fun r hr => by
        simpa only [S, q, Real.norm_eq_abs] using happrox r hr
    rw [← integral_sub hsquareν hqν, ← Real.norm_eq_abs]
    simpa using norm_integral_le_of_norm_le_const hbound
  have hq_integral (m : Measure ℝ) [IsFiniteMeasure m] :
      (∫ r, q r ∂m) =
        ∑ k ∈ Finset.range (N + 1), (1 / (k.factorial : ℝ)) *
          ∫ r, gaussianWeightedMonomial (2 * k + 2) r ∂m := by
    simp only [q, secondMomentTaylorPolynomial_eval, Finset.mul_sum]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      have hfun :
          (fun r : ℝ => gaussianWeight r *
              (r ^ (2 * k + 2) / (k.factorial : ℝ))) =
            fun r => (1 / (k.factorial : ℝ)) *
              gaussianWeightedMonomial (2 * k + 2) r := by
        funext r
        simp only [gaussianWeightedMonomial]
        ring
      rw [hfun, integral_const_mul]
    · intro k hk
      rw [show (fun r : ℝ => gaussianWeight r *
          (r ^ (2 * k + 2) / (k.factorial : ℝ))) =
          fun r => (1 / (k.factorial : ℝ)) *
            gaussianWeightedMonomial (2 * k + 2) r by
        funext r
        simp only [gaussianWeightedMonomial]
        ring]
      exact (integrable_gaussianWeightedMonomial m (2 * k + 2)).const_mul _
  have hmiddle :
      |(∫ r, q r ∂μ) - ∫ r, q r ∂ν| ≤
        secondMomentRecoveryCoefficient N *
          ‖meanEmbedding gaussianFeatureMap μ -
            meanEmbedding gaussianFeatureMap ν‖ := by
    rw [hq_integral μ, hq_integral ν, ← Finset.sum_sub_distrib]
    simpa only [mul_sub] using abs_secondMomentWeightedSum_sub_le μ ν N
  calc
    |(∫ r, r ^ 2 ∂μ) - ∫ r, r ^ 2 ∂ν| ≤
        |(∫ r, r ^ 2 ∂μ) - ∫ r, q r ∂μ| +
          |(∫ r, q r ∂μ) - ∫ r, q r ∂ν| +
          |(∫ r, q r ∂ν) - ∫ r, r ^ 2 ∂ν| := by
      calc
        _ ≤ |(∫ r, r ^ 2 ∂μ) - ∫ r, q r ∂μ| +
            |(∫ r, q r ∂μ) - ∫ r, r ^ 2 ∂ν| :=
          abs_sub_le _ _ _
        _ ≤ _ := by
          have htri :
              |(∫ r, q r ∂μ) - ∫ r, r ^ 2 ∂ν| ≤
                |(∫ r, q r ∂μ) - ∫ r, q r ∂ν| +
                  |(∫ r, q r ∂ν) - ∫ r, r ^ 2 ∂ν| :=
            abs_sub_le _ _ _
          linarith
    _ ≤ ε +
          secondMomentRecoveryCoefficient N *
            ‖meanEmbedding gaussianFeatureMap μ -
              meanEmbedding gaussianFeatureMap ν‖ + ε := by
      gcongr
      simpa only [abs_sub_comm] using herrorν
    _ = secondMomentRecoveryCoefficient N *
          ‖meanEmbedding gaussianFeatureMap μ -
            meanEmbedding gaussianFeatureMap ν‖ + 2 * ε := by ring

/-- For probability measures concentrated on `[0,5]`, the difference of raw
second moments is at most `5151` times the distance between their explicit
Gaussian mean embeddings plus the exact rational remainder `10⁻¹⁵`. -/
theorem gaussian_meanEmbedding_secondMoment_stability_Icc_zero_five
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (Icc (0 : ℝ) 5)ᶜ = 0) (hν : ν (Icc (0 : ℝ) 5)ᶜ = 0) :
    |(∫ r, r ^ 2 ∂μ) - ∫ r, r ^ 2 ∂ν| ≤
      5151 * ‖meanEmbedding gaussianFeatureMap μ -
        meanEmbedding gaussianFeatureMap ν‖ +
      (1 / 10 ^ 15 : ℝ) := by
  -- Apply `secondMoment_sub_le_of_taylor_error` with `R = 5`, `N = 100`,
  -- and the explicit factorial-tail remainder from `Taylor`.  Then enlarge
  -- the two nonnegative terms separately using
  -- `secondMomentRecoveryCoefficient_oneHundred_le`, norm nonnegativity, and
  -- `two_taylorRemainder_oneHundred_le`.
  let ε : ℝ :=
    25 * (25 ^ 101 / ((101 : ℕ).factorial : ℝ)) * (102 / 77)
  have hbound := secondMoment_sub_le_of_taylor_error
    (R := 5) (N := 100) (ε := ε) μ ν (by norm_num) (by
      dsimp [ε]
      positivity) hμ hν (by
        intro r hr
        dsimp [ε]
        simpa only [gaussianWeight] using
          abs_sq_sub_gaussianWeightedTaylor_oneHundred_le hr)
  calc
    |(∫ r, r ^ 2 ∂μ) - ∫ r, r ^ 2 ∂ν| ≤
        secondMomentRecoveryCoefficient 100 *
            ‖meanEmbedding gaussianFeatureMap μ -
              meanEmbedding gaussianFeatureMap ν‖ +
          2 * ε := hbound
    _ ≤ 5151 * ‖meanEmbedding gaussianFeatureMap μ -
            meanEmbedding gaussianFeatureMap ν‖ +
          (1 / 10 ^ 15 : ℝ) :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          secondMomentRecoveryCoefficient_oneHundred_le (norm_nonneg _))
        (by
          dsimp [ε]
          exact two_taylorRemainder_oneHundred_le)

/-- If the certified second-moment gap of two probability laws on `[0,5]`
exceeds `10⁻¹⁵`, their explicit Gaussian mean-embedding distance is at least
the positive quantity `(gap - 10⁻¹⁵) / 5151`. -/
theorem gaussian_meanEmbedding_norm_lowerBound_of_secondMoment_gap
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (Icc (0 : ℝ) 5)ᶜ = 0) (hν : ν (Icc (0 : ℝ) 5)ᶜ = 0)
    (hgap : (1 / 10 ^ 15 : ℝ) <
      |(∫ r, r ^ 2 ∂μ) - ∫ r, r ^ 2 ∂ν|) :
    0 < (|(∫ r, r ^ 2 ∂μ) - ∫ r, r ^ 2 ∂ν| -
          (1 / 10 ^ 15 : ℝ)) / 5151 ∧
      (|(∫ r, r ^ 2 ∂μ) - ∫ r, r ^ 2 ∂ν| -
          (1 / 10 ^ 15 : ℝ)) / 5151 ≤
        ‖meanEmbedding gaussianFeatureMap μ -
          meanEmbedding gaussianFeatureMap ν‖ := by
  -- The first conjunct is immediate from `hgap` and positivity of `5151`.
  -- For the second, specialize the preceding stability theorem, subtract the
  -- remainder, and divide by the positive coefficient; `linarith`/`nlinarith`
  -- can perform the rearrangement once the norm is named as a real quantity.
  have hbound :=
    gaussian_meanEmbedding_secondMoment_stability_Icc_zero_five μ ν hμ hν
  constructor
  · positivity
  · nlinarith

end CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability
