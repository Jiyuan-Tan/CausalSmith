/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PredictableVariance
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PredictableVarianceWeights

/-!
# Concentration of the predictable variance

This module expands the standardized Hájek predictable quadratic variation into the two
weighted prefix processes controlled by the finite-population moment estimates.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators Topology

namespace Causalean.Experimentation.DesignBased
open Causalean.Stat

open FinitePopulationMoments
open Filter ProbabilityTheory

/-- Given [a population size](hyp:N), [a proper sample size](hyp:K,hKlt), [population
outcomes](hyp:y), and [an ordering](hyp:π), the [explicit standardized predictable-variance
expression](goal) is the weighted sum of the remaining centered-square mean minus the squared
remaining centered mean. -/
noncomputable def srsPredictableVarianceExpression (N K : ℕ) (hKlt : K < N) (y : Fin N → ℝ)
    (π : PermutationSampleSpace N) : ℝ :=
  ((((N - K : ℕ) : ℝ) * (N : ℝ)) / ((K : ℝ) * popVar y)) *
    ∑ k ∈ Finset.range K,
      if hk : k < K then
        (((∑ i : Fin N, (y i - popMean y) ^ 2) -
            permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k
              (hk.le.trans hKlt.le) π) /
            (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) -
          (permutationRevealedSum (fun i => y i - popMean y) k
              (hk.le.trans hKlt.le) π) ^ 2 /
            (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2))
      else 0

/-- Given [population-size and sample-size sequences](hyp:N,K), [positive proper sample
sizes](hyp:hKpos,hKlt), [population outcomes](hyp:y) with [positive variances](hyp:hvar), and
[a row](hyp:n), [the standardized Hájek predictable quadratic variation equals its explicit
weighted prefix expression almost everywhere](goal). -/
theorem standardizedSrsPermutationHajekArray_predictableQuadraticVariation_ae_eq_expression
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (hvar : ∀ n, 0 < popVar (y n)) (n : ℕ) :
    (standardizedSrsPermutationHajekArray N K hKpos hKlt y).predictableQuadraticVariation n
      =ᵐ[(uniformPermutationDesign (N n)).toMeasure]
        srsPredictableVarianceExpression (N n) (K n) (hKlt n) (y n) := by
  have hstd := standardizedSrsPermutationHajekArray_predictableQuadraticVariation_ae_eq
    N K hKpos hKlt y hvar n
  have hraw := srsPermutationHajekArray_predictableQuadraticVariation_ae_eq
    N K hKpos hKlt y n
  filter_upwards [hstd, hraw] with π hstdπ hrawπ
  rw [hstdπ, hrawπ]
  unfold srsPredictableVarianceExpression srsSampleMeanVariance
  rw [Finset.mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hkRange
  have hk : k < K n := Finset.mem_range.mp hkRange
  simp only [hk, dite_true]
  rw [permutationNextVariance_eq_revealedSums (y n) k (hk.trans (hKlt n)) π]
  unfold hajekIncrementCoefficient
  have hKR : ((K n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (hKpos n).ne'
  have hNR : ((N n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast ((hKpos n).trans (hKlt n)).ne'
  have hLR : (((N n - K n : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt (hKlt n)).ne'
  have hvR : popVar (y n) ≠ 0 := (hvar n).ne'
  have hR : (((N n - k : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt (hk.trans (hKlt n))).ne'
  have hksN : k + 1 < N n := (Nat.succ_le_iff.mpr hk).trans_lt (hKlt n)
  have hRmNat : 0 < N n - k - 1 := by
    rw [Nat.sub_sub]
    exact Nat.sub_pos_of_lt hksN
  have hRm : (((N n - k - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hRmNat.ne'
  rw [Nat.cast_sub (hKlt n).le]
  field_simp



private lemma srsPredictableVarianceExpression_sub_one {N : ℕ} [Nonempty (Fin N)]
    (K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (y : Fin N → ℝ)
    (hvar : 0 < popVar y) (π : PermutationSampleSpace N) :
    srsPredictableVarianceExpression N K hKlt y π - 1 =
      ((((N - K : ℕ) : ℝ) * (N : ℝ)) / ((K : ℝ) * popVar y)) *
        ∑ k ∈ Finset.range K, (if hk : k < K then
          (- (permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k
                (hk.le.trans hKlt.le) π -
              (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)) /
              (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) -
            ((permutationRevealedSum (fun i => y i - popMean y) k
                (hk.le.trans hKlt.le) π) ^ 2 -
              (k : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * popVar y) /
              (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2))
        else 0) := by
  have hN : 2 ≤ N := by omega
  have hbase := predictableVariance_deterministicBaseline N K hKpos hKlt
    (popVar y) hvar
  have hS : (∑ i : Fin N, (y i - popMean y) ^ 2) =
      ((N - 1 : ℕ) : ℝ) * popVar y := by
    unfold popVar
    rw [Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    have hden : (N : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      linarith
    norm_num
    field_simp [hden]
  have hmean : popMean (fun i => (y i - popMean y) ^ 2) =
      (∑ i : Fin N, (y i - popMean y) ^ 2) / (N : ℝ) := by
    unfold popMean
    rw [Fintype.card_fin]
  rw [← hbase]
  unfold srsPredictableVarianceExpression
  rw [← mul_sub]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hkRange
  have hk : k < K := Finset.mem_range.mp hkRange
  simp only [hk, dite_true]
  rw [hmean, hS]
  ring


private lemma srsPredictableVarianceExpression_abs_sub_one_le {N : ℕ} [Nonempty (Fin N)]
    (K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (y : Fin N → ℝ)
    (hvar : 0 < popVar y) (π : PermutationSampleSpace N) :
    |srsPredictableVarianceExpression N K hKlt y π - 1| ≤
      ((((N - K : ℕ) : ℝ) * (N : ℝ)) / ((K : ℝ) * popVar y)) *
        (∑ k ∈ Finset.range K, if hk : k < K then
          |permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k
                (hk.le.trans hKlt.le) π -
              (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)| /
              (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) +
            ((permutationRevealedSum (fun i => y i - popMean y) k
                (hk.le.trans hKlt.le) π) ^ 2 +
              (k : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * popVar y) /
              (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2)
        else 0) := by
  rw [srsPredictableVarianceExpression_sub_one K hKpos hKlt y hvar π]
  have hc0 : 0 ≤ (((N - K : ℕ) : ℝ) * (N : ℝ)) /
      ((K : ℝ) * popVar y) := by positivity
  rw [abs_mul, abs_of_nonneg hc0]
  apply mul_le_mul_of_nonneg_left _ hc0
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k hkRange
  have hk : k < K := Finset.mem_range.mp hkRange
  simp only [hk, dite_true]
  have hR : (0 : ℝ) < (N - k : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hk.trans hKlt)
  have hRm : (0 : ℝ) < (N - k - 1 : ℕ) := by
    have hksN : k + 1 < N := (Nat.succ_le_iff.mpr hk).trans_lt hKlt
    rw [Nat.sub_sub]
    exact_mod_cast Nat.sub_pos_of_lt hksN
  have hd1 : 0 ≤ ((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2 := by
    positivity
  have hd2 : 0 ≤ ((N - k : ℕ) : ℝ) ^ 2 *
      ((N - k - 1 : ℕ) : ℝ) ^ 2 := by positivity
  have he0 : 0 ≤ (k : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * popVar y := by
    positivity
  calc
    |-(permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k
              (hk.le.trans hKlt.le) π -
            (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)) /
            (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) -
          ((permutationRevealedSum (fun i => y i - popMean y) k
              (hk.le.trans hKlt.le) π) ^ 2 -
            (k : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * popVar y) /
            (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2)| ≤
        |-(permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k
              (hk.le.trans hKlt.le) π -
            (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)) /
            (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)| +
          |((permutationRevealedSum (fun i => y i - popMean y) k
              (hk.le.trans hKlt.le) π) ^ 2 -
            (k : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * popVar y) /
            (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2)| :=
      abs_sub _ _
    _ = |permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k
              (hk.le.trans hKlt.le) π -
            (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)| /
            (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) +
          |(permutationRevealedSum (fun i => y i - popMean y) k
              (hk.le.trans hKlt.le) π) ^ 2 -
            (k : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * popVar y| /
            (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2) := by
      rw [abs_div, abs_div, abs_neg, abs_of_nonneg hd1, abs_of_nonneg hd2]
    _ ≤ |permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k
              (hk.le.trans hKlt.le) π -
            (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)| /
            (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) +
          ((permutationRevealedSum (fun i => y i - popMean y) k
              (hk.le.trans hKlt.le) π) ^ 2 +
            (k : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * popVar y) /
            (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2) := by
      gcongr
      let A : ℝ := (permutationRevealedSum (fun i => y i - popMean y) k
        (hk.le.trans hKlt.le) π) ^ 2
      let e : ℝ := (k : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * popVar y
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have he : 0 ≤ e := by simpa only [e] using he0
      simpa only [A, e, abs_of_nonneg hA, abs_of_nonneg he] using abs_sub A e

/-- Given [a population size](hyp:N), [a positive proper sample size](hyp:K,hKpos,hKlt),
[population outcomes](hyp:y), and [their positive variance](hyp:hvar), [the expected absolute
deviation of the standardized predictable variance from one is bounded by four square roots of
the maximal-deviation ratio plus four divided by the complementary-arm size](goal). -/
theorem srsPredictableVarianceExpression_integral_abs_sub_one_le {N : ℕ} [Nonempty (Fin N)]
    (K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (y : Fin N → ℝ)
    (hvar : 0 < popVar y) :
    ∫ π, |srsPredictableVarianceExpression N K hKlt y π - 1|
        ∂(uniformPermutationDesign N).toMeasure ≤
      4 * Real.sqrt (popMaxSqDev y /
          (((min K (N - K) : ℕ) : ℝ) * popVar y)) +
        4 / ((N - K : ℕ) : ℝ) := by
  let μ := (uniformPermutationDesign N).toMeasure
  let C : ℝ := (((N - K : ℕ) : ℝ) * (N : ℝ)) / ((K : ℝ) * popVar y)
  let F : PermutationSampleSpace N → ℝ := fun π => C *
    (∑ k ∈ Finset.range K, if hk : k < K then
      |permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k
            (hk.le.trans hKlt.le) π -
          (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)| /
          (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2) +
        ((permutationRevealedSum (fun i => y i - popMean y) k
            (hk.le.trans hKlt.le) π) ^ 2 +
          (k : ℝ) * ((N - k : ℕ) : ℝ) / (N : ℝ) * popVar y) /
          (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2)
      else 0)
  have hmono : (∫ π, |srsPredictableVarianceExpression N K hKlt y π - 1| ∂μ) ≤
      ∫ π, F π ∂μ := by
    apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
    exact fun π => srsPredictableVarianceExpression_abs_sub_one_le K hKpos hKlt y hvar π
  refine hmono.trans ?_
  let S1 : ℝ := ∑ k ∈ Finset.range K,
    (∫ π, |permutationRevealedSum (fun i => (y i - popMean y) ^ 2) (min k N)
          (min_le_right k N) π -
        (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)| ∂μ) /
      (((N - k : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) ^ 2)
  let S2 : ℝ := ∑ k ∈ Finset.range K,
    (∫ π, (permutationRevealedSum (fun i => y i - popMean y) (min k N)
          (min_le_right k N) π) ^ 2 ∂μ) /
      (((N - k : ℕ) : ℝ) ^ 2 * ((N - k - 1 : ℕ) : ℝ) ^ 2)
  have hF : (∫ π, F π ∂μ) = C * S1 + 2 * (C * S2) := by
    unfold F
    rw [integral_const_mul]
    rw [integral_finsetSum]
    · have hsum : (∑ i ∈ Finset.range K, ∫ a,
          (if hi : i < K then
            |permutationRevealedSum (fun j => (y j - popMean y) ^ 2) i
                (hi.le.trans hKlt.le) a -
              (i : ℝ) * popMean (fun j => (y j - popMean y) ^ 2)| /
                (((N - i : ℕ) : ℝ) * ((N - i - 1 : ℕ) : ℝ) ^ 2) +
            ((permutationRevealedSum (fun j => y j - popMean y) i
                (hi.le.trans hKlt.le) a) ^ 2 +
              (i : ℝ) * ((N - i : ℕ) : ℝ) / (N : ℝ) * popVar y) /
                (((N - i : ℕ) : ℝ) ^ 2 * ((N - i - 1 : ℕ) : ℝ) ^ 2)
          else 0) ∂μ) = S1 + 2 * S2 := by
        unfold S1 S2
        rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hkRange
        have hk : k < K := Finset.mem_range.mp hkRange
        simp only [hk, dite_true]
        have hmink : min k N = k := min_eq_left (hk.le.trans hKlt.le)
        simp only [hmink]
        by_cases hk0 : k = 0
        · subst k
          simp [permutationRevealedSum]
        rw [integral_add (Integrable.of_finite) (Integrable.of_finite)]
        rw [integral_div, integral_div]
        rw [integral_add (Integrable.of_finite) (Integrable.of_finite)]
        rw [integral_const]
        simp only [Measure.real, measure_univ, ENNReal.toReal_one]
        rw [integral_centered_revealedSum_sq y k (hk.le.trans hKlt.le)]
        · have habs : (∫ a,
              |permutationRevealedSum (fun j => (y j - popMean y) ^ 2) k
                    (hk.le.trans hKlt.le) a -
                (k : ℝ) * popMean (fun j => (y j - popMean y) ^ 2)| ∂μ) =
              ∫ a, |-(k : ℝ) * popMean (fun j => (y j - popMean y) ^ 2) +
                permutationRevealedSum (fun j => (y j - popMean y) ^ 2) k
                  (hk.le.trans hKlt.le) a| ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with a
            congr 1
            ring
          rw [habs]
          have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (hKpos.trans hKlt).ne'
          have hR : ((N - k : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.sub_pos_of_lt (hk.trans hKlt)).ne'
          have hksN : k + 1 < N := (Nat.succ_le_iff.mpr hk).trans_lt hKlt
          have hRmNat : 0 < N - k - 1 := by
            rw [Nat.sub_sub]
            exact Nat.sub_pos_of_lt hksN
          have hRm : ((N - k - 1 : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast hRmNat.ne'
          field_simp [hkR, hNR, hR, hRm]
          rw [Nat.cast_sub (hk.trans hKlt).le]
          simp only [smul_eq_mul]
          field_simp [hNR]
          ring
        · exact Nat.pos_of_ne_zero hk0
        · omega
      rw [hsum]
      ring
    · intro k hk
      exact Integrable.of_finite
  rw [hF]
  have hfirst := predictableVariance_firstWeightedEstimate K hKpos hKlt y hvar
  have hsecond := predictableVariance_secondWeightedEstimate K hKpos hKlt y hvar
  change C * S1 ≤ 4 * Real.sqrt (popMaxSqDev y /
    (((min K (N - K) : ℕ) : ℝ) * popVar y)) at hfirst
  change C * S2 ≤ 2 / ((N - K : ℕ) : ℝ) at hsecond
  have htwice := mul_le_mul_of_nonneg_left hsecond (by norm_num : (0 : ℝ) ≤ 2)
  calc
    C * S1 + 2 * (C * S2) ≤
        4 * Real.sqrt (popMaxSqDev y /
          (((min K (N - K) : ℕ) : ℝ) * popVar y)) +
          2 * (2 / ((N - K : ℕ) : ℝ)) := add_le_add hfirst htwice
    _ = 4 * Real.sqrt (popMaxSqDev y /
          (((min K (N - K) : ℕ) : ℝ) * popVar y)) +
        4 / ((N - K : ℕ) : ℝ) := by ring


private lemma popVar_le_two_popMaxSqDev {N : ℕ} [Nonempty (Fin N)] (hN : 2 ≤ N) (y : Fin N → ℝ) :
    popVar y ≤ 2 * popMaxSqDev y := by
  have hM : 0 ≤ popMaxSqDev y := by
    let i : Fin N := Classical.choice (inferInstance : Nonempty (Fin N))
    exact (sq_nonneg (y i - popMean y)).trans (by
      unfold popMaxSqDev
      exact Finset.le_sup' (fun j : Fin N => (y j - popMean y) ^ 2) (Finset.mem_univ i))
  have hsum : (∑ i : Fin N, (y i - popMean y) ^ 2) ≤ (N : ℝ) * popMaxSqDev y := by
    rw [show (N : ℝ) * popMaxSqDev y =
      ∑ _i : Fin N, popMaxSqDev y by simp]
    apply Finset.sum_le_sum
    intro i hi
    unfold popMaxSqDev
    exact Finset.le_sup' (fun j : Fin N => (y j - popMean y) ^ 2) hi
  unfold popVar
  rw [Fintype.card_fin]
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : (0 : ℝ) < N - 1 := by linarith
  rw [div_le_iff₀ hden]
  have hNR : (N : ℝ) ≤ 2 * ((N : ℝ) - 1) := by linarith
  calc
    (∑ i : Fin N, (y i - popMean y) ^ 2) ≤ (N : ℝ) * popMaxSqDev y := hsum
    _ ≤ (2 * ((N : ℝ) - 1)) * popMaxSqDev y :=
      mul_le_mul_of_nonneg_right hNR hM
    _ = 2 * popMaxSqDev y * ((N : ℝ) - 1) := by ring

private lemma inv_complementaryArm_le_two_maximalDeviationRatio {N : ℕ} [Nonempty (Fin N)]
    (K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (y : Fin N → ℝ)
    (hvar : 0 < popVar y) :
    (1 : ℝ) / ((N - K : ℕ) : ℝ) ≤
      2 * (popMaxSqDev y /
        (((min K (N - K) : ℕ) : ℝ) * popVar y)) := by
  let L := N - K
  let m := min K L
  have hL : 0 < L := Nat.sub_pos_of_lt hKlt
  have hm : 0 < m := lt_min hKpos hL
  have hN : 2 ≤ N := by omega
  have hvarmax := popVar_le_two_popMaxSqDev hN y
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmL : m ≤ L := min_le_right K L
  calc
    (1 : ℝ) / (L : ℝ) ≤ 1 / (m : ℝ) :=
      one_div_le_one_div_of_le hmR (by exact_mod_cast hmL)
    _ ≤ 2 * (popMaxSqDev y / ((m : ℝ) * popVar y)) := by
      rw [div_le_iff₀ hmR]
      field_simp [ne_of_gt hmR, hvar.ne']
      nlinarith

/-- Given [population-size and sample-size sequences](hyp:N,K), [positive proper sample
sizes](hyp:hKpos,hKlt), and [population outcomes](hyp:y) with [positive variances](hyp:hvar),
if [the Li–Ding maximal-deviation sufficient-condition ratio tends to zero](hyp:hmax), then [the expected absolute
deviation of the explicit standardized predictable variance from one tends to zero](goal). -/
theorem srsPredictableVarianceExpression_integral_abs_sub_one_tendsto_zero
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (hvar : ∀ n, 0 < popVar (y n))
    (hmax : Tendsto (fun n => popMaxSqDev (y n) /
      (((min (K n) (N n - K n) : ℕ) : ℝ) * popVar (y n))) atTop (nhds 0)) :
    Tendsto (fun n => ∫ π,
      |srsPredictableVarianceExpression (N n) (K n) (hKlt n) (y n) π - 1|
        ∂(uniformPermutationDesign (N n)).toMeasure) atTop (nhds 0) := by
  let r : ℕ → ℝ := fun n => popMaxSqDev (y n) /
    (((min (K n) (N n - K n) : ℕ) : ℝ) * popVar (y n))
  let q : ℕ → ℝ := fun n => (1 : ℝ) / ((N n - K n : ℕ) : ℝ)
  change Tendsto r atTop (nhds 0) at hmax
  have hr0 : ∀ n, 0 ≤ r n := by
    intro n
    have hM : 0 ≤ popMaxSqDev (y n) := by
      let i : Fin (N n) := Classical.choice (inferInstance : Nonempty (Fin (N n)))
      exact (sq_nonneg (y n i - popMean (y n))).trans (by
        unfold popMaxSqDev
        exact Finset.le_sup' (fun j : Fin (N n) => (y n j - popMean (y n)) ^ 2)
          (Finset.mem_univ i))
    have hm : 0 < min (K n) (N n - K n) :=
      lt_min (hKpos n) (Nat.sub_pos_of_lt (hKlt n))
    exact div_nonneg hM (mul_pos (by exact_mod_cast hm) (hvar n)).le
  have hq0 : ∀ n, 0 ≤ q n := fun n => by positivity
  have hqle : ∀ n, q n ≤ 2 * r n := by
    intro n
    exact inv_complementaryArm_le_two_maximalDeviationRatio (K n) (hKpos n) (hKlt n) (y n) (hvar n)
  have hsqrt : Tendsto (fun n => Real.sqrt (r n)) atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hmax
    simpa only [Real.sqrt_zero, Function.comp_def] using this
  have hq : Tendsto q atTop (nhds 0) := by
    apply squeeze_zero (fun n => hq0 n) hqle
    simpa using hmax.const_mul 2
  have hbound : Tendsto (fun n => 4 * Real.sqrt (r n) + 4 * q n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hsqrt).add (tendsto_const_nhds.mul hq)
  refine squeeze_zero ?_ ?_ hbound
  · intro n
    exact integral_nonneg fun π => abs_nonneg _
  · intro n
    simpa [r, q, div_eq_mul_inv] using
      srsPredictableVarianceExpression_integral_abs_sub_one_le
        (K n) (hKpos n) (hKlt n) (y n) (hvar n)


/-- Given [population-size and sample-size sequences](hyp:N,K), [positive proper sample
sizes](hyp:hKpos,hKlt), and [population outcomes](hyp:y) with [positive variances](hyp:hvar),
if [the Li–Ding maximal-deviation sufficient-condition ratio tends to zero](hyp:hmax), then [the explicit standardized
predictable variance converges in probability to one](goal). -/
theorem srsPredictableVarianceExpression_tendstoInProbability
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (hvar : ∀ n, 0 < popVar (y n))
    (hmax : Tendsto (fun n => popMaxSqDev (y n) /
      (((min (K n) (N n - K n) : ℕ) : ℝ) * popVar (y n))) atTop (nhds 0)) :
    TendstoInProbability (fun n => (uniformPermutationDesign (N n)).toMeasure)
      (fun n => srsPredictableVarianceExpression (N n) (K n) (hKlt n) (y n)) 1 := by
  rw [tendstoInProbability_iff_real]
  have hL1 := srsPredictableVarianceExpression_integral_abs_sub_one_tendsto_zero
    N K hKpos hKlt y hvar hmax
  intro ε hε
  apply (ENNReal.tendsto_toReal_zero_iff).mp
  apply squeeze_zero (fun _ => measureReal_nonneg)
  · intro n
    change Measure.real ((uniformPermutationDesign (N n)).toMeasure)
        {π | ε ≤ |srsPredictableVarianceExpression (N n) (K n) (hKlt n) (y n) π - 1|} ≤
      (∫ π, |srsPredictableVarianceExpression (N n) (K n) (hKlt n) (y n) π - 1|
        ∂(uniformPermutationDesign (N n)).toMeasure) / ε
    rw [le_div_iff₀ hε]
    simpa [mul_comm] using mul_meas_ge_le_integral_of_nonneg
      (μ := (uniformPermutationDesign (N n)).toMeasure)
      (f := fun π =>
        |srsPredictableVarianceExpression (N n) (K n) (hKlt n) (y n) π - 1|)
      (Filter.Eventually.of_forall fun π => abs_nonneg _)
      Integrable.of_finite ε
  · simpa using hL1.div_const ε

/-- Given [population-size and sample-size sequences](hyp:N,K), [positive proper sample
sizes](hyp:hKpos,hKlt), and [population outcomes](hyp:y) with [positive variances](hyp:hvar),
if [the Li–Ding maximal-deviation sufficient-condition ratio tends to zero](hyp:hmax), then [the standardized Hájek
array's predictable quadratic variation converges in probability to one](goal). -/
theorem standardizedSrsPermutationHajekArray_predictableQuadraticVariation_tendstoInProbability
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (hvar : ∀ n, 0 < popVar (y n))
    (hmax : Tendsto (fun n => popMaxSqDev (y n) /
      (((min (K n) (N n - K n) : ℕ) : ℝ) * popVar (y n))) atTop (nhds 0)) :
    TendstoInProbability (fun n => (uniformPermutationDesign (N n)).toMeasure)
      (standardizedSrsPermutationHajekArray N K hKpos hKlt y).predictableQuadraticVariation
      1 := by
  have hexpr := srsPredictableVarianceExpression_tendstoInProbability N K hKpos hKlt y hvar hmax
  rw [tendstoInProbability_iff_real] at hexpr ⊢
  intro ε hε
  have heq := standardizedSrsPermutationHajekArray_predictableQuadraticVariation_ae_eq_expression
    N K hKpos hKlt y hvar
  have hmeasure : ∀ n,
      (uniformPermutationDesign (N n)).toMeasure
          {π | ε ≤
            |((standardizedSrsPermutationHajekArray N K hKpos hKlt
              y).predictableQuadraticVariation) n π - 1|} =
        (uniformPermutationDesign (N n)).toMeasure
          {π | ε ≤ |srsPredictableVarianceExpression
            (N n) (K n) (hKlt n) (y n) π - 1|} := by
    intro n
    apply measure_congr
    filter_upwards [heq n] with π hπ
    change
      (ε ≤ |((standardizedSrsPermutationHajekArray N K hKpos hKlt
        y).predictableQuadraticVariation) n π - 1|) =
      (ε ≤ |srsPredictableVarianceExpression (N n) (K n) (hKlt n) (y n) π - 1|)
    rw [hπ]
  simp_rw [hmeasure]
  exact hexpr ε hε


end Causalean.Experimentation.DesignBased
