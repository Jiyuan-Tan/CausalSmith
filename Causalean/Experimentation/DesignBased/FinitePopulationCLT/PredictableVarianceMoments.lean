/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PermutationTransport
public import Causalean.Experimentation.DesignBased.FinitePopulationVariance
public import Causalean.Mathlib.Probability.LimitTheorems.Approximation.CharFunBound

/-!
# Moment bounds for permutation prefixes

This module gives exact second moments and an absolute first-moment bound for centered
prefix sums of a uniform permutation, together with the remaining-variance identity used in
Hájek’s finite-population martingale.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Experimentation.DesignBased
open Causalean.Stat

open FinitePopulationMoments
open ProbabilityTheory

/-- Given [population outcomes](hyp:y), [a positive feasible prefix length](hyp:k,hk,hkpos),
and [an ordering](hyp:π), [the revealed sum is the prefix length times the prefix mean](goal). -/
lemma permutationRevealedSum_eq_mul_permutationSampleMean {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) (hkpos : 0 < k) (π : PermutationSampleSpace N) :
    permutationRevealedSum y k hk π = (k : ℝ) * permutationSampleMean k hk y π := by
  unfold permutationRevealedSum permutationSampleMean
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
  field_simp

/-- Given [population outcomes](hyp:y), [a positive feasible prefix length](hyp:k,hk,hkpos),
and [a population of at least two units](hyp:hN), [the expected absolute centered prefix sum is
bounded by its exact standard deviation](goal). -/
lemma integral_abs_permutationRevealedSum_sub_mean_le {N : ℕ} (y : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) (hkpos : 0 < k) (hN : 2 ≤ N) :
    ∫ π, |permutationRevealedSum y k hk π - (k : ℝ) * popMean y|
        ∂(uniformPermutationDesign N).toMeasure ≤
      (k : ℝ) * Real.sqrt ((1 / (k : ℝ) - 1 / (N : ℝ)) * popVar y) := by
  let D := uniformPermutationDesign N
  let μ := D.toMeasure
  let X := permutationSampleMean k hk y
  have hXlp : MemLp X 2 μ := D.memLp_toMeasure X 2
  have hdiffLp : MemLp (fun π => X π - popMean y) 2 μ :=
    hXlp.sub (memLp_const (popMean y))
  have hcs :=
    Causalean.Mathlib.Probability.ConvergingTogether.integral_abs_le_sqrt_integral_sq
      μ (fun π => X π - popMean y) hdiffLp
  have hmean : ∫ π, X π ∂μ = popMean y := by
    rw [FiniteDesign.integral_toMeasure]
    exact uniformPermutationDesign_E_permutationSampleMean k hk hkpos y
  have hsq : ∫ π, (X π - popMean y) ^ 2 ∂μ =
      (1 / (k : ℝ) - 1 / (N : ℝ)) * popVar y := by
    rw [← hmean]
    rw [← variance_eq_integral (measurable_of_finite X).aemeasurable]
    rw [FiniteDesign.variance_toMeasure]
    exact uniformPermutationDesign_Var_permutationSampleMean k hk hkpos hN y
  have hcs' : ∫ π, |X π - popMean y| ∂μ ≤ Real.sqrt
      ((1 / (k : ℝ) - 1 / (N : ℝ)) * popVar y) := by
    simpa only [Real.norm_eq_abs, sq_abs, hsq] using hcs
  have hkR : (0 : ℝ) ≤ k := by positivity
  change (∫ π, |permutationRevealedSum y k hk π - (k : ℝ) * popMean y| ∂μ) ≤ _
  calc
    (∫ π, |permutationRevealedSum y k hk π - (k : ℝ) * popMean y| ∂μ) =
        (k : ℝ) * ∫ π, |X π - popMean y| ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with π
      rw [permutationRevealedSum_eq_mul_permutationSampleMean y k hk hkpos π]
      dsimp only [X]
      rw [← mul_sub, abs_mul, abs_of_nonneg hkR]
    _ ≤ (k : ℝ) * Real.sqrt
        ((1 / (k : ℝ) - 1 / (N : ℝ)) * popVar y) :=
      mul_le_mul_of_nonneg_left hcs' hkR

/-- Given [population outcomes](hyp:y), [centering the outcomes preserves their finite-population
variance](goal). -/
lemma popVar_centered {N : ℕ} [Nonempty (Fin N)] (y : Fin N → ℝ) :
    popVar (fun i => y i - popMean y) = popVar y := by
  unfold popVar
  rw [popMean_centered_eq_zero]
  simp only [sub_zero]

/-- Given [a population of at least two units](hyp:hN) and [population outcomes](hyp:y), [their
finite-population variance is nonnegative](goal). -/
lemma popVar_nonneg_of_two_le {N : ℕ} (hN : 2 ≤ N) (y : Fin N → ℝ) :
    0 ≤ popVar y := by
  unfold popVar
  apply div_nonneg
  · positivity
  · rw [Fintype.card_fin]
    exact sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ N))

/-- Given [population outcomes](hyp:y), [a positive feasible prefix length](hyp:k,hk,hkpos),
and [a population of at least two units](hyp:hN), [the expected absolute fluctuation of the
revealed centered-square sum has the sampling-without-replacement bound](goal). -/
lemma integral_abs_centeredSq_revealedSum_le {N : ℕ} [Nonempty (Fin N)] (y : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) (hkpos : 0 < k) (hN : 2 ≤ N) :
    ∫ π, |permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k hk π -
        (k : ℝ) * popMean (fun i => (y i - popMean y) ^ 2)|
        ∂(uniformPermutationDesign N).toMeasure ≤
      Real.sqrt ((((k : ℝ) * (N - k : ℕ) / (N : ℝ)) *
        popMaxSqDev y * popVar y)) := by
  let w : Fin N → ℝ := fun i => (y i - popMean y) ^ 2
  have hraw := integral_abs_permutationRevealedSum_sub_mean_le w k hk hkpos hN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hN)
  have hfactor : 0 ≤ 1 / (k : ℝ) - 1 / (N : ℝ) := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hkR (by exact_mod_cast hk))
  have hwvar0 : 0 ≤ popVar w := popVar_nonneg_of_two_le hN w
  have hMv : popVar w ≤ popMaxSqDev y * popVar y :=
    popVar_centeredSq_le_max_mul_popVar (by simpa using hN) y
  have hleft0 : 0 ≤ (k : ℝ) *
      Real.sqrt ((1 / (k : ℝ) - 1 / (N : ℝ)) * popVar w) := by positivity
  refine hraw.trans ?_
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hfactor hwvar0)]
  have hmul := mul_le_mul_of_nonneg_left hMv hfactor
  have hkn : ((k : ℝ) ^ 2) * (1 / (k : ℝ) - 1 / (N : ℝ)) =
      (k : ℝ) * (N - k : ℕ) / (N : ℝ) := by
    rw [Nat.cast_sub hk]
    field_simp [ne_of_gt hkR, ne_of_gt hNR]
  calc
    (k : ℝ) ^ 2 * ((1 / (k : ℝ) - 1 / (N : ℝ)) * popVar w) =
        ((k : ℝ) ^ 2 * (1 / (k : ℝ) - 1 / (N : ℝ))) * popVar w := by ring
    _ ≤ ((k : ℝ) ^ 2 * (1 / (k : ℝ) - 1 / (N : ℝ))) *
        (popMaxSqDev y * popVar y) := by
      exact mul_le_mul_of_nonneg_left hMv (mul_nonneg (sq_nonneg _) hfactor)
    _ = ((k : ℝ) * (N - k : ℕ) / (N : ℝ)) *
        popMaxSqDev y * popVar y := by rw [hkn]; ring

/-- Given [population outcomes](hyp:y), [a positive feasible prefix length](hyp:k,hk,hkpos),
and [a population of at least two units](hyp:hN), [the centered revealed sum has the exact
sampling-without-replacement second moment](goal). -/
lemma integral_centered_revealedSum_sq {N : ℕ} [Nonempty (Fin N)] (y : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) (hkpos : 0 < k) (hN : 2 ≤ N) :
    ∫ π, (permutationRevealedSum (fun i => y i - popMean y) k hk π) ^ 2
        ∂(uniformPermutationDesign N).toMeasure =
      (k : ℝ) ^ 2 * (1 / (k : ℝ) - 1 / (N : ℝ)) * popVar y := by
  let D := uniformPermutationDesign N
  let μ := D.toMeasure
  let z : Fin N → ℝ := fun i => y i - popMean y
  let X := permutationSampleMean k hk z
  have hmeanDesign : D.E X = 0 := by
    rw [uniformPermutationDesign_E_permutationSampleMean k hk hkpos z]
    exact popMean_centered_eq_zero y
  have hmean : ∫ π, X π ∂μ = 0 := by
    rw [FiniteDesign.integral_toMeasure, hmeanDesign]
  have hsq : ∫ π, (X π) ^ 2 ∂μ =
      (1 / (k : ℝ) - 1 / (N : ℝ)) * popVar y := by
    rw [← variance_of_integral_eq_zero (measurable_of_finite X).aemeasurable hmean]
    rw [FiniteDesign.variance_toMeasure]
    rw [uniformPermutationDesign_Var_permutationSampleMean k hk hkpos hN z]
    rw [popVar_centered]
  change (∫ π, (permutationRevealedSum z k hk π) ^ 2 ∂μ) = _
  simp_rw [permutationRevealedSum_eq_mul_permutationSampleMean z k hk hkpos]
  rw [show (∫ π, ((k : ℝ) * X π) ^ 2 ∂μ) =
      (k : ℝ) ^ 2 * ∫ π, (X π) ^ 2 ∂μ by
    simp_rw [mul_pow]
    rw [integral_const_mul]]
  rw [hsq]
  ring

private lemma permutationNextVariance_eq_remainingSecondMoment {N : ℕ}
    (y : Fin N → ℝ) (k : ℕ) (hk : k < N)
    (π : PermutationSampleSpace N) :
    permutationNextVariance y k hk π =
      permutationRemainingSum (fun i => y i ^ 2) k hk.le π / ((N - k : ℕ) : ℝ) -
        (permutationRemainingSum y k hk.le π / ((N - k : ℕ) : ℝ)) ^ 2 := by
  rw [permutationNextVariance_eq_remainingVariance,
    permutationNextMean_eq_remainingMean]
  have hcount : ((N - k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
  have hsumY := sum_remainingPositions_eq_permutationRemainingSum y k hk.le π
  have hsumY2 := sum_remainingPositions_eq_permutationRemainingSum
    (fun i => y i ^ 2) k hk.le π
  rw [← hsumY, ← hsumY2]
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hcount]
  ring

private lemma permutationNextVariance_centered {N : ℕ} [Nonempty (Fin N)] (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) (π : PermutationSampleSpace N) :
    permutationNextVariance (fun i => y i - popMean y) k hk π =
      permutationNextVariance y k hk π := by
  rw [permutationNextVariance_eq_remainingVariance,
    permutationNextVariance_eq_remainingVariance]
  have hm : permutationNextMean (fun i => y i - popMean y) k hk π =
      permutationNextMean y k hk π - popMean y := by
    rw [permutationNextMean_eq_remainingMean, permutationNextMean_eq_remainingMean]
    rw [← sum_remainingPositions_eq_permutationRemainingSum,
      ← sum_remainingPositions_eq_permutationRemainingSum]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hcount : ((N - k : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
    field_simp [hcount]
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma sum_centered {N : ℕ} [Nonempty (Fin N)] (y : Fin N → ℝ) :
    ∑ i : Fin N, (y i - popMean y) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  unfold popMean
  simp only [Fintype.card_fin, nsmul_eq_mul]
  have hNpos : 0 < N := Fin.pos_iff_nonempty.mpr inferInstance
  field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hNpos.ne']
  ring

/-- Given [population outcomes](hyp:y), [a valid reveal time](hyp:k,hk), and [an
ordering](hyp:π), [the next-draw conditional variance equals the remaining centered-square
mean minus the squared remaining centered mean](goal). -/
lemma permutationNextVariance_eq_revealedSums {N : ℕ} [Nonempty (Fin N)] (y : Fin N → ℝ)
    (k : ℕ) (hk : k < N) (π : PermutationSampleSpace N) :
    permutationNextVariance y k hk π =
      ((∑ i : Fin N, (y i - popMean y) ^ 2) -
          permutationRevealedSum (fun i => (y i - popMean y) ^ 2) k hk.le π) /
          ((N - k : ℕ) : ℝ) -
        (permutationRevealedSum (fun i => y i - popMean y) k hk.le π /
          ((N - k : ℕ) : ℝ)) ^ 2 := by
  rw [← permutationNextVariance_centered y k hk π, permutationNextVariance_eq_remainingSecondMoment]
  unfold permutationRemainingSum
  have hsumSq : (∑ i : Fin N, (fun i => (y i - popMean y) ^ 2) (π i)) =
      ∑ i : Fin N, (y i - popMean y) ^ 2 := by
    simpa using Equiv.sum_comp π (fun i : Fin N => (y i - popMean y) ^ 2)
  have hsum : (∑ i : Fin N, (fun i => y i - popMean y) (π i)) =
      ∑ i : Fin N, (y i - popMean y) := by
    simpa using Equiv.sum_comp π (fun i : Fin N => y i - popMean y)
  rw [hsumSq, hsum, sum_centered]
  simp only [zero_sub, neg_div, neg_sq]


end Causalean.Experimentation.DesignBased
