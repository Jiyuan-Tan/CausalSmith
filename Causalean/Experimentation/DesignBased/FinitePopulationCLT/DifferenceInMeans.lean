/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.Estimators.DifferenceInMeans
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.SRS

/-!
# Finite-population CLT for difference in means

This module reduces the complete-randomization difference in means to a simple-random-sample mean
of Li and Ding's transformed finite population, then applies Hájek's finite-population CLT.
-/

@[expose] public section

open scoped BigOperators Topology

namespace Causalean.Experimentation.DesignBased
open Causalean.Stat

open Filter
open FinitePopulationMoments
open ProbabilityTheory

/-- Given [a population size, a natural-number count, and treated and control potential
outcomes](hyp:N,K,Y1,Y0), the [transformed finite-population outcome](goal) assigns each unit the
formal weighted sum using weights given by the count and its truncated complement divided by the
population size. -/
noncomputable def diffInMeansTransformedOutcome
    (N K : ℕ) (Y1 Y0 : Fin N → ℝ) : Fin N → ℝ :=
  fun i => ((N - K : ℕ) : ℝ) / (N : ℝ) * Y1 i + (K : ℝ) / (N : ℝ) * Y0 i

private lemma diffInMeans_sub_sate_eq_scaled_sampleMean_sub_popMean
    {N K : ℕ} (hKpos : 0 < K) (hKlt : K < N)
    (Y1 Y0 : Fin N → ℝ) (S : {S : Finset (Fin N) // S.card = K}) :
    diffInMeans K Y1 Y0 S - sateEstimand Y1 Y0 =
      (N : ℝ) / ((N - K : ℕ) : ℝ) *
        (sampleMean K (diffInMeansTransformedOutcome N K Y1 Y0) S -
          popMean (diffInMeansTransformedOutcome N K Y1 Y0)) := by
  classical
  have hKN : K ≤ N := hKlt.le
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hKpos.trans hKlt))
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hKpos)
  have hL0 : ((N - K : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_of_lt hKlt)
  have hdiff0 : (N : ℝ) - (K : ℝ) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hKlt))
  have hsplit0 : (∑ i, Y0 i) =
      (∑ i, if i ∈ S.val then Y0 i else 0) +
        ∑ i, if i ∈ S.val then 0 else Y0 i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S.val <;> simp [hi]
  have hsumSel :
      (∑ i, if i ∈ S.val then diffInMeansTransformedOutcome N K Y1 Y0 i else 0) =
        ((N - K : ℕ) : ℝ) / (N : ℝ) *
            (∑ i, if i ∈ S.val then Y1 i else 0) +
          (K : ℝ) / (N : ℝ) * (∑ i, if i ∈ S.val then Y0 i else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold diffInMeansTransformedOutcome
    by_cases hi : i ∈ S.val <;> simp [hi]
  have hsumAll : (∑ i, diffInMeansTransformedOutcome N K Y1 Y0 i) =
      ((N - K : ℕ) : ℝ) / (N : ℝ) * (∑ i, Y1 i) +
        (K : ℝ) / (N : ℝ) * (∑ i, Y0 i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  unfold diffInMeans treatedMean controlMean sateEstimand sampleMean popMean
  simp only [Fintype.card_fin]
  rw [Nat.cast_sub hKN]
  rw [Finset.sum_sub_distrib, hsumSel, hsumAll, hsplit0]
  rw [Nat.cast_sub hKN]
  field_simp [hN0, hK0, hL0, hdiff0]
  ring

/-- Given [a positive proper treated count](hyp:K,hKpos,hKlt) and [fixed treated and control
potential outcomes](hyp:Y1,Y0), [the exact variance of difference in means equals the squared
treated-to-control scaling factor times the simple-random-sample variance of the transformed
outcome](goal). -/
lemma Var_diffInMeans_eq_scaled_srsSampleMeanVariance
    {N K : ℕ} (hKpos : 0 < K) (hKlt : K < N) (Y1 Y0 : Fin N → ℝ) :
    (completeRandomization (V := Fin N) K (by simpa using hKlt.le)).Var
        (diffInMeans K Y1 Y0) =
      ((N : ℝ) / ((N - K : ℕ) : ℝ)) ^ 2 *
        srsSampleMeanVariance N K (diffInMeansTransformedOutcome N K Y1 Y0) := by
  let D := completeRandomization (V := Fin N) K (by simpa using hKlt.le)
  let w := diffInMeansTransformedOutcome N K Y1 Y0
  let c := (N : ℝ) / ((N - K : ℕ) : ℝ)
  have hmeanDiff : D.E (diffInMeans K Y1 Y0) = sateEstimand Y1 Y0 := by
    exact E_diffInMeans_eq_sate K hKpos (by simpa using hKlt) Y1 Y0
  have hmeanSample : D.E (sampleMean K w) = popMean w := by
    exact E_sampleMean K (by simpa using hKlt.le) hKpos w
  calc
    D.Var (diffInMeans K Y1 Y0) =
        D.E (fun S => (diffInMeans K Y1 Y0 S - sateEstimand Y1 Y0) ^ 2) := by
      unfold FiniteDesign.Var
      rw [hmeanDiff]
    _ = D.E (fun S => c ^ 2 * (sampleMean K w S - popMean w) ^ 2) := by
      apply D.E_congr
      intro S
      rw [diffInMeans_sub_sate_eq_scaled_sampleMean_sub_popMean hKpos hKlt]
      dsimp only [c, w]
      ring
    _ = c ^ 2 * D.E (fun S => (sampleMean K w S - popMean w) ^ 2) := by
      rw [FiniteDesign.E_const_mul]
    _ = c ^ 2 * D.Var (sampleMean K w) := by
      unfold FiniteDesign.Var
      rw [hmeanSample]
    _ = c ^ 2 * srsSampleMeanVariance N K w := by
      rw [Var_sampleMean K (by simpa using hKlt.le) hKpos
        (by simpa using (show 2 ≤ N by omega))]
      simp only [Fintype.card_fin, srsSampleMeanVariance]

private lemma standardized_diffInMeans_eq_standardized_sampleMean
    {N K : ℕ} (hKpos : 0 < K) (hKlt : K < N)
    (Y1 Y0 : Fin N → ℝ)
    (hvar : 0 < popVar (diffInMeansTransformedOutcome N K Y1 Y0))
    (S : {S : Finset (Fin N) // S.card = K}) :
    (diffInMeans K Y1 Y0 S - sateEstimand Y1 Y0) /
        Real.sqrt ((completeRandomization (V := Fin N) K
          (by simpa using hKlt.le)).Var (diffInMeans K Y1 Y0)) =
      (sampleMean K (diffInMeansTransformedOutcome N K Y1 Y0) S -
          popMean (diffInMeansTransformedOutcome N K Y1 Y0)) /
        Real.sqrt (srsSampleMeanVariance N K
          (diffInMeansTransformedOutcome N K Y1 Y0)) := by
  let w := diffInMeansTransformedOutcome N K Y1 Y0
  let c := (N : ℝ) / ((N - K : ℕ) : ℝ)
  let v := srsSampleMeanVariance N K w
  have hNpos : 0 < N := hKpos.trans hKlt
  have hLpos : 0 < N - K := Nat.sub_pos_of_lt hKlt
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hfactor : (0 : ℝ) < 1 / (K : ℝ) - 1 / (N : ℝ) := by
    exact sub_pos.mpr (one_div_lt_one_div_of_lt (by exact_mod_cast hKpos)
      (by exact_mod_cast hKlt))
  have hv : 0 < v := by
    dsimp only [v, w, srsSampleMeanVariance]
    exact mul_pos hfactor hvar
  have hsqrt : Real.sqrt (c ^ 2 * v) = c * Real.sqrt v := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  rw [diffInMeans_sub_sate_eq_scaled_sampleMean_sub_popMean hKpos hKlt]
  rw [Var_diffInMeans_eq_scaled_srsSampleMeanVariance hKpos hKlt]
  change c * (sampleMean K w S - popMean w) / Real.sqrt (c ^ 2 * v) =
    (sampleMean K w S - popMean w) / Real.sqrt v
  rw [hsqrt]
  field_simp [hc.ne', (Real.sqrt_pos.2 hv).ne']

/-- Given [population-size and treated-count sequences](hyp:N,K), [positive treatment and control
arm sizes](hyp:hKpos,hKlt), and [fixed treated and control potential outcomes](hyp:Y1,Y0), if
[Li and Ding's transformed population has positive variance](hyp:hvar) and [satisfies their
maximal-deviation condition](hyp:hmax), then [the difference in means, centered at the finite-
population average effect and divided by its exact randomization standard deviation, converges
in distribution to the standard normal law](goal). -/
theorem diffInMeans_clt
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (Y1 Y0 : ∀ n, Fin (N n) → ℝ)
    (hvar : ∀ n, 0 < popVar
      (diffInMeansTransformedOutcome (N n) (K n) (Y1 n) (Y0 n)))
    (hmax : Tendsto (fun n =>
      popMaxSqDev (diffInMeansTransformedOutcome (N n) (K n) (Y1 n) (Y0 n)) /
        (((min (K n) (N n - K n) : ℕ) : ℝ) *
          popVar (diffInMeansTransformedOutcome (N n) (K n) (Y1 n) (Y0 n))))
      atTop (nhds 0)) :
    TendstoInDistribution
      (fun n => (completeRandomization (V := Fin (N n)) (K n)
        (by simpa using (hKlt n).le)).toMeasure)
      (fun n S =>
        (diffInMeans (K n) (Y1 n) (Y0 n) S - sateEstimand (Y1 n) (Y0 n)) /
          Real.sqrt ((completeRandomization (V := Fin (N n)) (K n)
            (by simpa using (hKlt n).le)).Var (diffInMeans (K n) (Y1 n) (Y0 n))))
      (gaussianReal 0 1) (fun _n => (measurable_of_finite _).aemeasurable) := by
  let w := fun n => diffInMeansTransformedOutcome (N n) (K n) (Y1 n) (Y0 n)
  have hclt := completeRandomization_sampleMean_clt N K hKpos hKlt w hvar hmax
  have hstat : ∀ n,
      (fun S =>
        (diffInMeans (K n) (Y1 n) (Y0 n) S - sateEstimand (Y1 n) (Y0 n)) /
          Real.sqrt ((completeRandomization (V := Fin (N n)) (K n)
            (by simpa using (hKlt n).le)).Var (diffInMeans (K n) (Y1 n) (Y0 n)))) =
      (fun S => (sampleMean (K n) (w n) S - popMean (w n)) /
        Real.sqrt (srsSampleMeanVariance (N n) (K n) (w n))) := by
    intro n
    funext S
    exact standardized_diffInMeans_eq_standardized_sampleMean
      (hKpos n) (hKlt n) (Y1 n) (Y0 n) (hvar n) S
  refine ⟨fun _ => (measurable_of_finite _).aemeasurable,
    hclt.aemeasurable_limit, ?_⟩
  simpa only [hstat] using hclt.tendsto

end Causalean.Experimentation.DesignBased
