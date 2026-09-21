/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PredictableVarianceConcentration

/-!
# Finite-population CLT under the Li–Ding maximal-deviation condition

This module combines predictable-variance concentration and conditional Lindeberg control to
obtain the standardized central limit theorem for a simple random sample represented by the
prefix of a uniform permutation, then transports it to complete randomization.  The formalized
maximal-deviation condition is the convenient sufficient condition used by Li and Ding (2017),
not Hájek's weaker necessary-and-sufficient Lindeberg criterion.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators Topology

namespace Causalean.Experimentation.DesignBased
open Causalean.Stat

open Filter
open FinitePopulationMoments
open ProbabilityTheory

/-- Given [population-size and sample-size sequences](hyp:N,K), [positive proper sample
sizes](hyp:hKpos,hKlt), and [population outcomes](hyp:y) with [positive variances](hyp:hvar),
if [the Li–Ding maximal-deviation sufficient-condition ratio tends to zero](hyp:hmax), then [the centered ordered
simple-random-sample mean, standardized by its exact design variance, converges in distribution
to the standard normal law](goal). -/
theorem srs_finitePopulation_clt
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (hvar : ∀ n, 0 < popVar (y n))
    (hmax : Tendsto (fun n => popMaxSqDev (y n) /
      (((min (K n) (N n - K n) : ℕ) : ℝ) * popVar (y n))) atTop (nhds 0)) :
    TendstoInDistribution (fun n => (uniformPermutationDesign (N n)).toMeasure)
      (fun n π => (permutationSampleMean (K n) (hKlt n).le (y n) π - popMean (y n)) /
        Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)))
      (gaussianReal 0 1) (fun _n => (measurable_of_finite _).aemeasurable) := by
  let A := standardizedSrsPermutationHajekArray N K hKpos hKlt y
  have hclt := martingaleArrayCLT A
    (standardizedSrsPermutationHajekArray_predictableQuadraticVariation_tendstoInProbability
      N K hKpos hKlt y hvar hmax)
    (standardizedSrsPermutationHajekArray_conditionalLindeberg
      N K hKpos hKlt y hvar hmax)
  have hrow : A.rowSum = fun n π =>
      (permutationSampleMean (K n) (hKlt n).le (y n) π - popMean (y n)) /
        Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)) := by
    funext n
    exact standardizedSrsPermutationHajekArray_rowSum N K hKpos hKlt y n
  simpa only [hrow] using hclt

/-- Given [population-size and sample-size sequences](hyp:N,K), [positive proper sample
sizes](hyp:hKpos,hKlt), and [population outcomes](hyp:y) with [positive variances](hyp:hvar),
if [the Li–Ding maximal-deviation sufficient-condition ratio tends to zero](hyp:hmax), then [the centered sample mean
under complete randomization, standardized by its exact design variance, converges in
distribution to the standard normal law](goal). -/
theorem completeRandomization_sampleMean_clt
    (N K : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (hvar : ∀ n, 0 < popVar (y n))
    (hmax : Tendsto (fun n => popMaxSqDev (y n) /
      (((min (K n) (N n - K n) : ℕ) : ℝ) * popVar (y n))) atTop (nhds 0)) :
    TendstoInDistribution
      (fun n => (completeRandomization (V := Fin (N n)) (K n)
        (by simpa using (hKlt n).le)).toMeasure)
      (fun n S => (sampleMean (K n) (y n) S - popMean (y n)) /
        Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)))
      (gaussianReal 0 1) (fun _n => (measurable_of_finite _).aemeasurable) := by
  have hclt := srs_finitePopulation_clt N K hKpos hKlt y hvar hmax
  have hrow : ∀ n,
      Measure.map
          (fun S => (sampleMean (K n) (y n) S - popMean (y n)) /
            Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)))
          (completeRandomization (V := Fin (N n)) (K n)
            (by simpa using (hKlt n).le)).toMeasure =
        Measure.map
          (fun π => (permutationSampleMean (K n) (hKlt n).le (y n) π - popMean (y n)) /
            Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)))
          (uniformPermutationDesign (N n)).toMeasure := by
    intro n
    let pfx := permutationPrefixSet (K n) (hKlt n).le
    have hdesign := uniformPermutationDesign_map_prefixSet_eq_completeRandomization
      (K n) (hKlt n).le
    have hmeasure := FiniteDesign.toMeasure_map (uniformPermutationDesign (N n)) pfx
    rw [hdesign] at hmeasure
    rw [hmeasure, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    apply Measure.map_congr
    filter_upwards with π
    change (sampleMean (K n) (y n) (pfx π) - popMean (y n)) /
        Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)) = _
    rw [sampleMean_permutationPrefixSet_eq]
  refine ⟨fun _ => (measurable_of_finite _).aemeasurable,
    hclt.aemeasurable_limit, ?_⟩
  simpa only [hrow] using hclt.tendsto

end Causalean.Experimentation.DesignBased
