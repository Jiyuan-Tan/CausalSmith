module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalBiasScale
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalCoverage
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalDeathRemainder
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalEmpiricalRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalExtinction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalFallbackLength
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalGaussianTransfer
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalIntervalLength
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalNonfallback
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalNumerator
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalOracleBand
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalOracleLimit
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalPoissonExponent
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalPoissonTaylor
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalPredictableComparison
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalProjection
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalProjectionProbability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRecurrenceApproximation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRecurrenceGaussian
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRecurrenceWitness
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRelativeVariance
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalSmallJumps
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalSurvivalEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalSurvivalIntegrated
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalSurvivalPrefix
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVarianceConsistency
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVariationLocalization
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalVariationMean
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalWitnessProbability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ErrorDecomposition
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceCanonicalCharFun
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrencePoissonCharFun
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SelectedRecurrenceCharFun
public import Causalean.Stat.CLT.GaussianCharFunBridge
public import Causalean.Stat.CLT.Martingale.Main
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Critical studentized Gaussian law

At endpoint exponent one the optional variation has logarithmic scale.
The conclusions use arbitrary triangular law sequences to express uniformity.
Mean optional variation is controlled by conditional recurrence compensation.
Early observed recurrences give positive optional variation. Their uniform
positive subject probability and iid no-witness calculation close (31)--(32),
including the probability rate for every sample size at least three.
CriticalExtinction closes roadmap (23) and proves that the extinction
correction is negligible at the critical scale along triangular laws.
CriticalVariationFluctuation proves the localized second-moment bound (28)
and triangular fluctuation limit (29). CriticalVariationLocalization removes
the risk localization using CriticalEmpiricalRisk and proves the full
observable two-arm optional-minus-predictable variation limit.
CriticalNumerator closes (11) and the unweighted terminal logarithmic
expansion in (13), with an integrable, uniformly bounded endpoint remainder.
CriticalOracleBand completes (13), including the bounded interior and
continuation-band contributions, with the exact logarithmic coefficient.
CriticalOracleLimit proves the deterministic normalized two-arm oracle limit
and its relative version in (15), uniformly along triangular model laws.
CriticalEmpiricalRisk closes (5)--(6) by countable nested-chain
symmetrization, with a uniform fourth moment, root-n tail bound, and
triangular control of failure of the time-dependent linear risk floor.
CriticalSmallJumps closes (18) on that event: the actual standardized subject
coefficients have a uniform deterministic envelope tending to zero.
CriticalSurvivalEnergy proves the logarithmic second-moment energy bound
underlying (8), with genuine KM/risk dependence and observed-law transport.
It gives second-mean and probability convergence of the left-limit KM at
the moving cutoff; control of the supremum in (9) remains separate.
CriticalSurvivalIntegrated integrates the prefix bounds against inverse retention
and proves normalized weighted second-mean and probability convergence along
triangular laws, supplying survival control under the oracle variance integral.
CriticalSurvivalFirstMean transfers integrated squared survival control to
absolute survival error in probability. CriticalPredictableIntegrated combines
it with relative empirical risk control to close the stochastic comparison (14).
CriticalVarianceConsistency assembles the two arms and the deterministic oracle
limit into (15), then uses the optional fluctuation bound (29) to close (30).
CriticalRelativeVariance proves the conditional energy relative limit and the
observable square-root denominator consistency needed for (19) and Slutsky.
CriticalGaussianTransfer completes studentization and the uniform CDF transfer
from the recurrence Gaussian limit.
CriticalPoissonTaylor proves the integrated complex Taylor remainder in (19)
vanishes in probability from the small jumps and relative predictable energy;
the conditional Poisson characteristic-function identity remains separate.
CriticalPoissonExponent identifies the compensated exponential intensity integral
with the relative quadratic energy plus remainder, and proves its exponential
converges in probability to the standard Gaussian characteristic function.
Its exponential has unconditional modulus at most one and is measurable and
integrable; bounded probability convergence now gives its expectation limit.
CriticalSurvivalPrefix extends the logarithmic energy bound to every prefix
of the shrinking horizon, and proves triangular second-mean, probability
and relative-ratio consistency for arbitrary deterministic prefix times.
CriticalRecurrenceCharFun identifies the observed standardized contrast
characteristic function with the critical exponential expectation through the
selected-arm mixture and finite assignment-cell integration.
CriticalRecurrenceGaussian applies the existing Lévy/CDF bridge to close the
recurrence Gaussian limit and hence all critical studentization conclusions.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: thm:critical-studentized-law
theorem critical_studentized_law (c : ClassConstants)
    (hkappa : c.kappa = 1) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1 / 2) : -- @realizes alpha(miscoverage range)
    (∀ Pseq : ℕ → SubjectLaw, (∀ n, CriticalScope c (Pseq n)) →
      Tendsto (fun n => (sampleLaw (Pseq n) n).real
        {s | ¬ nonFallback c s}) atTop (nhds 0) ∧
      Tendsto (fun n =>
        sSup {d : ℝ | ∃ z : ℝ,
          d = |(sampleLaw (Pseq n) n).real
            {s | nonFallback c s ∧
              (observableEstimator c s - causalTarget (Pseq n)) /
                Real.sqrt (criticalVarianceEstimator c s) ≤ z} - normalCDF z|})
        atTop (nhds 0) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => (sampleLaw (Pseq n) n).real
          {s | ε < |(n : ℝ) * criticalVarianceEstimator c s /
            Real.log n - criticalVariance c (Pseq n)|}) atTop (nhds 0)) ∧
      Tendsto (fun n => (sampleLaw (Pseq n) n).real
        {s | causalTarget (Pseq n) ∈ criticalInterval c alpha s})
        atTop (nhds (1 - alpha))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      ∀ P : SubjectLaw, CriticalScope c P →
        (∫ s, volume.real (criticalInterval c alpha s) ∂sampleLaw P n) ≤
          C * Real.sqrt (Real.log n / n)) := by
  have remaining :
    (∀ Pseq : ℕ → SubjectLaw, (∀ n, CriticalScope c (Pseq n)) →
      Tendsto (fun n =>
        sSup {d : ℝ | ∃ z : ℝ,
          d = |(sampleLaw (Pseq n) n).real
            {s | nonFallback c s ∧
              (observableEstimator c s - causalTarget (Pseq n)) /
                Real.sqrt (criticalVarianceEstimator c s) ≤ z} - normalCDF z|})
        atTop (nhds 0)) := by
    intro Pseq hP
    apply critical_studentized_cdf_uniform_tendsto_of_pointwise c Pseq
    apply critical_studentized_cdf_tendsto_of_recurrence c hkappa Pseq
      (fun n => (hP n).modelClass)
    exact critical_recurrence_cdf_triangular_tendsto c hkappa Pseq
      (fun n => (hP n).modelClass)
  refine ⟨?_, ?_⟩
  swap
  · obtain ⟨C, hC, hb⟩ := criticalInterval_expected_length_uniform_log_rate
      c hkappa alpha halpha0 halpha1
    exact ⟨C, hC, fun n hn P hP => hb n hn P hP.modelClass⟩
  intro Pseq hP
  have h := remaining Pseq hP
  have hv := fun ε hε => critical_variance_estimator_triangular_tendsto_zero
    c hkappa Pseq (fun n => (hP n).modelClass) (ε := ε) hε
  have hf := nonFallback_compl_triangular_tendsto_of_early_witness
    c Pseq (fun n => (hP n).modelClass)
  have hcov := criticalInterval_coverage_triangular_tendsto c Pseq
    (fun n => (hP n).modelClass) alpha halpha0 halpha1 hf
    (critical_studentized_cdf_tendsto_of_sup c Pseq h)
  exact ⟨hf, h, hv, hcov⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
