module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalCoverage
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalGaussianCDF
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalIntervalLength
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariancePlugin
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathErrorCentering
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ErrorDecomposition
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FixedHorizonDeathVariation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FixedHorizonKMConsistency
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FixedHorizonLocalization
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FullHorizonRecurrenceVariation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FullHorizonDeathPlugin
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.InverseRiskCompensator
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.InverseRiskCompensatorIntegral
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LocalizedDeathVariation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LocalizedRecurrenceVariation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedDeathOracleReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedRecurrenceFullMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedRecurrenceOracleReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.OrdinaryRecurrenceOracleReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceExposureOrthogonality
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceOracleTransport
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceSubcriticalRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceVariationFirstMoment
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RemainingMeanCompensator
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RemainingMeanIdentification
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RemainingMeanRecurrenceEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalAsymptoticLinearity
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalCoefficientEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathOracleMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathPlugin
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathPluginConvergence
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalEmpiricalCompensator
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalEstimatorTightness
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalExtinction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceAssembly
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceCLT
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceTightness
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalNonfallback
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleCompensator
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleOrthogonality
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleTails
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOrdinaryConsistency
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalRemainingMeanGrid
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalSquaredCoefficient
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariance
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UnboundedRecurrenceTransport
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.Inference.OracleInfluenceWald
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Subcritical studentization

For a fixed law with endpoint exponent below one, the ordinary estimator
has an iid influence expansion and an observable variance estimate.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: thm:subcritical-studentized-law
theorem subcritical_studentized_law (c : ClassConstants)
    (hkappa : c.kappa < 1) (P : SubjectLaw)
    (hP : SubcriticalScope c P) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1 / 2) : -- @realizes alpha(miscoverage range)
    0 < subcriticalVariance c P ∧
    subcriticalVariance c P =
      ∫ o, (subcriticalInfluence c P true o -
        subcriticalInfluence c P false o) ^ 2 ∂observedLaw P ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (sampleLaw P n).real
        {s | ε < |Real.sqrt n * (ordinaryEstimator c s - causalTarget P) -
          (∑ i : Fin n, (subcriticalInfluence c P true (s i) -
            subcriticalInfluence c P false (s i))) / Real.sqrt n|})
        atTop (nhds 0)) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (sampleLaw P n).real
        {s | ε < |sigmaHatSq c s - subcriticalVariance c P|})
        atTop (nhds 0)) ∧
    Tendsto (fun n => (sampleLaw P n).real
      {s | ¬ nonFallbackSub c s}) atTop (nhds 0) ∧
    Tendsto (fun n =>
      sSup {d : ℝ | ∃ z : ℝ,
        d = |(sampleLaw P n).real
          {s | nonFallbackSub c s ∧
            Real.sqrt n * (ordinaryEstimator c s - causalTarget P) /
              Real.sqrt (sigmaHatSq c s) ≤ z} - normalCDF z|})
      atTop (nhds 0) ∧
    Tendsto (fun n => (sampleLaw P n).real
      {s | causalTarget P ∈ subcriticalInterval c alpha s})
      atTop (nhds (1 - alpha)) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (sampleLaw P n).real
        {s | ε < |Real.sqrt n * volume.real (subcriticalInterval c alpha s) -
          2 * normalQuantile alpha * Real.sqrt (subcriticalVariance c P)|})
        atTop (nhds 0)) := by
  refine ⟨subcriticalVariance_pos c P hP.modelClass hkappa,
    (subcriticalInfluence_contrast_moments c P hP.modelClass hkappa).2.2.2.symm, ?_⟩
  refine ⟨fun ε hε => subcritical_ordinaryEstimator_influence_probability_tendsto_zero
    c P hP.modelClass hkappa hε, ?_⟩
  refine ⟨fun ε hε => sigmaHatSq_probability_tendsto_subcriticalVariance
    c P hP.modelClass hkappa hε, ?_⟩
  refine ⟨nonFallbackSub_compl_probability_tendsto_of_variance_consistency
    c P hP.modelClass hkappa (fun ε hε =>
      sigmaHatSq_probability_tendsto_subcriticalVariance c P hP.modelClass hkappa hε), ?_⟩
  -- Roadmap (46) follows from standard-error consistency, shrinking radius,
  -- strict target interiority, and vanishing clipping/fallback probability.
  -- Coverage (45) uses the exact two-sided event and vanishing fallback mass.
  rw [← and_assoc]
  refine ⟨?_, fun ε hε => subcriticalInterval_scaled_length_probability_tendsto_zero
    c P hP.modelClass hkappa alpha halpha0 halpha1 hε⟩
  exact ⟨subcritical_studentized_cdf_uniform_tendsto c P hP.modelClass hkappa,
    subcriticalInterval_coverage_tendsto c P hP.modelClass hkappa alpha halpha0 halpha1⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
