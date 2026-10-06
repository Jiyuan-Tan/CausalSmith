module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionAsymptoticLinearity
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionGaussianTransfer
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionTargetIdentification
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ErrorDecomposition
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionExtinction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRecurrence
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionProjection
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionInfluenceMeasurability
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionOracleMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathOracleMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionInfluenceAssembly
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionLocalization
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionKMEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionKMConsistency
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionKMTimeConsistency
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionCenteredEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionOracleCoefficient
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionOracleMeanEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRecurrenceReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathReplacement
public import Causalean.Stat.CLT.Lindeberg

/-!
# Positive-retention benchmark

The ordinary risk-set estimator has parametric risk and a fixed-law Gaussian
limit under horizon retention. The cited scope claims are comparison material.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: ordinaryMuTilde_eq_muTildeAt_zero
lemma ordinaryMuTilde_eq_muTildeAt_zero (c : ClassConstants)
    {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) :
    ordinaryMuTilde a s = muTildeAt c 0 a s := by
  simp [ordinaryMuTilde, muTildeAt, continuationWeight]

-- @node: prop:positive-retention-reduction
theorem positive_retention_reduction (c : ClassConstants) (P : SubjectLaw)
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P)
    (hHorizon : PositiveHorizonRetention c P) :
    (∀ a : Arm, c.pMin * c.Ghor ≤ P.p a * retention P a 1) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, continuationWeight (holderOrder c) 0 t = 1) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → ∀ a : Arm,
      Causalean.Stat.sqRisk (sampleLaw P n) (ordinaryMuHat c a)
        (armMean P a) ≤ C / n) ∧
    (∃ σ2 : ℝ, 0 < σ2 ∧
      ConvergesInLaw (fun n : ℕ => (sampleLaw P n).map
        (fun s => Real.sqrt n * (ordinaryEstimator c s - causalTarget P)))
        (gaussianReal 0 (Real.toNNReal σ2))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    exact mul_le_mul (hOverlap a) (hHorizon a (1 : ℝ) (by norm_num))
      c.Ghor_pos.le (le_trans c.pMin_pos.le (hOverlap a))
  · intro t ht
    simp [continuationWeight]
  -- Roadmap (6)--(14): measurable-representative death isometry, the
  -- recurrence and death C/n bounds, exponential extinction, and projection.
  · exact positiveRetention_ordinaryMuHat_sqRisk_le c P hIid hRandom hAssignment
      hOverlap hPoisson hDeath hRecurDeath hCensor hRecurBounds hDeathBounds hHorizon
  -- Roadmap (25)--(30): PositiveRetentionInfluenceAssembly proves the actual
  -- influence contrast's exact moments and its nondegenerate iid Gaussian limit.
  -- PositiveRetentionLocalization supplies full-horizon denominator control (18).
  -- PositiveRetentionKMEnergy proves the full-horizon KM oracle isometry and
  -- its C/n second moment under the benchmark death assumptions alone.
  -- PositiveRetentionKMTransport transfers the full-horizon second moment to
  -- observed histories and proves that the observed KM action vanishes in probability.
  -- PositiveRetentionKMConsistency identifies the observable KM endpoint error
  -- and proves full-horizon endpoint consistency in second mean and probability.
  -- PositiveRetentionKMTimeConsistency proves second-mean consistency at all study times,
  -- integrated observable KM consistency, and localized inverse-risk weighted KM energy.
  -- PositiveRetentionCenteredEnergy proves the full-horizon centered denominator energy,
  -- including its integrated C/n bound and convergence in mean and probability.
  -- PositiveRetentionOracleCoefficient combines the dependent KM and denominator
  -- errors and proves vanishing full-horizon recurrence/death hazard energy.
  -- PositiveRetentionOracleMeanEnergy strengthens both full-horizon hazard energies
  -- to convergence in mean using reciprocal-binomial second moments and Young.
  -- PositiveRetentionRecurrenceReplacement closes the actual observable recurrence
  -- oracle replacement (26) by conditional Poisson energy and its mean limit.
  -- PositiveRetentionDeathDifferenceMoments proves the normalized predictable
  -- death difference isometry and vanishing full-horizon second moment.
  -- PositiveRetentionDeathReplacement transports those moments to observed
  -- histories and closes the actual death martingale oracle replacement (27).
  -- PositiveRetentionAsymptoticLinearity assembles both arm expansions with
  -- extinction and removes projection. The benchmark Campbell identity
  -- identifies the clinical target, and the weak-limit transfer proves (31).
  · refine ⟨subcriticalVariance c P, positiveRetention_variance_pos c P hOverlap
      hPoisson hDeath hRecurBounds hDeathBounds hHorizon, ?_⟩
    rw [positiveRetention_causalTarget_eq_armMean_contrast P hPoisson hDeath hRecurDeath]
    exact positiveRetention_ordinaryEstimator_armMean_gaussian c P hIid hRandom
      hAssignment hOverlap hPoisson hDeath hRecurDeath hCensor hRecurBounds
      hDeathBounds hHorizon

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
