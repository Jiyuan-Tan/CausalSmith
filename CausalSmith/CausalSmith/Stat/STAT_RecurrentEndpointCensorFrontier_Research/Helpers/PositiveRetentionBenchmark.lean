module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ErrorDecomposition
public import Causalean.Stat.CLT.Lindeberg

/-!
# Zero-bandwidth form of the positive-retention estimator

This file records the exact deterministic specialization of the continued
estimator at bandwidth zero.  Quantitative risk and limit-law claims require
additional probabilistic estimates that are not part of the current API.
-/

public section

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- At zero bandwidth, the continued arm estimator before projection is exactly
the ordinary unweighted estimator. -/
lemma benchmark_ordinaryMuTilde_eq_muTildeAt_zero (c : ClassConstants)
    {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) :
    ordinaryMuTilde a s = muTildeAt c 0 a s := by
  simp [ordinaryMuTilde, muTildeAt, continuationWeight]

/-- At zero bandwidth, projection preserves the exact identification between
the continued and ordinary arm estimators. -/
lemma benchmark_ordinaryMuHat_eq_muHatAt_zero (c : ClassConstants)
    {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) :
    ordinaryMuHat c a s = muHatAt c 0 a s := by
  rw [ordinaryMuHat, muHatAt, benchmark_ordinaryMuTilde_eq_muTildeAt_zero]

/-- The ordinary treatment contrast is the contrast of the two zero-bandwidth
continued arm estimators. -/
lemma benchmark_ordinaryEstimator_eq_muHatAt_zero_contrast (c : ClassConstants)
    {n : ℕ} (s : Fin n → ObsHistory) :
    ordinaryEstimator c s = muHatAt c 0 true s - muHatAt c 0 false s := by
  rw [ordinaryEstimator, benchmark_ordinaryMuHat_eq_muHatAt_zero,
    benchmark_ordinaryMuHat_eq_muHatAt_zero]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
