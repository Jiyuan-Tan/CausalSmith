module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.CompleteArrivalRisk
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.FallbackBias
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.ChebyshevCoefficients
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.ChebyshevRiskBounds
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.LightSecondMoment
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.LightExponentialBounds
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.PilotTails
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamBiasRates
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamBiasAlgebra
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamLargeBias
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamHeavyBias
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamHeavyVariance
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamLightSecondMoment
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamCorrections
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamPilot
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamVariance
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamCorrectionVariance
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamLargeVariance
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamProduct
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamVarianceAlgebra
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamVarianceRates
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamRiskVariance
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamLinear
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamAggregateVariance
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamRiskAssembly
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamRawMean
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamTransfer
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial
public import Causalean.Stat.Concentration.Poisson.FactorialPath

/-!
# Uniform risk of the missing-membership estimator

The constant is outside all sample-size, alphabet-size and arrival-floor quantifiers.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: lem:upper-risk
/-- A universal constant controls the estimator's risk on the complete MAR class. [the stated mathematical conclusion holds](goal). -/
lemma upper_risk : ∃ CU : ℝ, UpperRiskCertificate CU := by
  let Cnon : ℝ := 8 * ((201719808 : ℝ) ^ 2 *
    ((720 * (4 / 3 : ℝ) ^ 6) * (Real.exp 1 + 1)) + 119) +
    2 * (268435456 : ℝ) ^ 2 + 104
  let Cfall : ℝ := 4 * Real.exp 128
  have hnC : 0 < Cnon := by dsimp [Cnon]; positivity
  have hfC : 0 < Cfall := by dsimp [Cfall]; positivity
  refine ⟨Cnon + Cfall, add_pos hnC hfC, ?_⟩
  intro n d q hn hd hq P μ hiid
  have hn' : 0 < n := Nat.zero_lt_of_lt hn
  have hr : 0 ≤ rate n d q := by unfold rate; positivity
  rw [hiid]
  by_cases hqone : q = 1
  · have hf := upper_fallback_branches_risk_rate hn' P.val P.property hq
      (Or.inl hqone)
    exact hf.trans (mul_le_mul_of_nonneg_right (by dsimp [Cfall]; linarith) hr)
  · by_cases hreg : ell n < 128 ∨ (d : ℝ) ≥ (n : ℝ) * ell n
    · have hf := upper_fallback_branches_risk_rate hn' P.val P.property hq
        (Or.inr hreg)
      exact hf.trans (mul_le_mul_of_nonneg_right (by dsimp [Cfall]; linarith) hr)
    · have hnon := upper_nonfallback_risk_rate hn' P.val P.property hq hqone hreg
      exact hnon.trans (mul_le_mul_of_nonneg_right (by dsimp [Cnon]; linarith) hr)

end CausalSmith.Stat.MarNearcompleteFrontier
