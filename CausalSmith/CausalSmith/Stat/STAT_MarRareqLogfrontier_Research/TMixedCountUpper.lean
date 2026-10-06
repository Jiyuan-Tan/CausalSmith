module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUniformMixedCountCertificate
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PrefixTransfer

/-! TMixedCountUpper for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: thm:mixed-count-upper
/-- [the stated mathematical conclusion holds](goal). -/
theorem mixed_count_upper :
    ∃ C : ℝ, 0 < C ∧ -- @realizes \(\overline C\)(universal upper constant)
      ∀ (n d : ℕ) (q : ℝ) (P : FullLaw d),
        RareArrivalModelClass n d q P →
        deterministicRisk (mixedCountEstimator n d q) P ≤ riskEnvelope n d q ∧
        riskEnvelope n d q ≤ C * frontierRate n d q ∧
        deterministicRisk (mixedCountEstimator n d q) P ≤ auxiliaryMixedRisk n q P := by
  obtain ⟨C, hC, hcertificate⟩ := uniform_mixed_count_certificate
  refine ⟨C, hC, ?_⟩
  intro n d q P hP
  obtain ⟨hrisk, hrate⟩ := hcertificate n d q P hP
  exact ⟨hrisk, hrate, mixed_count_derandomization n d q P⟩

end CausalSmith.Stat.MarRareqLogfrontier
