module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedUniformMixedCountCertificate
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PrefixTransfer

/-! TUnrestrictedMixedCountUpper for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: thm:unrestricted-mixed-count-upper
/-- [the stated mathematical conclusion holds](goal). -/
theorem unrestricted_mixed_count_upper :
    ∃ C : ℝ, 0 < C ∧ -- @realizes \(\overline C\)(universal upper constant)
      ∀ (n d : ℕ) (q : ℝ) (P : FullLaw d),
        UnrestrictedArrivalModelClass n d q P →
        IIDSampling n (sampleLaw n P)
          (fun (i : Fin n) (s : Fin n → ObsRecord d) => s i) P →
        deterministicRisk (mixedCountEstimator n d q) P ≤ riskEnvelope n d q ∧
        riskEnvelope n d q ≤ C * frontierRate n d q ∧
        deterministicRisk (mixedCountEstimator n d q) P ≤ auxiliaryMixedRisk n q P := by
  obtain ⟨C, hC, hcertificate⟩ := unrestricted_uniform_mixed_count_certificate
  refine ⟨C, hC, ?_⟩
  intro n d q P hP hiid
  obtain ⟨hrisk, hrate⟩ := hcertificate n d q P hP hiid
  have hident := unrestricted_cell_identification P hP
  rw [← hident] at hrisk
  exact ⟨hrisk, hrate, mixed_count_derandomization n d q P⟩

end CausalSmith.Stat.MarRareqLogfrontier
