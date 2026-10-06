module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedUniformMixedCountCertificate
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Identification

/-! TUniformMixedCountCertificate for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: thm:uniform-mixed-count-certificate
/-- [the stated mathematical conclusion holds](goal). -/
theorem uniform_mixed_count_certificate :
    ∃ C : ℝ, 0 < C ∧ -- @realizes \(\overline C\)(universal upper constant)
      ∀ (n d : ℕ) (q : ℝ) (P : FullLaw d),
        RareArrivalModelClass n d q P →
        deterministicRisk (mixedCountEstimator n d q) P ≤ riskEnvelope n d q ∧
        riskEnvelope n d q ≤ C * frontierRate n d q := by
  obtain ⟨C, hC, hcertificate⟩ := unrestricted_uniform_mixed_count_certificate
  refine ⟨C, hC, ?_⟩
  intro n d q P hP
  have hPplus : UnrestrictedArrivalModelClass n d q P :=
    { n_pos := hP.n_pos
      d_pos := hP.d_pos
      q_pos := hP.q_pos
      q_le_one := hP.q_le_one
      randomized := hP.randomized
      balanced := hP.balanced
      surrogate := hP.surrogate
      outcome := hP.outcome
      mar := hP.mar
      arrival := hP.arrival }
  obtain ⟨hrisk, hrate⟩ := hcertificate n d q P hPplus hP.iid
  have hident := unrestricted_cell_identification P hPplus
  rw [← hident] at hrisk
  exact ⟨hrisk, hrate⟩

end CausalSmith.Stat.MarRareqLogfrontier
