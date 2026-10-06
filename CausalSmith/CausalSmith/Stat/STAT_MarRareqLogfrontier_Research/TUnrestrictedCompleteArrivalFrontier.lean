module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedNearCompleteArrivalEnvelope

/-! The complete-arrival endpoint of the all-kernel near-complete envelope. -/

public section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: thm:unrestricted-complete-arrival-frontier
/-- Uniformly over sample size and alphabet size, [the unrestricted complete-arrival frontier has parametric order](goal). -/
theorem unrestricted_complete_arrival_frontier :
    ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d →
      1 / (256 * (n : ℝ)) ≤ unrestrictedMinimaxRisk n d 1 ∧
      unrestrictedMinimaxRisk n d 1 ≤
        Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P}) =>
            deterministicRisk (completeArrivalHTEstimator n d) P.1) () ∧
      Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P}) =>
            deterministicRisk (completeArrivalHTEstimator n d) P.1) () ≤
        4 / (n : ℝ) := by
  intro n d hn hd
  obtain ⟨C, hC, hmixed, hnear⟩ := unrestricted_near_complete_arrival_envelope
  obtain ⟨hlo, _, hhi⟩ := hnear n d 1 hn hd (by norm_num) (by norm_num)
  exact ⟨hlo, (complete_arrival_frontier_direct n d hn hd).2.1, by simpa using hhi⟩

end CausalSmith.Stat.MarRareqLogfrontier
