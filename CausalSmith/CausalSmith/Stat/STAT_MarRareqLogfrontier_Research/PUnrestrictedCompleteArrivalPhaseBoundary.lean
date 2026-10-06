module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.PUnrestrictedNearCompletePhaseBoundary

/-! PUnrestrictedCompleteArrivalPhaseBoundary for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: prop:unrestricted-complete-arrival-phase-boundary
/-- [the stated mathematical conclusion holds](goal). -/
theorem unrestricted_complete_arrival_phase_boundary :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ d : ℕ → ℕ, (∀ n, 1 ≤ d n) →
        ∀ᶠ n : ℕ in atTop,
          c / (n : ℝ) ≤ unrestrictedMinimaxRisk n (d n) 1 ∧
          unrestrictedMinimaxRisk n (d n) 1 ≤ C / (n : ℝ) := by
  refine ⟨1 / 256, 4, by norm_num, by norm_num, ?_⟩
  intro d hd
  have hdeficit : ∀ᶠ n : ℕ in atTop,
      1 - (1 : ℝ) ≤ (0 : ℝ) / Real.sqrt (n : ℝ) := by simp
  have hb := unrestricted_near_complete_phase_boundary 0 (by norm_num) d hd
    (fun _ => 1) (by intro n; norm_num) hdeficit
  filter_upwards [hb] with n hn
  simpa [div_eq_mul_inv, mul_comm, mul_assoc] using hn

end CausalSmith.Stat.MarRareqLogfrontier
