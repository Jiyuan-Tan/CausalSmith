module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.ConditionedPredictiveTV
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.FactorialCalibration
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.TransferErrorCalibration

/-! Numerical TV bound for the conditioned relaxed iid experiment. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
open Causalean.Stat

private lemma ae_p_mu_bounds_of_supported
    {b ε : ℝ} (ν : Measure MarkedParam) [IsProbabilityMeasure ν]
    (hsupp : ν {t | 0 ≤ t.1 ∧ t.1 ≤ b ∧ ε ≤ t.2.1 ∧
      t.2.1 ≤ 1 - ε ∧ 0 ≤ t.2.2 ∧ t.2.2 ≤ 1} = 1) :
    (∀ᵐ t ∂ν, 0 ≤ t.1 ∧ t.1 ≤ b) ∧
      (∀ᵐ t ∂ν, 0 ≤ t.2.2 ∧ t.2.2 ≤ 1) := by
  let S : Set MarkedParam := {t | 0 ≤ t.1 ∧ t.1 ≤ b ∧ ε ≤ t.2.1 ∧
    t.2.1 ≤ 1 - ε ∧ 0 ≤ t.2.2 ∧ t.2.2 ≤ 1}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hae : ∀ᵐ t ∂ν, t ∈ S := by
    apply (ae_mem_iff_measure_eq hS.nullMeasurableSet).2
    simpa [S] using hsupp
  constructor <;> filter_upwards [hae] with t ht
  · exact ⟨ht.1, ht.2.1⟩
  · exact ⟨ht.2.2.2.2.1, ht.2.2.2.2.2⟩

end CausalSmith.Stat.MarRareqLogfrontier
