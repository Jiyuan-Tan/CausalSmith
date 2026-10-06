module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.FixedPoissonBridge
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.ManyCellLowerProof
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.Parametric
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The cited fixed-positivity lower bound and its paper-local proof. -/

@[expose] public section

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: lem:zeng-theorem-two-lower
def ZengTheoremTwoLower : Sort 0 :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∃ (cε c₀ : ℝ) (n₀ : ℕ), 0 < cε ∧ 0 < c₀ ∧
      ∀ (n d : ℕ), n₀ ≤ n → 1 ≤ d →
        (d : ℝ) ≤ c₀ * n * Real.log n →
          cε * ((n : ℝ)⁻¹ +
            ((d : ℝ) / ((n : ℝ) * Real.log n)) ^ 2) ≤
              zengZeroControlRisk n d ε

end CausalSmith.Stat.MarRareqLogfrontier
