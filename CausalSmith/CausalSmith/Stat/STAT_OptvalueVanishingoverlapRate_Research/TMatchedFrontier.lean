module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TAllEstimatorLower
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TObservableUpper
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TIdentification

/-!
# Matched observed and causal frontiers
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

-- @node: thm:matched-frontier
/-- [Universal constants sandwich both the observed and causal minimax risks at the vanishing-overlap rate, while the explicit armwise estimator lies between the observed minimax risk and the same upper rate and its causal risk lies between the causal minimax risk and that upper rate](goal). -/
theorem matched_frontier :
    ∃ (cstar Cstar H₀ κ : ℝ) (D₀ : ℕ),
      ∃ hH₀ : 0 < H₀, ∃ hκ : 0 < κ, ∃ hD₀ : 2 ≤ D₀,
      0 < cstar ∧ cstar ≤ Cstar ∧
      ∀ (n d : ℕ) (ε : ℝ),
        1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
        cstar * rateScale n d ε ≤ minimaxRisk n d ε ∧
        minimaxRisk n d ε ≤ armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε ∧
        armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε ≤ Cstar * rateScale n d ε ∧
        cstar * rateScale n d ε ≤ causalMinimaxRisk n d ε ∧
        causalMinimaxRisk n d ε ≤ Cstar * rateScale n d ε ∧
        causalMinimaxRisk n d ε ≤
          causalArmwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε ∧
        causalArmwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε ≤
          Cstar * rateScale n d ε := by
  obtain ⟨cstar, Cstar, H₀, κ, D₀, hH₀, hκ, hD₀, hcstar, hcC, hfront⟩ :=
    weighted_separation_and_frontier.2.1
  refine ⟨cstar, Cstar, H₀, κ, D₀, hH₀, hκ, hD₀, hcstar, hcC, ?_⟩
  intro n d ε hn hd hε hεhalf
  obtain ⟨hlo, hmid, hhi, hclo, hchi⟩ := hfront n d ε hn hd hε hεhalf
  refine ⟨hlo, hmid, hhi, hclo, hchi, ?_, ?_⟩
  · rw [causalMinimaxRisk_eq_minimaxRisk hd hε hεhalf,
      causalArmwiseWorstRisk_eq_armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε hd hε hεhalf]
    exact hmid
  · rw [causalArmwiseWorstRisk_eq_armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε hd hε hεhalf]
    exact hhi

end CausalSmith.Stat.OptvalueVanishingoverlapRate
