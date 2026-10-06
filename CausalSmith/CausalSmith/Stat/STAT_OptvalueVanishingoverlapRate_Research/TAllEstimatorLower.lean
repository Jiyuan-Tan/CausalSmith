module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TWeightedSeparationAndFrontier

/-!
# All-estimator lower risk
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

-- @node: thm:all-estimator-lower
/-- [A universal positive constant times the vanishing-overlap rate is a lower bound for the minimax squared error at every sample size, alphabet size, and admissible overlap level](goal). -/
theorem all_estimator_lower :
    ∃ cstar : ℝ, 0 < cstar ∧
      ∀ (n d : ℕ) (ε : ℝ),
        1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
        cstar * rateScale n d ε ≤ minimaxRisk n d ε := by
  obtain ⟨_, ⟨cstar, Cstar, H₀, κ, D₀, hH₀, hκ, hD₀,
    hcstar, _, hfrontier⟩, _⟩ := weighted_separation_and_frontier
  exact ⟨cstar, hcstar, fun n d ε hn hd hε hεhalf =>
    (hfrontier n d ε hn hd hε hεhalf).1⟩
  -- @realizes \(c_\star\)(universal lower risk constant)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
