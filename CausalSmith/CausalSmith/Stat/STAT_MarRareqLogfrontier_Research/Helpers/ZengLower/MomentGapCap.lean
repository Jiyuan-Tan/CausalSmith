module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.MomentCertificate

@[expose] public section

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:ε,c₁,c₂,c₄,c₄',n,d,K,M,hden,hc₄'), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def ZengMomentPriorPair.weaken_separation
    {ε c₁ c₂ c₄ c₄' : ℝ} {n d K : ℕ}
    (M : ZengMomentPriorPair ε c₁ c₂ c₄ n d K)
    (hden : 0 ≤ (n : ℝ) * Real.log n)
    (hc₄' : c₄' ≤ c₄) :
    ZengMomentPriorPair ε c₁ c₂ c₄' n d K := by
  refine { M with separated_pmu := ?_ }
  exact (div_le_div_of_nonneg_right hc₄' hden).trans M.separated_pmu

end CausalSmith.Stat.MarRareqLogfrontier
