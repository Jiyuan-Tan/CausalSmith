module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetCutoffs
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetGaussian
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetHigh
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetLow

/-! # A numerical budget for the sharper Berry–Esseen route

The unchanged explicit smoothing envelope is bounded by four focused
sufficient estimates. The three integral allocations are 1/4, 3/20, and
3/5 of the ratio, summing to one. Each estimate is proved in its own imported
module; this module only combines them.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a third-moment ratio ρ strictly between zero and one](hyp:hρ,hρ1), with
inner cutoff U0 = max(3/2, √(4 log(1/ρ))) and outer cutoff U = 12/(5ρ),
[the inner cutoff is at most the outer cutoff and the full deterministic
Prawitz smoothing envelope at these cutoffs is at most ρ](goal). -/
theorem prawitz_berry_esseen_budget
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    U0 ≤ U ∧ prawitzBerryEsseenEnvelope ρ U0 U ≤ ρ := by
  refine ⟨(prawitz_budget_cutoffs ρ hρ hρ1).2, ?_⟩
  have hlo := prawitz_budget_low ρ hρ hρ1
  have hhi := prawitz_budget_high ρ hρ hρ1
  have hg := prawitz_budget_gaussian ρ hρ hρ1
  dsimp only at hlo hhi hg ⊢
  unfold prawitzBerryEsseenEnvelope
  linarith

end Causalean.Stat.CLT.BerryEsseen
