module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetHighCompact
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetHighSmall

/-! # PrawitzBudgetHigh

One independent sufficient estimate in the deterministic Prawitz budget.
The full budget retains its original cutoffs and constant; the three
integral allocations add to one and introduce no probability hypotheses.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a moment ratio ρ strictly between zero and one](hyp:ρ,hρ,hρ1), with
cutoffs U0 = max(3/2, √(4 log(1/ρ))) and U = 12/(5ρ),
[the high-frequency contribution (2/U)·∫ over [U0, U] of the Prawitz filter
magnitude times the characteristic-function moment envelope is at most three
twentieths of ρ](goal). -/
theorem prawitz_budget_high
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    (2 / U) * (∫ t in U0..U,
      ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t) ≤ 3 * ρ / 20 := by
  by_cases hsmall : ρ ≤ 1 / 100
  · exact prawitz_budget_high_small ρ hρ hsmall
  · exact prawitz_budget_high_compact ρ (lt_of_not_ge hsmall) hρ1

end Causalean.Stat.CLT.BerryEsseen
