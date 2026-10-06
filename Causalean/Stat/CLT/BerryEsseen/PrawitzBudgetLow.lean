module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetLowCompact
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetLowSmall

/-! # PrawitzBudgetLow

One independent sufficient estimate in the deterministic Prawitz budget.
The full budget retains its original cutoffs and constant; the three
integral allocations add to one and introduce no probability hypotheses.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a moment ratio ρ strictly between zero and one](hyp:ρ,hρ,hρ1), with
cutoffs U0 = max(3/2, √(4 log(1/ρ))) and U = 12/(5ρ),
[the low-frequency Fourier discrepancy contribution (2/U)·∫ over [0, U0] of
the Prawitz filter magnitude times the discrepancy envelope is at most one
quarter of ρ](goal). -/
theorem prawitz_budget_low
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    (2 / U) * (∫ t in (0 : ℝ)..U0,
      ‖prawitzKernel (t / U)‖ * prawitzDiscrepancyEnvelope ρ t) ≤ ρ / 4 := by
  by_cases hsmall : ρ ≤ 1 / 100
  · exact prawitz_budget_low_small ρ hρ hsmall
  · exact prawitz_budget_low_compact ρ (lt_of_not_ge hsmall) hρ1

end Causalean.Stat.CLT.BerryEsseen
