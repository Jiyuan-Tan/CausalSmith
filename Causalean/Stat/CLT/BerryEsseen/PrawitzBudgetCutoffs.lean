module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzEnvelopes
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernelBounds

/-! # PrawitzBudgetCutoffs

One independent sufficient estimate in the deterministic Prawitz budget.
The full budget retains its original cutoffs and constant; the three
integral allocations add to one and introduce no probability hypotheses.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a moment ratio ρ strictly between zero and one](hyp:ρ,hρ,hρ1),
[the inner cutoff U0 = max(3/2, √(4 log(1/ρ))) is positive and no larger
than the outer cutoff U = 12/(5ρ)](goal). -/
theorem prawitz_budget_cutoffs
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    0 < U0 ∧ U0 ≤ U := by
  /- Use log(1/ρ)≤1/ρ-1, square the positive outer cutoff, and
  apply sqrt_le_iff. This is elementary cutoff geometry, independent of all
  envelope integrals. The hypothesis ρ<1 gives positivity of log(1/ρ). -/
  dsimp only
  have hU : 0 < 12 / (5 * ρ) := by positivity
  refine ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2) (le_max_left _ _),
    max_le ?_ ?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < 5 * ρ)).2
    nlinarith
  · apply (Real.sqrt_le_left hU.le).2
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / ρ)
    have hinv : 0 ≤ 1 / ρ := by positivity
    have hinv1 : 1 ≤ 1 / ρ := (le_div_iff₀ hρ).2 (by linarith)
    have hsquare : (12 / (5 * ρ)) ^ 2 = (144 / 25 : ℝ) * (1 / ρ) ^ 2 := by
      field_simp
      ring
    rw [hsquare]
    nlinarith [sq_nonneg (1 / ρ - 1)]

end Causalean.Stat.CLT.BerryEsseen
