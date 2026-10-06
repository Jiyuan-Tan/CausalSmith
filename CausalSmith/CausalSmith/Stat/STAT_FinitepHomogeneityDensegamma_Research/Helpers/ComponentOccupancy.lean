module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentOccupancyBridge
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OccupancySeries

/-! Finite-moment homogeneity testing: Helpers/ComponentOccupancy. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The first expected activity budget retains the two-mark rarity factor and fine-cell collision scale. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the a parameter](hyp:a), [the u parameter](hyp:u), [the ε parameter](hyp:ε). [This is the stated defined object](goal). -/
def activityBudgetA (n K : ℕ) (a u ε : ℝ) : ℝ := 2^38*a^4*u^4*ε^2*(n:ℝ)^2/K
/-- The second expected activity budget retains two-mark rarity and collisions between distinct components within one coarse pair. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the ε parameter](hyp:ε). [This is the stated defined object](goal). -/
def activityBudgetB (n K M : ℕ) (a u ε : ℝ) : ℝ := 2^56*a^4*u^4*ε^2*(n:ℝ)^4/((M:ℝ)*K^2)
/-- Component occupancy budgets: the displayed mathematical construction or bound.  [the parameters and conditions in the statement](hyp:n,K,M,a,u,L,h,hK), [the asserted mathematical result holds](goal). -/
-- @node: component_occupancy_budgets
lemma component_occupancy_budgets (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) (hK : 2^40*n ≤ K) :
    Measurable (activityA n K M a u) ∧ Measurable (activityB n K M a u) ∧
    Integrable (activityA n K M a u) (commonAugmentation n K M ε) ∧
    Integrable (activityB n K M a u) (commonAugmentation n K M ε) ∧
    (∫ aug, activityA n K M a u aug ∂commonAugmentation n K M ε) ≤ activityBudgetA n K a u ε ∧
    (∫ aug, activityB n K M a u aug ∂commonAugmentation n K M ε) ≤ activityBudgetB n K M a u ε := by
  have hM : 0 < M := lt_of_lt_of_le (by decide : 0 < 2) h.2.2.2.2.1
  have hpos : 0 < K := lt_of_lt_of_le (by omega : 0 < 16 * M) h.2.2.2.1
  let z : ℝ := 8 * Real.exp 1 * (n : ℝ) / K
  have hcount :
      (∫ aug, activityA n K M a u aug ∂commonAugmentation n K M ε) ≤
        2 ^ 14 * a ^ 4 * u ^ 4 * ε ^ 2 * K *
          (∑' j : ℕ, (j + 2 : ℝ) ^ 11 * z ^ (j + 2)) ∧
      (∫ aug, activityB n K M a u aug ∂commonAugmentation n K M ε) ≤
        2 ^ 17 * a ^ 4 * u ^ 4 * ε ^ 2 * (K : ℝ) ^ 2 / M *
          (∑' j : ℕ, (j + 2 : ℝ) ^ 6 * z ^ (j + 2)) ^ 2 := by
    exact component_occupancy_series_bounds n K M a u ε L h hK
  have hnumeric := occupancy_numeric_budget_bounds n K M hpos hM hK a u ε
  have hi := component_activities_integrable n K M a u ε L h
  exact ⟨measurable_activityA n K M a u, measurable_activityB n K M a u,
    hi.1, hi.2, hcount.1.trans hnumeric.1, hcount.2.trans hnumeric.2⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
