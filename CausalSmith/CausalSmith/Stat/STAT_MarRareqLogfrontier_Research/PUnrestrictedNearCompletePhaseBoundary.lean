module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedNearCompleteArrivalEnvelope
public import Mathlib.Order.Filter.AtTopBot.Basic

/-! A sufficient near-complete window for parametric point risk uniformly in dimension. -/

public section
open Filter
namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: prop:unrestricted-near-complete-phase-boundary
/-- Given [the specified inputs and assumptions](hyp:M,hM,d,hd,q,hq,hdeficit), [the stated mathematical conclusion holds](goal). -/
theorem unrestricted_near_complete_phase_boundary
    (M : ℝ) (hM : 0 ≤ M) (d : ℕ → ℕ) (hd : ∀ n, 1 ≤ d n)
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n ∧ q n ≤ 1)
    (hdeficit : ∀ᶠ n : ℕ in atTop, 1 - q n ≤ M / Real.sqrt (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      1 / (256 * (n : ℝ)) ≤ unrestrictedMinimaxRisk n (d n) (q n) ∧
      unrestrictedMinimaxRisk n (d n) (q n) ≤ (4 + M ^ 2) / (n : ℝ) := by
  obtain ⟨C, hC, hmix, henvelope⟩ := unrestricted_near_complete_arrival_envelope
  filter_upwards [hdeficit, eventually_ge_atTop (1 : ℕ)] with n hdef hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hlower, hupper, hHT⟩ := henvelope n (d n) (q n) hn (hd n)
    (hq n).1 (hq n).2
  refine ⟨hlower, ?_⟩
  have hupper' : unrestrictedMinimaxRisk n (d n) (q n) ≤
      4 / (n : ℝ) + (1 - q n) ^ 2 :=
    hupper.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hscaled : (1 - q n) * Real.sqrt (n : ℝ) ≤ M :=
    (le_div_iff₀ hsqrt).1 hdef
  have hnonneg : 0 ≤ (1 - q n) * Real.sqrt (n : ℝ) :=
    mul_nonneg (sub_nonneg.2 (hq n).2) hsqrt.le
  have hsquare : ((1 - q n) * Real.sqrt (n : ℝ)) ^ 2 ≤ M ^ 2 := by
    nlinarith
  have hbudget : (1 - q n) ^ 2 ≤ M ^ 2 / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    simpa only [mul_pow, Real.sq_sqrt hnR.le] using hsquare
  calc
    unrestrictedMinimaxRisk n (d n) (q n) ≤
        4 / (n : ℝ) + (1 - q n) ^ 2 := hupper'
    _ ≤ 4 / (n : ℝ) + M ^ 2 / (n : ℝ) := add_le_add_right hbudget _
    _ = (4 + M ^ 2) / (n : ℝ) := by rw [add_div]


end CausalSmith.Stat.MarRareqLogfrontier
