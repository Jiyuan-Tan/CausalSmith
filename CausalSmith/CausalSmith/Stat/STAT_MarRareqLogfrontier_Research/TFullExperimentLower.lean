module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.FuzzyTesting

/-! TFullExperimentLower for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: frontier_min_sum_le
/-- Given [the specified inputs and assumptions](hyp:a,b,ha,hb), [the stated mathematical conclusion holds](goal). -/
lemma frontier_min_sum_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ≤ min 1 a + min 1 b := by
  rcases le_total a 1 with ha1 | ha1
  · rcases le_total b 1 with hb1 | hb1
    · simpa [min_eq_right ha1, min_eq_right hb1] using
        (min_le_right (1 : ℝ) (a + b))
    · rw [min_eq_right ha1, min_eq_left hb1]
      have : 0 ≤ a := ha
      exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left ha1]
    have : 0 ≤ min 1 b := le_min (by norm_num) hb
    exact (min_le_left _ _).trans (by linarith)

-- @node: thm:full-experiment-lower
/-- [the stated mathematical conclusion holds](goal). -/
theorem full_experiment_lower :
    ∃ c : ℝ, 0 < c ∧ -- @realizes \(\underline c\)(universal lower constant)
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
        RareArrivalSlice n q → c * frontierRate n d q ≤ minimaxRisk n d q := by
  obtain ⟨c₀, cInterval, hc₀, -, hOne⟩ := one_cell_testing_family
  obtain ⟨c₁, hc₁, hMany⟩ := activated_fuzzy_lower
  refine ⟨min c₀ c₁ / 4, by positivity, ?_⟩
  intro n d q hn hd hq hq1 hslice
  obtain ⟨_, hBern, hPoint, _⟩ := hOne n d q hn hd hq hq1 hslice
  obtain ⟨_, _, _, _, _, hRiskOne⟩ := hPoint
  let N := effectiveSize n q
  let L := logScale n q
  let a := N⁻¹
  let b := ((d : ℝ) / (N * L)) ^ 2
  have hN : 0 < N := by
    dsimp [N, effectiveSize]
    positivity
  have hL : 1 ≤ L := by
    change 1 ≤ Real.log (Real.exp 1 + N)
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := sq_nonneg _
  have hOne' : c₀ * min 1 a ≤ minimaxRisk n d q := hRiskOne.2
  have hMany' : Real.sqrt N ≤ d → c₁ * min 1 b ≤ minimaxRisk n d q := by
    intro h
    exact hMany n d q hn hd hq hq1 hslice h
  have hr : frontierRate n d q = min 1 (a + b) := rfl
  rw [hr]
  by_cases hdim : Real.sqrt N ≤ d
  · have hbRisk := hMany' hdim
    have hmin := frontier_min_sum_le a b ha hb
    have hmax : min 1 a ≤ max (min 1 a) (min 1 b) := le_max_left _ _
    have hmax' : min 1 b ≤ max (min 1 a) (min 1 b) := le_max_right _ _
    have hc : 0 < min c₀ c₁ := lt_min hc₀ hc₁
    have h₀ : min c₀ c₁ ≤ c₀ := min_le_left _ _
    have h₁ : min c₀ c₁ ≤ c₁ := min_le_right _ _
    have hma : 0 ≤ min 1 a := le_min (by norm_num) ha
    have hmb : 0 ≤ min 1 b := le_min (by norm_num) hb
    have hca := mul_nonneg (sub_nonneg.mpr h₀) hma
    have hcb := mul_nonneg (sub_nonneg.mpr h₁) hmb
    have hbound := mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ min c₀ c₁ / 4)
    nlinarith
  · have hdim' : (d : ℝ) ≤ Real.sqrt N := le_of_not_ge hdim
    have hN0 : 0 ≤ N := le_of_lt hN
    have hsqrt := Real.sq_sqrt hN0
    have hden : 0 < N * L := mul_pos hN (by linarith)
    have hb_le : b ≤ a := by
      dsimp [a, b]
      have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
      have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
      have hsq : ((d : ℝ) : ℝ) ^ 2 ≤ N := by nlinarith
      have hNL : 0 < N * L := hden
      rw [div_pow]
      apply (div_le_iff₀ (pow_pos hNL 2)).2
      have hL2 : 1 ≤ L ^ 2 := by nlinarith
      have heq : N⁻¹ * (N * L) ^ 2 = N * L ^ 2 := by
        field_simp [ne_of_gt hN]
      rw [heq]
      nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hL2)]
    have hminb : min 1 b ≤ min 1 a := min_le_min_left 1 hb_le
    have hmin := frontier_min_sum_le a b ha hb
    have h₀ : min c₀ c₁ ≤ c₀ := min_le_left _ _
    have hma : 0 ≤ min 1 a := le_min (by norm_num) ha
    have hca := mul_nonneg (sub_nonneg.mpr h₀) hma
    have hbound := mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ min c₀ c₁ / 4)
    have hcb := mul_le_mul_of_nonneg_left hminb (by positivity : 0 ≤ min c₀ c₁ / 4)
    nlinarith

end CausalSmith.Stat.MarRareqLogfrontier
