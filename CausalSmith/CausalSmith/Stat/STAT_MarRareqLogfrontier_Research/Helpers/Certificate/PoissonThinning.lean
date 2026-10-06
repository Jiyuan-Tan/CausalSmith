module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.ChebyshevNeedle
public import Causalean.Stat.Concentration.Poisson.Threshold

/-! Poisson cap and thinning bookkeeping for the three streams. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: poisson_half_prefix_tail
/-- Given [the specified inputs and assumptions](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma poisson_half_prefix_tail (n : ℕ) :
    (poissonMeasure ((n : ℝ≥0) / 2)).real {k : ℕ | n < k} ≤
      Real.exp (-(n : ℝ) * (Real.log 2 - 1 / 2)) := by
  have h := Causalean.Stat.Concentration.Poisson.poisson_upper_tail_mul_exp_le
    ((n : ℝ≥0) / 2) n (r := 1) (by norm_num)
  have hexp : 0 < Real.exp (-((n : ℝ) / 2)) := Real.exp_pos _
  apply le_of_mul_le_mul_right _ hexp
  calc
    (poissonMeasure ((n : ℝ≥0) / 2)).real {k : ℕ | n < k} *
        Real.exp (-((n : ℝ) / 2)) ≤ Real.exp (-Real.log 2 * (n : ℝ)) := by
          convert h using 1 <;> norm_num [NNReal.coe_div]
    _ = Real.exp (-(n : ℝ) * (Real.log 2 - 1 / 2)) *
        Real.exp (-((n : ℝ) / 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring

end CausalSmith.Stat.MarRareqLogfrontier
