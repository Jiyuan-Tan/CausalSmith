module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.Estimator
public import Causalean.Mathlib.Probability.EventSelectedMixture
public import Mathlib.Algebra.Order.Chebyshev

/-! Algebraic variance identities for the pilot-selected hybrid statistic. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability

/-- A difference of two arm contributions costs at most twice the sum of
their squared contributions.  [the stated conclusion](goal). -/
lemma sq_sub_le_two_sq_add_two_sq (x y : Real) :
    (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x + y)]

/-- Clipping to `[-1,1]` contracts squared loss for a target in that interval.  [the stated conditions](hyp:htheta) [the stated conclusion](goal). -/
lemma hybrid_clipUnit_sq_sub_le (z theta : Real)
    (htheta : theta ∈ Set.Icc (-1 : Real) 1) :
    (clipUnit z - theta) ^ 2 ≤ (z - theta) ^ 2 := by
  rcases htheta with ⟨htheta0, htheta1⟩
  simp only [clipUnit]
  by_cases hz0 : z < -1
  · rw [min_eq_right (by linarith), max_eq_left hz0.le]
    nlinarith [sq_nonneg (z - theta)]
  · have hm0 : -1 ≤ min 1 z := by simp [le_min_iff, le_of_not_gt hz0]
    rw [max_eq_right hm0]
    by_cases hz1 : 1 < z
    · rw [min_eq_left hz1.le]
      nlinarith [sq_nonneg (z - theta)]
    · rw [min_eq_right (le_of_not_gt hz1)]

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
