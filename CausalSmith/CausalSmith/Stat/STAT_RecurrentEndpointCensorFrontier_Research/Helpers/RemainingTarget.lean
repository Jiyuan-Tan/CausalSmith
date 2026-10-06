module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.Estimators

/-!
# Boundary values of the remaining target

The remaining target starts at the truncated mean and vanishes at the
truncation horizon. These are the boundary terms in the error decomposition.
-/

public section

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: remainingTarget_at_zero
lemma remainingTarget_at_zero (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h : ℝ) :
    remainingTarget c P a h 0 = truncatedMean c P a h := by
  rfl

-- @node: remainingTarget_at_horizon
lemma remainingTarget_at_horizon (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h : ℝ) :
    remainingTarget c P a h (1 - h) = 0 := by
  simp [remainingTarget]

-- @node: remainingTarget_complement
lemma remainingTarget_complement (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h u : ℝ)
    (hLeft : IntervalIntegrable
      (fun t => continuationWeight (holderOrder c) h t *
        survival P a t * P.lam a t) MeasureTheory.volume 0 u)
    (hRight : IntervalIntegrable
      (fun t => continuationWeight (holderOrder c) h t *
        survival P a t * P.lam a t) MeasureTheory.volume u (1 - h)) :
    (∫ t in (0 : ℝ)..u,
      continuationWeight (holderOrder c) h t * survival P a t * P.lam a t) +
      remainingTarget c P a h u = truncatedMean c P a h := by
  exact intervalIntegral.integral_add_adjacent_intervals hLeft hRight

-- @node: remainingTarget_integral_eq_sub
lemma remainingTarget_integral_eq_sub (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h x y : ℝ)
    (hLeft : IntervalIntegrable
      (fun t => continuationWeight (holderOrder c) h t *
        survival P a t * P.lam a t) MeasureTheory.volume x y)
    (hRight : IntervalIntegrable
      (fun t => continuationWeight (holderOrder c) h t *
        survival P a t * P.lam a t) MeasureTheory.volume y (1 - h)) :
    (∫ t in x..y,
      continuationWeight (holderOrder c) h t * survival P a t * P.lam a t) =
      remainingTarget c P a h x - remainingTarget c P a h y := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals hLeft hRight
  change (∫ t in x..y,
      continuationWeight (holderOrder c) h t * survival P a t * P.lam a t) +
      remainingTarget c P a h y = remainingTarget c P a h x at hsum
  linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
