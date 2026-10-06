module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Basic
/-! Borel point-containment events for the shared interval representation. -/
public section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Point containment is Borel for every empty, finite, or unbounded interval code. [The displayed conclusion](goal) follows. -/
-- @node: measurableSet_interval_contains
lemma measurableSet_interval_contains (x : ℝ) :
    MeasurableSet {c : IntervalCode | x ∈ c.toSet} := by
  apply measurableSet_sum_iff.mpr
  constructor
  · simp [IntervalCode.toSet]
  · change MeasurableSet {p : EReal × EReal × Bool × Bool |
      (if p.2.2.1 then p.1 ≤ (x : EReal) else p.1 < (x : EReal)) ∧
      (if p.2.2.2 then (x : EReal) ≤ p.2.1 else (x : EReal) < p.2.1)}
    have hl : Measurable (fun p : EReal × EReal × Bool × Bool => p.1) := by fun_prop
    have hu : Measurable (fun p : EReal × EReal × Bool × Bool => p.2.1) := by fun_prop
    have hc0 : MeasurableSet {p : EReal × EReal × Bool × Bool | p.2.2.1 = true} := by
      exact measurableSet_eq_fun (by fun_prop) measurable_const
    have hc1 : MeasurableSet {p : EReal × EReal × Bool × Bool | p.2.2.2 = true} := by
      exact measurableSet_eq_fun (by fun_prop) measurable_const
    convert
      (MeasurableSet.ite hc0 (measurableSet_le hl (measurable_const (a := (x : EReal))))
        (measurableSet_lt hl (measurable_const (a := (x : EReal))))).inter
      (MeasurableSet.ite hc1 (measurableSet_le (measurable_const (a := (x : EReal))) hu)
        (measurableSet_lt (measurable_const (a := (x : EReal))) hu)) using 1
    ext p
    simp [Set.ite, ite_prop_iff_or, and_comm]

end CausalSmith.Stat.PrivateCateRoughdesign
