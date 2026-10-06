module
public import Causalean.Mathlib.Analysis.RealInterpolation.Basic

/-!
# Measurability of the scale-dependent K-functional

Monotonicity on positive scales supplies the measurability needed for dilation.
The endpoint gauges need not themselves be measurable, since each decomposition
cost depends continuously on the scale and the infimum is monotone there.
-/

public section
open MeasureTheory Set
open scoped ENNReal
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- [Arbitrary endpoint gauges](hyp:n0,n1) and [a vector](hyp:v) give
[a monotone squared K-functional on positive scales](goal). -/
theorem monotoneOn_kFunctionalSq {V : Type*} [AddCommGroup V]
    (n0 n1 : V → ℝ≥0∞) (v : V) :
    MonotoneOn (fun t => kFunctionalSq n0 n1 t v) (Ioi (0 : ℝ)) := by
  intro s hs t ht hst
  unfold kFunctionalSq
  refine iInf_mono fun v0 => iInf_mono fun v1 => iInf_mono fun _ => ?_
  exact add_le_add le_rfl
    (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (le_of_lt hs) hst 2)) le_rfl)

/-- [Arbitrary endpoint gauges](hyp:n0,n1) and [a vector](hyp:v) give
[a measurable K-functional after restriction to positive scales](goal).
Use monotoneOn_kFunctionalSq and measurable extension by zero. -/
theorem measurable_kFunctionalSq_indicator {V : Type*} [AddCommGroup V]
    (n0 n1 : V → ℝ≥0∞) (v : V) :
    Measurable (Set.indicator (Ioi (0 : ℝ)) (fun t => kFunctionalSq n0 n1 t v)) := by
  apply Monotone.measurable
  intro s t hst
  by_cases hs : s ∈ Ioi (0 : ℝ)
  · have ht : t ∈ Ioi (0 : ℝ) := lt_of_lt_of_le hs hst
    simp only [Set.indicator_of_mem hs, Set.indicator_of_mem ht]
    exact monotoneOn_kFunctionalSq n0 n1 v hs ht hst
  · simp only [Set.indicator_of_notMem hs]
    exact zero_le

end Causalean.Mathlib.Analysis.RealInterpolation
