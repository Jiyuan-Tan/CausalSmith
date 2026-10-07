module
public import Mathlib.Probability.CentralLimitTheorem

/-! # One-sided modulus of a difference of distribution functions

An interval-mass bound on a reference law controls how far the difference
of two cumulative distribution functions can fall as its argument increases.
This is the pointwise order estimate used before integrating a smoothing kernel.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- If [ν assigns every interval at most L times its length](hyp:hν), then for [any points a ≤ b](hyp:hab)
[the CDF difference Fμ − Fν at a is at most its value at b plus
L·(b − a)](goal). -/
theorem cdf_difference_one_sided_modulus
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (L : ℝ)
    (hν : ∀ a b : ℝ, a ≤ b →
      (ν (Set.Ioc a b)).toReal ≤ L * (b - a))
    (a b : ℝ) (hab : a ≤ b) :
    (μ (Set.Iic a)).toReal - (ν (Set.Iic a)).toReal ≤
      (μ (Set.Iic b)).toReal - (ν (Set.Iic b)).toReal + L * (b - a) := by
  /- Use `Iic b = Iic a ∪ Ioc a b` and monotonicity of μ. The same
  disjoint union identifies the ν-CDF increment with its interval mass;
  convert the finite ENNReal measures to real numbers. -/
  have hμmono : (μ (Set.Iic a)).toReal ≤ (μ (Set.Iic b)).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Iic_subset_Iic.mpr hab))
  have hνadd : (ν (Set.Iic b)).toReal =
      (ν (Set.Iic a)).toReal + (ν (Set.Ioc a b)).toReal := by
    rw [← Set.Iic_union_Ioc_eq_Iic hab,
      measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)]
  have hbound := hν a b hab
  linarith

end Causalean.Stat.CLT.BerryEsseen
