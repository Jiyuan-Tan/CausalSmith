/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Nonparametric.LinearSmoother.Variance
public import Causalean.Stat.Nonparametric.LocalPoly.Weights

/-!
# Variance of the interior local-polynomial estimator

Specializes the generic uncorrelated heteroskedastic linear-smoother variance bound
(`Causalean.Stat.Nonparametric.LinearSmoother.Variance`) to the degree-`p`
local-polynomial equivalent-kernel weights. The leverage `∑ᵢ Sᵢ²` is controlled by the
intercept entry of the inverse design moment matrix `(M⁻¹)₀₀`
(`equivKernelWeight_sq_sum_le`), so the interior `O((Nh)^{−1/2})` stochastic-error rate
reduces to the single design-concentration bound `(M⁻¹)₀₀ = O(1/(Nh))`.
-/

public section

namespace Causalean.Stat.Nonparametric

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- **Variance of the interior local-polynomial estimator.** The degree-`p` local-polynomial
equivalent-kernel smoother `∑ᵢ Sᵢ Yᵢ`, applied to [a family `Y` of square-integrable
responses](hyp:hY) whose [distinct coordinates are uncorrelated and individual variances are
bounded by `σbar²`](hyp:hnoise), with [an invertible design
moment matrix](hyp:hM) and [nonnegative weights](hyp:hw) [bounded above by a constant
`W`](hyp:hwW), has [variance `Var[∑ᵢ Sᵢ Yᵢ] ≤ σ² · W · (M⁻¹)₀₀`](goal). This reduces the interior
`O((Nh)^{−1/2})` stochastic-error rate to the single design-concentration bound
`(M⁻¹)₀₀ = O(1/(Nh))`. -/
theorem localPoly_intercept_variance_le {Ω : Type*} {N p : ℕ} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {x w : Fin N → ℝ} {Y : Fin N → Ω → ℝ}
    {σbar W : ℝ}
    (hY : ∀ i, MemLp (Y i) 2 μ)
    (hnoise : UncorrelatedVarianceFamily Y μ σbar)
    (hM : IsUnit (designMatrix p x w).det)
    (hw : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) :
    Var[fun ω => ∑ i, equivKernelWeight p x w i * Y i ω; μ]
      ≤ σbar ^ 2 * (W * (designMatrix p x w)⁻¹ 0 0) :=
  linearSmoother_variance_le hY hnoise (equivKernelWeight_sq_sum_le hM hw hwW)

end Causalean.Stat.Nonparametric
