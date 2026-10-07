/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.LinearSmoother.Bias
public import Causalean.Stat.Nonparametric.LinearSmoother.Variance

/-!
# Bias and variance of fixed-weight linear smoothers

A linear smoother estimates `f(t)` by `∑ᵢ Sᵢ Yᵢ` with weights that depend only on the design. If
the weights reproduce polynomials of degree up to `p` (the largest integer strictly below `β`) at
`t` and `f` is `β`-Hölder with constant `M`, the bias satisfies
`|∑ᵢ Sᵢ f(aᵢ) − f(t)| ≤ (M/p!) ∑ᵢ |Sᵢ| |aᵢ − t|^β`, which is of order `h^β` when all design points
lie within `h` of `t`. If the responses are pairwise uncorrelated with variances at most `σ̄²`,
then `Var(∑ᵢ Sᵢ Yᵢ) ≤ σ̄² ∑ᵢ Sᵢ²`. Both bounds hold for any design and are shared by the
local-polynomial and series estimators.

## Main results

* `linearSmoother_bias_of_reproduces`, `linearSmoother_bias_window` (`LinearSmoother/Bias`) — the
  weighted-spread bias bound and its `O(h^β)` window form.
* `linearSmoother_variance_le` (`LinearSmoother/Variance`) — the variance bound, for an
  `UncorrelatedVarianceFamily` of responses.
-/
