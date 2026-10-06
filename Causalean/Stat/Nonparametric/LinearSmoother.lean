/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.LinearSmoother.Bias
public import Causalean.Stat.Nonparametric.LinearSmoother.Variance

/-!
# Fixed-weight linear-smoother building blocks

Design-agnostic deterministic bias and heteroskedastic, uncorrelated-error variance bounds for
fixed-weight linear smoothers.

This barrel collects the design-agnostic fixed-weight linear-smoother results consumed by both the
local-polynomial and the series/sieve estimators:

* `LinearSmoother/Bias.lean` — the deterministic bias of a fixed-weight linear smoother.
* `LinearSmoother/Variance.lean` — the generic variance bound under pairwise uncorrelated errors
  with `Var[Yᵢ] ≤ σ̄²`, together with its leverage consequence.
-/
