/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.DensityLeverage
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.EstimatorRisk
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk.Unconditional

/-!
# Conditional risk of the local-polynomial estimator and unconditional lifts

Given the design, the degree-`p` local-polynomial intercept of a `β`-Hölder regression function
has bias at most `Cbias · h^β` and stochastic L² error at most `Cvar · (Nh)^(−1/2)`, with the
leverage constants expressed through lower and upper bounds on the design density over the kernel
window. Separately, for a bounded estimator and a design-measurable good event, bounds on the
conditional bias and variance that hold on the event lift to unconditional bounds, at the cost of
a term proportional to the probability of the complement.

## Main results

* `localPoly_estimatorBias_window`, `localPoly_estimatorStochL2` (`EstimatorRisk/EstimatorRisk`) —
  the conditional bias and stochastic-error bounds.
* `localPoly_density_inv00_rate`, `localPoly_density_leverage_bound`
  (`EstimatorRisk/DensityLeverage`) — conditional `O(1/(Nh))` leverage bounds with explicit density
  constants; `popDesignMatrix_factor` and the quadratic-form sandwich lemmas support them.
* `estimatorBias_unconditional`, `estimatorVariance_unconditional`,
  `estimatorStochL2_unconditional` (`EstimatorRisk/Unconditional`) — the lifts from a good-design
  event.

`LocalPoly/RandomDesignRate` applies these lifts in dimension one to a design event that it
constructs from kernel-moment concentration, giving an unconditional mean-squared-error bound and
the `N^(-2β/(2β+1))` rate for the clipped estimator under a design density bounded above and
below near the evaluation point.
-/
