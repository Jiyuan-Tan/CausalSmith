/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.Regime

/-!
# Localized hypotheses for the NPIV empirical-process event

The assumptions under which the empirical process of the regularized adversarial NPIV estimator
is controlled, gathered from `Regime`. `LocalizedRegimeBundle` packages one loss class with its
sample map, a critical-radius certificate and radius-uniform boundedness and integrability.
`LocalizedRegimes` collects four such bundles — for candidate–critic products, moment–critic
compositions, critics and candidates — together with the law of the observation, realizability of
the population Tikhonov solution in the candidate class, uniform boundedness, the closedness
condition (every candidate has a critic realizing its projected residual), and diameter bounds.
`PeelingFloor` states, at one confidence level, that the variance-sensitive slack is absorbed at
a finite dyadic peeling depth for each class. These are hypotheses consumed by the deviation
events and the final rate event; this file adds no declarations of its own.

## Main results

* `peelingFloor_quarter_of_unit_scale` — the peeling condition holds at unit radius with at
  least 32 observations when the four envelope constants are zero and the four peeled radii are
  at most one (a satisfiability check, not a general sufficient condition).
-/

public section
