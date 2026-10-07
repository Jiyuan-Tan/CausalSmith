/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.FunctionalDelta

/-!
# Functional delta method for directionally differentiable maps

If a finite-dimensional estimator satisfies `rₙ (θ̂ₙ − θ) ⇒ Q` for a diverging rate `rₙ`, and `φ`
is Hadamard directionally differentiable at `θ` with a continuous (possibly nonlinear) derivative
`φ′`, then `rₙ (φ(θ̂ₙ) − φ(θ)) ⇒ φ′(Q)`, the image of the limit law under `φ′` (Shapiro 1991;
Fang–Santos 2019, in the finite-dimensional case). Applied to the maximum and the minimum of two
estimators this gives their limit laws at any base point, including ties, where the derivative
is `max(u, v)` or `min(u, v)` and the limit is not Gaussian.

## Main results (all proved in `Causalean.Stat.CLT.FunctionalDelta`)

* `functionalDeltaMethod` — the delta method above; measurability of the rescaled deviations and
  continuity of `φ′` are hypotheses.
* `HasHadamardDirDerivAt.uniform_on_bounded` — the rescaled increments converge to `φ′` uniformly
  on bounded sets.
* `deltaMethod_max_rate`, `deltaMethod_min_rate` — limit laws of the maximum and minimum of two
  estimators at a general rate; `deltaMethod_max`, `deltaMethod_min` at rate `√n`.

This file declares nothing itself; it makes that module available under the inference-layer path.
-/
