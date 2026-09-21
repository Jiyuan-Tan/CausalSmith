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
# Local-polynomial conditional bounds and generic unconditional lifts

Reusable local-polynomial and probabilistic bounds, including density constants, leverage bounds,
conditional MSE factorization, and generic unconditional risk lifts.

This barrel collects square completion of the conditional bias/variance trade-off, density and
leverage bounds, conditional MSE factorization, and generic theorems that lift assumed good-event
bounds to the full sample law. It does not connect a random local-polynomial estimator, a concrete
good-design event, and a concentration theorem in one capstone.
-/
