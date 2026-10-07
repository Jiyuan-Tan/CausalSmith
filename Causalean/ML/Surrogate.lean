/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Surrogate.ClampedSquare
public import Causalean.ML.Surrogate.ProperLoss

/-!
# Surrogate losses

Two tools for replacing a loss by a better-behaved one. The clamped square agrees with t² on
[−c, c], is 2c-Lipschitz on the whole line and vanishes at zero, which is what a contraction
argument needs to pass Rademacher complexity bounds through the squared loss on a bounded
prediction range. A proper binary loss is one whose expected value under a Bernoulli(η) label is
minimized by predicting η; integrating this shows that predicting the true conditional probability
has the smallest population risk among measurable [0, 1]-valued predictors, and for a strictly
proper loss every population risk minimizer equals the true conditional probability almost
everywhere.

## Contents

* `ClampedSquare` — `clampedSq`, `clampedSq_eq_sq` (agreement with the square on the band) and
  `lipschitzAt0_clampedSq` (the Lipschitz and zero-at-zero property).
* `ProperLoss` — `ProperBinaryLoss`, `StrictProperBinaryLoss`, `properLoss_population_risk_le`
  and `properLoss_population_minimizer_recovers_eta`.
-/
