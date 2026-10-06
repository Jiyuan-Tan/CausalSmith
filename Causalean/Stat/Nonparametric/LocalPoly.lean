/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.LocalPoly.CoordinateDerivative
public import Causalean.Stat.Nonparametric.LocalPoly.DesignMatrixPosDef
public import Causalean.Stat.Nonparametric.LocalPoly.EstimatorRisk
public import Causalean.Stat.Nonparametric.LocalPoly.GramCoercivity
public import Causalean.Stat.Nonparametric.LocalPoly.Rate.IntegralMoment

/-!
# Local-polynomial estimator substrate

Degree-`p` local-polynomial regression substrate: equivalent-kernel weights, design positive
definiteness, bias, variance, leverage rates, and pointwise risk bounds.

This barrel collects the degree-`p` local-polynomial regression substrate:

* `LocalPoly/Weights.lean` — the design moment matrix `designMatrix` and the equivalent-kernel
  weights `equivKernelWeight`.
* `LocalPoly/DesignMatrixPosDef.lean` — the empirical-Gram positive-definiteness lemmas.
* `LocalPoly/Bias.lean` — the interior local-polynomial bias bound.
* `LocalPoly/SmootherVariance.lean` — the local-polynomial specialization of the
  heteroskedastic, uncorrelated-error variance bound (`localPoly_intercept_variance_le`).
* `LocalPoly/Rate.lean` (+ `Rate/Conjugation.lean`, `Rate/IntegralMoment.lean`) — deterministic
  design-inverse perturbation and one-sided leverage upper bounds.
* `LocalPoly/EstimatorRisk.lean` — conditional estimator bounds and generic event-splitting lifts.
  No theorem in this barrel connects them to a random-design concentration event.

The barrel also exports `CoordinateDerivative.lean` and `GramCoercivity.lean`. These are
standalone bivariate analytic helpers; no theorem here connects them to the local-polynomial
design matrices or estimator bounds listed above.
-/
