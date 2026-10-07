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
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate
public import Causalean.Stat.Nonparametric.LocalPoly.Rate.IntegralMoment

/-!
# Local-polynomial regression

Finite-sample analysis of the degree-`p` local-polynomial estimator at an interior point. The
weighted least-squares intercept is a linear smoother with equivalent-kernel weights built from
the inverse of the design moment matrix; these weights reproduce polynomials of degree up to `p`,
so the estimator has bias of order `h^β` for a `β`-Hölder regression function and, under
uncorrelated errors with variances at most `σ̄²` and kernel weights at most `W`, variance at most
`σ̄² W (M⁻¹)₀₀`, where `M` is the design moment matrix. On a design event
where the empirical moment matrix is close to its population counterpart, `(M⁻¹)₀₀` is of order
`1/(Nh)`.

In dimension one, with independent design points whose density is bounded above and below by
positive constants near the evaluation point, that design event is constructed and shown to fail
with exponentially small probability. The estimator clipped to `[-M, M]`, where `M` bounds the
regression function at the evaluation point, then has unconditional mean-squared error at most
`C_bias² h^(2β) + C_var/(Nh) + 16 M² (p+1)² exp(-c₀ N h)`, and at `h = N^(-1/(2β+1))` at most an
explicit constant times `N^(-2β/(2β+1))`. These are upper bounds for the clipped estimator; no
condition on the realized design is assumed.

## Contents

* `LocalPoly/Weights` — `designMatrix`, `equivKernelWeight`; `equivKernelWeight_reproduces`,
  `wls_intercept_eq_equivKernelSmoother`, and the leverage identities.
* `LocalPoly/DesignMatrixPosDef` — `designMatrix_posDef`, `nondegenerate_of_distinct_points`: the design
  moment matrix is positive definite when at least `p + 1` distinct design points carry positive
  weight.
* `LocalPoly/Bias` — `localPoly_intercept_bias`, the interior `O(h^β)` bias bound, and
  `localPoly_intercept_bias_within` for a regression function smooth only on a window.
* `LocalPoly/SmootherVariance` — `localPoly_intercept_variance_le`.
* `LocalPoly/Rate` (with `Rate/Conjugation`, `Rate/IntegralMoment`) — `localPoly_inv00_rate`,
  `localPoly_leverage_bound`: deterministic design-inverse perturbation and one-sided leverage
  bounds, given entrywise closeness of the empirical and population moment matrices.
* `LocalPoly/EstimatorRisk` — conditional bias and stochastic-error bounds for the estimator and
  generic lifts from a good-design event to the full sample law.
* `LocalPoly/RandomDesignRate` — one-dimensional random design:
  `localPoly_moment_entrywise_bernstein` and `localPoly_moment_simultaneous_probability`
  (concentration of the kernel-weighted design moments), `localPoly_leverage_on_momentEvent`
  (the moment event implies an invertible design matrix with `O(1/(Nh))` leverage),
  `localPoly_clipped_mse_unconditional` (the unconditional mean-squared-error bound) and
  `localPoly_clipped_pointwise_rate` (the `N^(-2β/(2β+1))` rate).
* `LocalPoly/CoordinateDerivative`, `LocalPoly/GramCoercivity` — standalone bivariate analytic
  helpers.
-/
