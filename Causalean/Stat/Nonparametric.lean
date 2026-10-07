/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.Approximation
public import Causalean.Stat.Nonparametric.GaussianTransfer
public import Causalean.Stat.Nonparametric.HigherOrderInfluence
public import Causalean.Stat.Nonparametric.HistogramRegression
public import Causalean.Stat.Nonparametric.LinearSmoother
public import Causalean.Stat.Nonparametric.LocalPoly
public import Causalean.Stat.Nonparametric.SeriesSieve
public import Causalean.Stat.Nonparametric.Specialization

/-!
# Nonparametric regression and smoothing

Finite-sample bias, variance and risk bounds for nonparametric estimators of a regression function
under Hölder smoothness. A linear smoother whose weights reproduce polynomials of degree below `β`
has bias at most a constant times `h^β` for a `β`-Hölder function, and variance at most
`σ̄² ∑ᵢ Sᵢ²` under uncorrelated errors with variances bounded by `σ̄²`; these two facts are
specialized to local-polynomial and series (sieve) least-squares estimators. The histogram
regression estimator on a cubical partition of `[0,1]^d` attains integrated squared risk of order
`m^(−2β/(2β+d))`, with explicit constants.

## Contents

* `Approximation` — Hölder–Taylor remainders, the `O(h^β)` kernel-convolution bias, monomial
  approximation in a multivariate Hölder ball, and a pointwise-to-local-L¹ interpolation
  inequality.
* `LinearSmoother` — `linearSmoother_bias_window` and `linearSmoother_variance_le`.
* `LocalPoly` — design moment matrix and equivalent-kernel weights, positive definiteness, bias
  and variance of the intercept, `O(1/(Nh))` leverage bounds, and conditional risk bounds with
  generic lifts from a good-design event.
* `SeriesSieve` — piecewise-Taylor (Jackson-type) approximation at rate `J^(−β)`, series
  least-squares identities, and a conditional prediction oracle inequality.
* `HistogramRegression` — `histogram_risk_le` for an arbitrary finite measurable partition and
  `optimized_cubical_histogram_risk_le` for the Hölder cubical case.
* `HigherOrderInfluence` — the projection kernel `⟨c(x), Σ⁻¹ c(y)⟩` has L² energy equal to its
  dimension `J`; algebra combining assumed component bounds into a risk bound.
* `GaussianTransfer`, `Specialization` — bounds on a Gaussian-shifted design variance integral by
  weighted L² energies of the kernel, and its inverse-Gaussian-multiplier specialization.

This file only gathers the modules above.
-/
