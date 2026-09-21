/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.SeriesSieve.Jackson
public import Causalean.Stat.Nonparametric.SeriesSieve.PredictionRate

/-!
# Series / sieve `L²` substrate

This barrel collects reusable series/sieve approximation and prediction tools for
nonparametric regression and projection arguments.

* `SeriesSieve/Jackson.lean` — a Jackson-type bound for a function-valued piecewise-Taylor
  approximant on `J` cells (`piecewiseTaylor_sup_approx`, `piecewiseTaylor_sup_approx_rate`). It
  does not represent that approximant in a finite basis or identify `J` with basis cardinality.
* `SeriesSieve/LeastSquares.lean` — closed-form series least-squares coefficients and hat-matrix
  identities for an arbitrary finite design.
* `SeriesSieve/Prediction.lean` — empirical approximation reduction, exact Pythagorean prediction
  decomposition, and a conditional heteroskedastic oracle inequality.
* `SeriesSieve/PredictionRate.lean` — a finite-dimensional prediction bound conditional on an
  assumed Jackson-shaped objective bound; the basis-membership bridge is left to the caller.

Built on normal-equation identities from `Causalean.Mathlib.LinearAlgebra.NormalEquations` and
the shared fixed-weight linear-smoother variance layer.
-/
