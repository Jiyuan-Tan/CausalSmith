/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.SeriesSieve.Jackson
public import Causalean.Stat.Nonparametric.SeriesSieve.PredictionRate

/-!
# Series (sieve) least squares: approximation and prediction

Tools for regression on a finite set of basis functions. On the approximation side, the
piecewise-Taylor approximant of a `β`-Hölder function on `J` uniform cells has sup-norm error of
order `J^(−β)`. On the estimation side, the closed-form least-squares coefficients satisfy the
normal equations, the hat matrix has squared Frobenius norm equal to the number of basis
functions, the prediction error splits exactly into approximation and estimation parts, and under
mean-zero uncorrelated errors with variances at most `σ̄²` the expected prediction error obeys an
oracle inequality.

## Contents

* `SeriesSieve/Jackson` — `piecewiseTaylor_sup_approx`, `piecewiseTaylor_sup_approx_rate`. The
  approximant is function-valued: it is not represented in a finite basis, and `J` is not
  identified with a basis cardinality.
* `SeriesSieve/LeastSquares` — `seriesLSCoeff`, `seriesHatMatrix`;
  `seriesLSCoeff_normal_equations`, `seriesHatMatrix_frobenius_sq`.
* `SeriesSieve/Prediction` — `seriesApprox_le_of_sup`, `seriesLS_prediction_decomp`,
  `seriesLS_expected_prediction_le` (a conditional heteroskedastic oracle inequality).
* `SeriesSieve/PredictionRate` — `seriesLS_prediction_rate_of_jackson_bound`: a prediction bound
  conditional on an assumed Jackson-shaped bound for the noise-free objective; linking that bound
  to a concrete basis is left to the caller.
-/
