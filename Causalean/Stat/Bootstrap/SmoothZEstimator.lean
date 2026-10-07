/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Bootstrap.SmoothZEstimator.Basic
public import Causalean.Stat.Bootstrap.SmoothZEstimator.BootstrapLinearization
public import Causalean.Stat.Bootstrap.SmoothZEstimator.FeasibleGMM
public import Causalean.Stat.Bootstrap.SmoothZEstimator.FeasibleGMMHelpers
public import Causalean.Stat.Bootstrap.SmoothZEstimator.FeasibleGMMLinearization
public import Causalean.Stat.Bootstrap.SmoothZEstimator.Main
public import Causalean.Stat.Bootstrap.SmoothZEstimator.OLS
public import Causalean.Stat.Bootstrap.SmoothZEstimator.OLSConditions
public import Causalean.Stat.Bootstrap.SmoothZEstimator.SamplingLinearization

/-! # Bootstrap validity for smooth Z-estimators

Efron's bootstrap for estimators θ̂ solving a finite-dimensional estimating equation
(1/n) Σ ψ(θ, Xᵢ) = 0 with a smooth score ψ. For any continuous linear contrast c, the estimator
c(θ̂) is bootstrap asymptotically linear with influence function −c(J₀⁻¹ ψ(θ₀, X)), J₀ the
population Jacobian, so the percentile and basic bootstrap intervals for c(θ₀) have asymptotic
coverage 1 − α. The general theorem assumes, besides smooth-score regularity and positive
influence variance, that the estimator and its resampled version are consistent and solve their
estimating equations up to a residual of smaller order than n^(−1/2); no Donsker or stochastic
equicontinuity condition is required.

## Main results

* `zEstimator_samplingLinearization`, `zEstimator_bootstrapLinearization` — the sampling and
  conditional bootstrap linearizations of the coefficient vector.
* `BootstrapAsymLinear.zEstimator`, `zEstimator_percentileCI_coverage`,
  `zEstimator_basicCI_coverage` — bootstrap asymptotic linearity and coverage for a contrast.
* `olsContrast`, `olsContrast_of_moments`, `olsContrast_percentileCI_coverage_of_moments` — OLS:
  with measurable regressors and outcome, integrable monomials through degree four and a
  positive-definite population Gram matrix, the bootstrap-side hypotheses are proved, so
  coverage holds with no assumption on the resampling.
* `feasibleGMM_bootstrapLinearization_of_smoothMoment`, `BootstrapAsymLinear.feasibleGMM` —
  feasible GMM with an estimated weight matrix, assuming data and bootstrap consistency of the
  parameter and the weight and negligible first-order-condition residuals.
-/
