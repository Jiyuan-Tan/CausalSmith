/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.MEstimation.ArgmaxStability
public import Causalean.Stat.MEstimation.EmpiricalExpansion
public import Causalean.Stat.MEstimation.ExtremumConsistency
public import Causalean.Stat.MEstimation.FiniteModelSelection
public import Causalean.Stat.MEstimation.FinitePoisson
public import Causalean.Stat.MEstimation.FinitePoissonConsistency
public import Causalean.Stat.MEstimation.FinitePoissonDerivative
public import Causalean.Stat.MEstimation.FinitePoissonSign
public import Causalean.Stat.MEstimation.InfluenceFunction
public import Causalean.Stat.MEstimation.LogLinearScore
public import Causalean.Stat.MEstimation.SmoothZEstimator
public import Causalean.Stat.MEstimation.SmoothZEstimatorSampleFn
public import Causalean.Stat.MEstimation.ZEstimator
public import Causalean.Stat.MEstimation.ZEstimatorCLT

/-!
# M- and Z-estimation

Asymptotic theory for estimators defined by an estimating equation `Pₙ ψ(θ̂) ≈ 0` or by
maximizing a sample criterion. A consistent estimator whose normalized empirical score is
`o_P(1)` is asymptotically linear with influence function `−V⁻¹ ψ(θ₀, ·)`, where `V` is the
Jacobian of the population score, and is root-n asymptotically normal. Two routes are proved:
one assuming stochastic equicontinuity of the score process (covering nonsmooth scores), and one
for observationwise smooth scores that assumes neither equicontinuity nor a rate. Consistency can
be derived from a uniform law of large numbers and a well-separated optimum.

## Contents

* `InfluenceFunction`, `ZEstimator` — the influence-function predicate and the regularity bundle
  `ZEstimatorRegularity`.
* `EmpiricalExpansion`, `ZEstimatorCLT` — the local stochastic expansion; `zEstimator_asymLinear`
  and `zEstimator_tendsto_normal` under stochastic equicontinuity.
* `SmoothZEstimator`, `SmoothZEstimatorSampleFn` — `zEstimator_asymLinear_of_smoothScore`,
  `zEstimator_tendsto_normal_of_smoothScore`, and their versions for estimators that are functions
  of the sample vector.
* `ExtremumConsistency` — `zEstimator_asymLinear_of_extremum` and relatives, with consistency
  derived from Glivenko–Cantelli and well-separation inputs.
* `ArgmaxStability` — exact maximizers converge under uniform convergence on a common compact set
  with a unique limiting maximizer.
* `FiniteModelSelection` — `finite_penalized_argmin_consistent`: penalized selection among
  finitely many models picks a population minimizer with probability tending to one.
* `FinitePoisson`, `FinitePoissonConsistency`, `FinitePoissonDerivative`, `FinitePoissonSign` —
  the finite Poisson pseudo-likelihood with a linear index: existence and uniqueness of the
  maximizer, its convergence and continuity in the cell means, a one-cell derivative, and a sign
  characterization of one coefficient.
* `LogLinearScore` — the Poisson log-link score derivative is Lipschitz on balls but not globally.

This file only gathers the modules above.
-/
