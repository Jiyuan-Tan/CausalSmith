/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.Approximation
public import Causalean.Stat.Nonparametric.HigherOrderInfluence
public import Causalean.Stat.Nonparametric.LinearSmoother
public import Causalean.Stat.Nonparametric.LocalPoly
public import Causalean.Stat.Nonparametric.SeriesSieve

/-!
# Nonparametric methods

Top barrel for reusable nonparametric statistical methods: approximation theory, fixed-weight linear
smoothers, local-polynomial and series/sieve estimators, and higher-order influence function (HOIF) projection-kernel risk building blocks.
Organized into the following reusable layers:

* `LinearSmoother` — deterministic bias and generic variance bounds for fixed-weight linear
  smoothers with uncorrelated heteroskedastic errors whose coordinate variances are uniformly
  bounded, shared by local-polynomial and series/sieve estimators.
* `Approximation` — deterministic approximation-theory bias primitives (Hölder–Taylor, kernel).
* `LocalPoly` — the degree-`p` local-polynomial estimator substrate (weights, design positive
  definiteness, bias, variance, rate, estimator risk).
* `SeriesSieve` — the series/sieve `L²` approximation-and-prediction substrate.
* `HigherOrderInfluence` — HOIF projection-kernel U-statistic variance and risk algebra.
-/
