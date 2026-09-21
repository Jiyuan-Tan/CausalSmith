/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.ML.Linear.ClosedForm
public import Causalean.ML.Linear.Finite
public import Causalean.ML.Linear.L2BallRate
public import Causalean.ML.Linear.L2BallSquaredLoss
public import Causalean.ML.Linear.Population
public import Causalean.ML.Ridge

/-! # `Causalean.ML.Linear` — linear least squares and ridge

Roll-up of the linear-in-features regression family: ordinary least squares and
ridge, including finite-sample optimization, closed-form normal-equation
solutions, and population-risk target results. The `FeatureMap` layer makes
polynomial, spline, and Fourier sieve regressions instances of the same
theorems, while the finite OLS files expose the bridge from `empiricalRisk` to
design-matrix objectives. The L²-ball modules provide generic and squared-loss
ERM rates for bounded Euclidean linear predictors.
-/
