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

/-! `Stat.Bootstrap.SmoothZEstimator` directory barrel: bootstrap validity for smooth-score
Z-estimators — the sampling and conditional linearizations, the `BootstrapAsymLinear` constructor
for a contrast of the coefficient vector, and the OLS and feasible-GMM instances. -/
