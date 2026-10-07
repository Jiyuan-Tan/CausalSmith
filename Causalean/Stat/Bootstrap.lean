/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Bootstrap.AsymptoticLinear
public import Causalean.Stat.Bootstrap.EfronResampling
public import Causalean.Stat.Bootstrap.GaussianMultiplier
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans
public import Causalean.Stat.Bootstrap.SmoothZEstimator

/-! # The bootstrap

Validity of Efron's nonparametric bootstrap for asymptotically linear estimators. The bootstrap
is formalized as an actual conditional law — n draws with replacement from the observed sample —
and the main theorems state that the conditional bootstrap law of √n(θ̂* − θ̂) and the sampling
law of √n(θ̂ − θ) approach the same centred Gaussian in Kolmogorov distance, in probability, so
that percentile and basic bootstrap confidence intervals have asymptotic coverage 1 − α. This is
proved for sample means, smooth functions of vector means (delta method), and smooth
finite-dimensional Z-estimators, including OLS and feasible GMM.

## Contents

* `Bootstrap.EfronResampling` — the empirical measure, the resampling law, its exact finite
  representation and conditional moments, and measurable bootstrap quantiles.
* `Bootstrap.AsymptoticLinear` — the hypothesis bundle `BootstrapAsymLinear`, bootstrap
  consistency `BootstrapAsymLinear.consistent`, and interval coverage `percentileCI_coverage`,
  `basicCI_coverage`.
* `Bootstrap.SmoothFunctionOfMeans` — bootstrap weak law, conditional tightness and delta-method
  linearization; `BootstrapAsymLinear.smoothFunctionOfMeans`, `BootstrapAsymLinear.ratioOfMeans`.
* `Bootstrap.SmoothZEstimator` — `BootstrapAsymLinear.zEstimator`, with OLS and feasible-GMM
  instances; for OLS the hypotheses reduce to moment and Gram-matrix conditions
  (`olsContrast_percentileCI_coverage_of_moments`).
* `Bootstrap.GaussianMultiplier` — `multiplierBootstrap_law`: for fixed data, the Gaussian
  multiplier bootstrap statistic is exactly centred Gaussian with the sample variance; its
  consistency is not proved.
-/
