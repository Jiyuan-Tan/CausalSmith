/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Bootstrap.AsymptoticLinear.Basic
public import Causalean.Stat.Bootstrap.AsymptoticLinear.Coverage
public import Causalean.Stat.Bootstrap.AsymptoticLinear.LimitLemmas
public import Causalean.Stat.Bootstrap.AsymptoticLinear.Main
public import Causalean.Stat.Bootstrap.AsymptoticLinear.SampleMean

/-! # Bootstrap validity for asymptotically linear estimators

The general bootstrap validity theorem. An estimator θ̂ of θ from an iid sample is bootstrap
asymptotically linear with influence function φ (mean zero, variance σ² ∈ (0, ∞)) when
√n(θ̂ − θ) equals n^(−1/2) Σ φ(Xᵢ) up to a remainder vanishing in probability, and the same
expansion holds for the resampled estimator around θ̂, conditionally on the data, with a
remainder vanishing in conditional probability. Under this hypothesis the sampling law and the
conditional bootstrap law both converge to N(0, σ²), the bootstrap is consistent in Kolmogorov
distance, bootstrap quantiles converge to Gaussian quantiles, and the percentile and basic
bootstrap confidence intervals cover θ with probability tending to 1 − α.

## Main definitions

* `BootstrapAsymLinear` — the sampling and conditional bootstrap linearization hypotheses.
* `percentileCI`, `basicCI`, `bootstrapQuantile` — the intervals and the conditional quantile.

## Main results

* `BootstrapAsymLinear.sampling_tendsto_gaussian`, `BootstrapAsymLinear.bootstrap_tendsto_gaussian`
  — both laws converge to the centred Gaussian with variance E[φ²].
* `BootstrapAsymLinear.consistent` — the two laws are close in Kolmogorov distance, in
  probability.
* `BootstrapAsymLinear.quantile_tendsto` — convergence of bootstrap quantiles.
* `BootstrapAsymLinear.percentileCI_coverage`, `BootstrapAsymLinear.basicCI_coverage` —
  asymptotic coverage 1 − α for every α in (0, 1).
* `BootstrapAsymLinear.sampleMean` — the sample mean of a square-integrable observation with
  positive variance satisfies the hypothesis, with both remainders identically zero.
-/
