/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Quantile.SampleQuantileBahadur.Linearity
public import Causalean.Stat.Quantile.SampleQuantileBahadur.Oscillation
public import Causalean.Stat.Quantile.SampleQuantileBahadur.Rate

/-!
# Bahadur representation of the sample quantile

For an i.i.d. sample from a law whose CDF `F` is continuous near the population `τ`-quantile `q₀`
and differentiable at `q₀` with derivative `f₀ > 0`, where `F(q₀) = τ` and `τ ∈ (0, 1)`, the
sample `τ`-quantile satisfies

    √n (q̂ₙ − q₀) = n^(−1/2) ∑ᵢ (τ − 1{Zᵢ ≤ q₀}) / f₀ + o_P(1).

That is, it is asymptotically linear with influence function `(τ − 1{z ≤ q₀}) / f₀`. The remainder
is proved to vanish, without assuming a Donsker theorem: the argument uses a Chebyshev bound for
increments of the empirical process, a monotone-grid oscillation bound, the root-n rate of the
sample quantile, and an inversion with a Taylor expansion of `F`.

## Main definitions and results

* `SampleQuantileReg` (`Oscillation`) — the regularity conditions above.
* `IIDSample.empProcess_oscillation` (`Oscillation`) — local oscillation of the empirical process
  `√n (F̂ₙ − F)` vanishes in probability.
* `IIDSample.sampleQuantile_rate` (`Rate`) — `√n (q̂ₙ − q₀) = O_P(1)`.
* `IIDSample.sampleQuantile_isAsymLinear` (`Linearity`) — the representation displayed above.
* `IIDSample.sampleQuantile_quantileRegularity` (`Linearity`) — the sample quantile satisfies the
  generic `QuantileRegularity` bundle, so `QuantileRegularity.tendsto_normal` gives its normal
  limit.
-/
