/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Basic
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Linearization
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Main
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Measurability
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.SmoothRemainder
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Tightness
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Uniformization
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.WeakLaw
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.WeakLawVector

/-! # Bootstrap validity for smooth functions of sample means

The bootstrap delta method. For an iid sample, a vector of moment functions m with E‖m(X)‖² < ∞
and a scalar map g that is Fréchet differentiable at μ = E[m(X)], the estimator g of the sample
mean of m is bootstrap asymptotically linear with influence function Dg(μ)(m(X) − μ), provided
that influence function has positive variance. Hence Efron's bootstrap is consistent for it and
the percentile interval has asymptotic coverage 1 − α. Only differentiability at μ is used. The
ratio of two sample means, with nonzero denominator mean, is the worked example.

## Main results

* `bootstrapMean_sub_dataMean_tendsto_zero_ae`, `bootstrapMeanVec_sub_dataMean_tendsto_zero_ae`
  — conditional bootstrap weak law: for almost every data sequence, the resample mean is close
  to the sample mean with conditional probability tending to one (first moment only).
* `bootstrapMean_chebyshev`, `scaledBootstrapMeanDifferenceVec_conditionallyBounded` —
  conditional tightness of the √n-scaled centred bootstrap mean.
* `samplingLinearization_smoothFunctionOfMeans`, `bootstrapLinearization_smoothFunctionOfMeans`
  — the two first-order expansions.
* `BootstrapAsymLinear.smoothFunctionOfMeans` — the estimator is bootstrap asymptotically
  linear; `percentileCI_coverage_smoothFunctionOfMeans` is the coverage corollary.
* `BootstrapAsymLinear.ratioOfMeans` — the ratio-of-means instance.
-/
