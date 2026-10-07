/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.LAN.Convolution

/-!
# Local asymptotic normality

Local asymptotic normality (LAN) and the scalar Hájek–Le Cam convolution theorem. A sequence of
local experiments indexed by a finite-dimensional direction h is LAN when its log likelihood
ratio equals a linear term in a central sequence minus half a quadratic information form, up to
a remainder vanishing in probability, with the central sequence asymptotically centered Gaussian.
A dominated i.i.d. model that is differentiable in quadratic mean is LAN, with the normalized
score sum as central sequence and the score second-moment form as information. In a LAN
experiment, if a real-valued estimator is regular (its centered and rescaled law has one limit
under every local alternative) and the derivative of its target is represented by a canonical
gradient, then the limit law is a centered Gaussian with variance equal to the squared norm of
the gradient, convolved with some probability law; if the limit has a finite second moment, its
variance is at least that squared norm.

## Main results

* `iidDQM_implies_LAN` — an i.i.d. model differentiable in quadratic mean is LAN.
* `regular_convolution_limit` — the limit law of a regular scalar estimator is the efficient
  Gaussian law convolved with a residual probability law.
* `regular_asymptoticVariance_ge_gradientNormSq` — the asymptotic variance of a regular estimator
  is at least the squared norm of the canonical gradient.

The definitions `LocalExperiment`, `IsLAN`, `IsRegularEstimator` and `CanonicalGradientPairing`
and all proofs are in the modules under `LAN/Convolution`.
-/
