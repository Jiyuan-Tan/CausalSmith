/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.Approximation.Holder
public import Causalean.Stat.Nonparametric.Approximation.HolderTaylorMonomial
public import Causalean.Stat.Nonparametric.Approximation.Kernel


/-!
# Deterministic approximation bounds for Hölder functions

Approximation-theoretic estimates behind the bias analysis of nonparametric estimators; nothing
here is random. Convolving a `β`-Hölder function with a kernel of order `p` (the largest integer
strictly below `β`) at bandwidth `h` changes it by at most `(M/p!) ∫|K| · h^β`. A function in a
multivariate Hölder ball is approximated near any centre by an explicit monomial polynomial with a
remainder constant uniform over the ball. A function in a Hölder ball of exponent `γ` on `ℝ^d`
satisfies `c |g(x₀)|^(1 + d/γ) ≤ ∫ |g|` over a cube around `x₀`, an inequality used in two-point
and Assouad lower-bound arguments.

## Main results

* `kernelSmoothingBias_bound` (`Approximation/Kernel`) — the `O(h^β)` bound for the unnormalised
  convolution difference `kernelSmoothingBias` under a kernel of order `p` (`KernelOrder`).
* `holder_taylor_monomial_approx` (`Approximation/HolderTaylorMonomial`) — local monomial
  approximation in the Hölder ball `HolderBallStd`.
* `holder_point_l1_interpolation` (`Approximation/Holder/Interpolation`) — the pointwise-to-L¹
  interpolation inequality.
* `exists_holderBallStd_extension` (`Approximation/Holder/CubeExtension`) — extension of a function
  in the cube Hölder ball to an ambient Hölder ball with a controlled radius.

The one-dimensional Hölder–Taylor remainder bounds these rest on are in
`Causalean.Mathlib.Analysis.Calculus.HolderTaylor`.
-/
