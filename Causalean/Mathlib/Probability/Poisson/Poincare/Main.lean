/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.Poisson.Poincare.Tensorization

/-!
# The Poisson Poincaré inequality

If N is Poisson with rate λ and both f(N) and the increment f(N + 1) − f(N) are
square-integrable, then Var f(N) ≤ λ·E[(f(N + 1) − f(N))²]. For a vector of independent Poisson
counts with rates λ_i and a statistic F of the vector, Var F ≤ Σ_i λ_i·E[(D_i F)²], where D_i F
is the change in F when coordinate i is increased by one. The multivariate form follows from the
scalar one through the Efron–Stein tensorization of variance over product measures, which is
proved for arbitrary finite products of probability laws.

## Main results

* `poisson_addOne_poincare`, `poisson_addOne_poincare_tsum` — the scalar inequality, as an
  integral and as a series.
* `variance_pi_le_sum_integral_coordinateVariance` — the variance of a function of independent
  coordinates is at most the sum of expected conditional variances in each coordinate.
* `poissonPi_addOne_poincare` — the inequality for independent Poisson coordinates.
* `nestedPairedPoisson_addOne_poincare` — the same for a doubly indexed array of pairs of
  independent Poisson counts.

This file only gathers `Poincare.Tensorization`, which brings the scalar inequality and its
series and truncation foundations with it.
-/

public section
