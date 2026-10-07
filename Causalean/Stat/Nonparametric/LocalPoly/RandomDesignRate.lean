/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.Basic
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.ConditionalRisk
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.GoodDesign
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.MomentConcentration
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.PopulationMoment
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.Rate
public import Causalean.Stat.Nonparametric.LocalPoly.RandomDesignRate.Risk

/-!
# Random-design risk and rate of the local-polynomial estimator in dimension one

For independent pairs `(X_i, Y_i)` with a design density bounded above and below by positive
constants near an interior point `x₀`, the degree-`p` local-polynomial estimator of the
regression function at `x₀`, clipped to `[−M, M]` with `|m(x₀)| ≤ M`, has an unconditional
mean-squared-error bound and attains the rate `N^(−2β/(2β+1))` over a local Hölder class of
smoothness `β`. No condition on the realized design is assumed: the event on which the design
is well conditioned is constructed and its failure probability is bounded.

## Contents

* `RandomDesignRate/Basic` — `KernelDesign`, `InteriorDesign`, the moment matrices and
  `momentEvent`, the constants, `HolderRegression`, `rawIntercept`, `clippedIntercept`.
* `RandomDesignRate/MomentConcentration` — `localPoly_moment_entrywise_bernstein`,
  `localPoly_moment_simultaneous_probability`.
* `RandomDesignRate/PopulationMoment` — `populationMoment_eq_shape`, `shapeMoment_posDef`,
  `shape_inverse_rows`, `designTolerance_spec`.
* `RandomDesignRate/GoodDesign` — `localPoly_leverage_on_momentEvent`,
  `rawIntercept_eq_wls_intercept`.
* `RandomDesignRate/ConditionalRisk` — `windowed_localPoly_bias`,
  `localPoly_fibre_mse_of_designBounds`.
* `RandomDesignRate/Risk` — `localPoly_clipped_mse_unconditional`.
* `RandomDesignRate/Rate` — `localPoly_clipped_pointwise_rate`.
-/
