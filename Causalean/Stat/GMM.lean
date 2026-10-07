/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.GMM.AsymptoticNormality
public import Causalean.Stat.GMM.Feasible
public import Causalean.Stat.GMM.HansenJ
public import Causalean.Stat.GMM.ResidualProjection
public import Causalean.Stat.GMM.Setup
public import Causalean.Stat.GMM.SmoothFeasible
public import Causalean.Stat.GMM.SmoothFeasibleGeneral
public import Causalean.Stat.GMM.SmoothFeasibleGeneralRate
public import Causalean.Stat.GMM.SmoothMoment
public import Causalean.Stat.GMM.VarianceAlgebra
public import Causalean.Stat.GMM.ZEstimator

/-!
# Generalized method of moments

Large-sample theory for GMM estimators of a finite-dimensional parameter identified by moment
conditions `E g(θ₀, Z) = 0` with Jacobian `G`, weight `W` and moment covariance `Cov`. A consistent
estimator that approximately solves the first-order condition is asymptotically linear with
influence function `−(GᵀWG)⁻¹ GᵀW g(θ₀, z)` and is root-n asymptotically normal with the sandwich
covariance; this is proved for the population-weight (oracle) condition and for the feasible one
with estimated Jacobian and weight, under either stochastic equicontinuity of the moments or
observationwise smooth moments. The sandwich variance dominates the efficient variance
`(Gᵀ Cov⁻¹ G)⁻¹` in the positive-semidefinite order, and Hansen's J statistic of the efficient
feasible estimator converges in distribution to chi-squared with (number of moments − number of
parameters) degrees of freedom.

## Contents

* `Setup` — `GMMProblem`, `EfficientGMMProblem`, the score, influence function and asymptotic
  variance; `EfficientGMMProblem.efficiency`.
* `VarianceAlgebra` — bread and sandwich operators; `gmm_efficiency`, the covariance lower bound.
* `ZEstimator` — the GMM score as a Z-estimation problem.
* `AsymptoticNormality` — `oracleGMM_asymLinear`, `oracleGMM_tendsto_normal`, and versions with
  consistency derived from extremum-estimator primitives.
* `Feasible` — sample moment, feasible first-order condition, `hansenJStatistic`;
  `feasibleGMM_asymLinear`, `feasibleGMM_tendsto_normal` under stochastic equicontinuity.
* `SmoothMoment`, `SmoothFeasible`, `SmoothFeasibleGeneral`, `SmoothFeasibleGeneralRate` — smooth
  moments: empirical Taylor expansion, the root-n rate, and
  `feasibleGMM_tendsto_normal_of_smoothMoment` for a general limiting weight.
* `ResidualProjection`, `HansenJ` — the whitened residual projection and its Gaussian chi-squared
  law (`gaussian_residualProjection_chiSq`); `hansenJ_tendsto_chiSq`.

All limit theorems take consistency (or primitives implying it), the approximate first-order
condition, and the stated measurability as hypotheses. This file only gathers the modules above.
-/
