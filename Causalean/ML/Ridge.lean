/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Ridge.ClosedForm
public import Causalean.ML.Ridge.Finite
public import Causalean.ML.Ridge.Population
public import Causalean.ML.Ridge.Rate

/-!
# Ridge regression

Ridge regression in a finite feature basis: penalized least squares with penalty λ‖β‖², in the
sample and in the population. For λ > 0 the matrix XᵀX + λI is positive definite, so
β̂ = (XᵀX + λI)⁻¹Xᵀy is the unique solution of the ridge normal equations with no rank condition
on X, and for λ ≥ 0 any solution of the normal equations minimizes the penalized objective; the
same holds for the population objective. For a fixed λ > 0 and an i.i.d. sample, the sample ridge
predictor converges in L²(P) at rate n^{-1/2} to the population ridge predictor, given finite
fourth moments of the features and square-integrable scores. The limit is the penalized
pseudo-true linear predictor, not in general the conditional mean.

## Contents

* `Finite` — `ridgeObjective` and `ridge_is_regularized_squaredLoss_ERM_of_normalEq` (a solution
  of the normal equations minimizes the penalized sum of squares).
* `ClosedForm` — `ridgeCoef`, `ridgeGram_posDef`, `ridgeCoef_normalEq`, `ridgeCoef_unique`.
* `Population` — `populationRidgeObjective`, the population normal equations `IsPopulationRidge`,
  and `populationRidge_minimizes`.
* `Rate` — the sample estimator `sampleRidgeCoef` and the root-n theorem `ridge_achievesL2Rate`.
-/
