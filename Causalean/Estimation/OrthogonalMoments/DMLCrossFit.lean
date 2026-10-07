/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# K-fold cross-fitted Chernozhukov DML

K-fold version of the one-shot DML asymptotic-linearity interfaces from
`Estimation/OrthogonalMoments/DMLChernozhukov.lean`.  Each evaluation fold k uses a
nuisance estimator `η̂^{(-k)}` trained on the complement; the K fold scores
are averaged to form the final estimator.

Reference: Chernozhukov et al. (2018), §3.2 (DML2).
-/

module
public import Causalean.Estimation.OrthogonalMoments.DMLCrossFit.JacobianConsistency

/-!
# Cross-fitted double machine learning

K-fold cross-fitted double machine learning (the DML2 estimator of Chernozhukov et al. 2018) for
a scalar parameter defined by a score that is affine in the parameter. Each fold is evaluated
with nuisance functions fitted on the other folds, and the estimator solves the fold-averaged
empirical moment equation. Assuming a mean-zero, square-integrable score at the truth, a
product-form bound on the population moment at a wrong nuisance, and foldwise rates — the score
error vanishing in L², the nuisance error product of order o_p(n^{-1/2}), and the corresponding
rates for the score coefficient — the estimator is asymptotically linear with influence function
−J₀⁻¹·m(η₀, ·, θ₀), and after scaling by the true standard deviation it converges in
distribution to N(0,1). The limit is pointwise in the data law; the measurability and
integrability of the fitted scores are hypotheses.

## Contents

* `Estimator` — `crossFitOneStepOracleDML`, `feasibleLinearDML`, `feasibleCrossFitLinearDML`.
* `Helpers`, `AsymptoticLinearity` — `crossFitOneStepOracleDML_isAsymLinear_of_goodSet`: the
  oracle one-step estimator, which uses the true Jacobian, is asymptotically linear.
* `Feasible` — the single-split feasible estimator: `feasibleLinearDML_isAsymLinear` and the
  normal limit `feasibleLinearDML_tendstoStandardNormal_of_isAsymLinear`.
* `JacobianConsistency` — `crossFitLinearDML_jacobianConsistency` (the fold-averaged empirical
  coefficient is consistent) and the K-fold results `feasibleCrossFitLinearDML_isAsymLinear` and
  `feasibleCrossFitLinearDML_tendstoStandardNormal`.
-/
