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

/-! # Cross-Fitted Double Machine Learning

This barrel exports the estimator definitions, oracle linearization, feasible
DML transfer, empirical-Jacobian consistency, and solved feasible DML2 results.
The main results `feasibleCrossFitLinearDML_isAsymLinear` and
`feasibleCrossFitLinearDML_tendstoStandardNormal` derive the reference
influence-function expansion and true-standard-deviation `N(0,1)` limit from
foldwise nuisance and coefficient rates. -/
