/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.ML.Lasso.Finite
public import Causalean.ML.Lasso.HighProbability
public import Causalean.ML.Lasso.Optimality
public import Causalean.ML.Lasso.OracleInequality
public import Causalean.ML.Lasso.Rate
public import Causalean.ML.Lasso.SquaredLoss
public import Causalean.ML.Lasso.SubGaussian

/-! # `Causalean.ML.Lasso` — L1-regularized least squares

Roll-up of the lasso family: `l1penalty`, `lassoObjective`, convexity of the
finite objective, the scalar soft-thresholding optimality theorem
`softThreshold_isMinOn`, the fixed-design restricted-eigenvalue oracle inequality,
sub-Gaussian score calibration, and the Rademacher-complexity and squared-loss
excess-risk rates for the L¹-ball linear class. The current subtree focuses on
the reusable finite-objective, proximal, and complexity interfaces for
L1-regularized learning.
-/
