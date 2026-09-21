/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATE.DML.AsymptoticNormality

/-! # Double Machine Learning for ATE

This roll-up exports `dmlEstimator`, the one-shot sample-split augmented
inverse-probability weighted estimator for the back-door average treatment
effect. Its main linearity interface is `dml_ATE_isAsymLinear_of_goodSet`,
which connects the estimator to the AIPW influence function under overlap,
second-moment, sample-split, and high-probability nuisance-rate conditions.
It also exports `dml_ATE_tendstoNormal`, the fold-scaled normal-limit result. -/
