/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.Estimators.DifferenceInMeans
public import Causalean.Experimentation.DesignBased.Estimators.NeymanVariance

/-!
# Design-based estimators

Entry point for paper-agnostic estimators of finite-population causal estimands and their
randomization properties.

`Estimators.DifferenceInMeans` defines the sample average treatment effect `sateEstimand`, the arm
means `treatedMean` and `controlMean`, the estimator `diffInMeans`, and its
complete-randomization unbiasedness theorem `E_diffInMeans_eq_sate`.
`Estimators.NeymanVariance` supplies the paper-independent finite-population arm variances,
unit-effect variance, and observed separate-arm variance estimator used by downstream exact
variance and coverage results.
-/
