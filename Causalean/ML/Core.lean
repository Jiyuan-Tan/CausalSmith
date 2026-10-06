/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Core.Losses
public import Causalean.ML.Core.Hypothesis
public import Causalean.ML.Core.Risk
public import Causalean.ML.Core.ERM
public import Causalean.ML.Core.Bridge
public import Causalean.ML.Core.Convex
public import Causalean.ML.Core.PopulationTarget
public import Causalean.ML.Core.Rate

/-! # `Causalean.ML.Core` — the standalone learning spine

Roll-up of the causal-free machine-learning spine: losses, parametrized
predictors and extensional hypothesis classes, empirical/population risk, the
ERM-minimizer predicates, the parametric↔extensional bridge, the convex-analysis
substrate, and the population-target interface. Concrete methods (linear, ridge,
lasso, logistic, kernel, and neural nets) instantiate these in sibling
directories.
-/

public section
