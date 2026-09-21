/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.ML.Binary
public import Causalean.ML.CausalApplication
public import Causalean.ML.Core
public import Causalean.ML.Kernel
public import Causalean.ML.Lasso
public import Causalean.ML.Linear
public import Causalean.ML.Margin
public import Causalean.ML.NeuralNet
public import Causalean.ML.PartitionPredictor
public import Causalean.ML.Surrogate

/-! # `Causalean.ML` — machine-learning library

This roll-up collects generic risk, minimizer, and rate abstractions alongside
method-specific developments for regression and classification. `Predictor`,
`HypothesisClass`, and `Bridge` provide a common vocabulary when predictions and observations
have the same type. Most concrete learner families retain their own objectives and optimality
conditions, and only selected results currently connect them to that generic vocabulary:

* `Linear`  — least squares, ridge regression, and L²-ball linear ERM rates, including
  series/sieve learners via `FeatureMap`;
* `Ridge.Rate` — a root-n estimation-rate statement for ridge regression;
* `Lasso`   — L¹-regularized least squares, soft-thresholding, and Rademacher-rate results;
* `Binary`  — logistic losses, logistic regression, Fisher consistency, and rates;
* `Surrogate` — proper and strictly proper binary losses with population minimizers;
* `PartitionPredictor` — finite-partition predictors and fixed-average ensembles;
* `NeuralNet` — feedforward composition class;
* `Kernel`  — RKHS interfaces, kernel ridge regression, a representer theorem, and an
  RKHS-ball Rademacher-complexity bound;
* `Margin`  — Lipschitz margin-surrogate classification rates for linear classifiers.

The causal application layer is `Causalean.ML.CausalApplication`. It supplies abstract
conditional-mean bridges, nuisance packaging, and DML rate assembly, but does not yet connect a
concrete learner or proved learner rate to those causal endpoints. This roll-up imports that
layer; import individual learner modules directly for the causal-free supervised-learning core.
-/
