/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.ML.CausalApplication.AIPWExample
public import Causalean.ML.CausalApplication.RateAssembly

/-! # `Causalean.ML.CausalApplication` — causal applications of ML learners

This roll-up is the causal-application layer for `Causalean.ML`, kept separate
from the causal-free core. `RegressionBridge` identifies functions satisfying a
residual-orthogonality moment condition with conditional expectations, while `Nuisance`
packages supplied candidate functions for AIPW. `AIPWExample` transports exact
almost-everywhere nuisance equalities to ATE mean-zero identification, and `RateAssembly`
combines abstract quarter-rate error hypotheses into the corresponding DML rate conditions.
This layer does not yet connect a concrete learner or its proved rate to those hypotheses.
-/
