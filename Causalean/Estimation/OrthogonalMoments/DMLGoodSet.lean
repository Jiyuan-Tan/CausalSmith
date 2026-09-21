/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.ProbabilityTransfer
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcessHighProbability

/-!
# Compatibility Imports for DML Good-Set Bounds

The generic probability-transfer and centered fold-sum results formerly housed
with DML now live in the `Stat` layer. This module preserves the established
Estimation import path for downstream DML developments.
-/
