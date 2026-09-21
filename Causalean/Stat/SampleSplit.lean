/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sample-split umbrella

Re-exports the per-strategy split structures.  Existing consumers that import
`Causalean.Stat.SampleSplit` continue to work via this umbrella: the original
`OneShotSplit` API now lives in `Causalean.Stat.SampleSplit.OneShot`, and the
K-fold split lives in `Causalean.Stat.SampleSplit.KFold`.
-/

module
public import Causalean.Stat.SampleSplit.FiniteCategoryPilot
public import Causalean.Stat.SampleSplit.FiniteSelector
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcessHighProbability
public import Causalean.Stat.SampleSplit.FoldBWLLN
public import Causalean.Stat.SampleSplit.KFold
public import Causalean.Stat.SampleSplit.OneShot
public import Causalean.Stat.SampleSplit.PartialFoldCLT

/-! # Sample-Splitting Umbrella

This module is the public import point for sample-splitting infrastructure used
by cross-fitting and fold-based estimation arguments. It re-exports the one-shot
split API from `Causalean.Stat.SampleSplit.OneShot` and the K-fold split API
from `Causalean.Stat.SampleSplit.KFold`, preserving a single stable import for
downstream statistical modules.
-/
