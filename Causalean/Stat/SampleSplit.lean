/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
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

/-!
# Sample splitting and cross-fitting

Probabilistic facts behind estimators that fit nuisance functions on one part of an i.i.d. sample
and evaluate on another. For a one-shot split into a training fold A and an evaluation fold B, and
for a K-fold split, the evaluation fold is independent of its training complement. Consequently a
centred evaluation-fold sum of a score estimated on the training fold is `o_P(1)` whenever the
score's L²(P) norm is `o_P(1)`, and its bias term is negligible at the root-n scale when the L²
rate is `o_P(n^(−1/2))` and the split proportion is fixed. On the evaluation fold a fixed
square-integrable statistic obeys a weak law of large numbers and a central limit theorem.

## Contents

* `OneShot`, `KFold` — `OneShotSplit`, `KFoldSplit`, and independence of the folds (`folds_indep`).
* `FoldBEmpiricalProcess` — `foldB_centered_sum_isLittleOp_one`,
  `sqrtFoldB_integral_isLittleOp_one`, and the K-fold versions
  `KFoldSplit.fold_centered_sum_isLittleOp_one`, `KFoldSplit.sqrtFold_integral_isLittleOp_one`.
* `FoldBEmpiricalProcessHighProbability` — the same centred-sum bounds when the score is
  square-integrable only almost surely or on an event of probability tending to one.
* `FoldBWLLN` — `foldB_sampleMean_tendsto_inProb`.
* `PartialFoldCLT` — `clt_normalizedFoldB`; an estimator asymptotically linear on fold B is
  asymptotically normal at rate `√|B|`, and at rate `√n` under a fixed split ratio with the
  corresponding variance inflation (`IsAsymLinear.tendsto_normal_foldB_sqrt_n`).
* `FiniteSelector` — squared-risk bounds for a branch selected among finitely many by an
  independent pilot sample.
* `FiniteCategoryPilot` — Chernoff and union bounds for threshold selection of categories from
  pilot counts (`finiteCategoryPilot_bad_probability`).

This file only gathers the modules above.
-/
