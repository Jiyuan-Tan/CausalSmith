/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.ProbabilityTransfer
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcessHighProbability

/-!
# Good-set bounds for sample-split score sums

Two probability tools used when nuisance estimators are well behaved only on events whose
probability tends to one. First, if two random sequences agree on such events and one is o_p(r_n),
so is the other. Second, for random score functions fitted on the training part of a sample
split, square-integrable on the good events and with L² norm tending to zero in probability, the
centered sum over the evaluation fold divided by the square root of the fold size is o_p(1); this
holds for a single split and for each fold of a K-fold split, with almost-sure
square-integrability as a special case.

## Main results

* `isLittleOp_of_isLittleOp_on_highProbEvent` — transfer of a stochastic order bound between
  sequences that agree on high-probability events (`Stat/Limit/ProbabilityTransfer`).
* `foldB_centered_sum_isLittleOp_one_of_memLp_on_highProbEvent`,
  `KFoldSplit.fold_centered_sum_isLittleOp_one_of_memLp_on_highProbEvent` — the centered
  fold-sum bounds (`Stat/SampleSplit/FoldBEmpiricalProcessHighProbability`).

This file only gathers the two `Stat` modules above for double-machine-learning developments.
-/
