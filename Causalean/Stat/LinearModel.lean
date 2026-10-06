/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.FWLInstanceL2
public import Causalean.Stat.LinearModel.GaussMarkov
public import Causalean.Stat.LinearModel.OLSAsymptotics.HC1Wald

/-!
Linear-model tools for the L² Frisch–Waugh–Lovell specialization, algebraic
variance orderings for least-squares weights, and robust OLS asymptotics and
inference. The variance-ordering results do not themselves establish
unbiasedness because they do not assume a linear mean model.
-/
