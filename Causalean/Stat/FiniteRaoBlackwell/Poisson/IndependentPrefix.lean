/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.Basic
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.ProductPools
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.Risk

/-!
# Independent Poisson-prefix Rao--Blackwell transfer

This roll-up module exports exact laws, capped implementations, conditional averaging, and
depoissonization bounds for independent Poisson prefixes. It includes the unequal two-pool API,
its heterogeneous finite-family extension, and the random-scale two-pool minimax transfer.
-/
