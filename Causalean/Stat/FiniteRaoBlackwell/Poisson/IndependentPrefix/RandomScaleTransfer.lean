/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Basic
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Failure
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Main
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Risk

/-!
# Random-scale minimax transfer for unequal Poisson pools

This roll-up module exports ordered retention for two unequal marked-Poisson pools with a
shared random scale, prior-predictive count-failure bounds, bounded-loss decision transfer,
and the resulting fuzzy-prior minimax lower-bound composition.  It reuses the fixed iid pool
space and exact product law from the independent Poisson-prefix substrate.
-/
