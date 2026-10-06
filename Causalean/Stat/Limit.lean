/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.ContinuousMapping
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.Limit.ConvergenceCompatibility
public import Causalean.Stat.Limit.ConvergenceVec
public import Causalean.Stat.Limit.ExtendedContinuousMapping
public import Causalean.Stat.Limit.Modes
public import Causalean.Stat.Limit.ProbabilityTransfer
public import Causalean.Stat.Limit.QuadraticForm
public import Causalean.Stat.Limit.Slutsky
public import Causalean.Stat.Limit.StochasticOrder
public import Causalean.Stat.Limit.StochasticOrderEnvelope
public import Causalean.Stat.Limit.WLLN

/-!
Modes of convergence for random sequences, and the calculus for manipulating them.

Provides the hub predicates for convergence in probability and in distribution, the
stochastic-order notation `O_p` and `o_p`, and the rules that let one limit statement be
rewritten into another: continuous mapping, Slutsky's theorem, the weak law of large numbers,
quadratic-form limits, compatibility between row-wise and fixed-space convergence wrappers,
and transfer of stochastic bounds across high-probability events under a fixed measure.

This is vocabulary, not lower-bound machinery. Minimax lower bounds — van Trees, Le Cam,
Fano, Assouad — live in `Causalean.Stat.Minimax`.
-/
