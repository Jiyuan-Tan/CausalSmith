/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.GaussMarkov.BLUE
public import Causalean.Stat.LinearModel.GaussMarkov.LeastNorm
public import Causalean.Stat.LinearModel.GaussMarkov.OLS
public import Causalean.Stat.LinearModel.GaussMarkov.QuadForm
public import Causalean.Stat.LinearModel.GaussMarkov.Variance

/-!
Algebraic and probabilistic ingredients used in finite Gauss–Markov arguments.
The modules define covariance quadratic forms and least-squares weights, then
prove variance orderings under design-balance identities. They do not formalize
estimator unbiasedness or the full best-linear-unbiased-estimator theorem.
-/
