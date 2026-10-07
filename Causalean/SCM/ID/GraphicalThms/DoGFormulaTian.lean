/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.DoGFormulaTian.Recovery

/-! # Tian's c-component factorization of a post-intervention density

The density of the law of the ancestors of the outcome after an intervention do(X) factorizes as
a product of one factor per c-component (district) of the post-intervention ancestral graph,
each factor being the product of the conditional densities p(v | predecessors of v) over the
nodes v of the district. The factorization is first proved for an arbitrary finite law dominated
by a product reference measure on the observed nodes of a graph, and then applied to the
post-intervention ancestral marginal of a structural causal model. For finite-valued models with
positive observational probabilities, each district factor reachable by the c-factor recursion
is moreover recovered from the observational law. These are the density identities behind
soundness of the ID algorithm.

## Main results

* `rnDeriv_eq_tianDensityProduct` — chain rule: the density of a dominated finite law is the
  product of its one-node conditional densities along the topological order.
* `markov_tian_cfactorization_density` — that density is the product of the district densities.
* `doObsKernelAncestralMarginal_globalMarkovOn` — the post-intervention ancestral marginal is
  globally Markov with respect to the ancestral graph.
* `doObsKernelAncestralMarginal_tian_cfactorization_density` — the factorization for the
  post-intervention ancestral marginal, assuming it is dominated by the product reference.
* `doAncestralDistrictDensity_recovered_from_obs` — a factor-reachable district density of the
  post-intervention law is determined by the observational law.
-/
