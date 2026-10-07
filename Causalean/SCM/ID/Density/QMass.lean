/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Density.QMass.Prefix

/-! # Local q-masses and the c-component factorization of the observational law

For a structural causal model with finitely many values per variable, the local q-mass of a set
S of observed nodes at an observed assignment is the probability, under the product law of the
latent noises, that every structural equation in S produces its assigned value given the
assigned values of its parents. This is the discrete form of Tian's c-factor Q[S]. The main
theorem is the c-component factorization: for a set P of observed nodes closed under observed
parents, the probability of an assignment of P equals the product, over the c-components C of
the graph, of the local q-mass of C ∩ P. The proof uses that distinct c-components depend on
disjoint, hence independent, blocks of latent noises.

## Contents

* `QMass.Basic` — `qLocalMass`; monotonicity; summing out a childless coordinate
  (`qLocalMass_sum_point_eliminate`); marginalizing onto a parent-closed subset
  (`qLocalMass_marginalize_ancestralClosed`).
* `QMass.LatentBlocks` — the latent coordinates on which each local-consistency event depends
  (`latentBlockIndex`), with the measurability needed for independence across c-components.
* `QMass.Factorization` — `obsKernel_marginal_singleton_eq_prod_qLocalMass`, the factorization.
* `QMass.Prefix` — positivity of the post-intervention ancestral marginal when all
  observational probabilities are positive (`doObsKernelAncestralMarginal_positiveMass`), and a
  telescoping identity for products of successive ratios (`prod_filter_div_telescope`).
-/
