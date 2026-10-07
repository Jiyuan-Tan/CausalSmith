/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Density.QFactor.TianRecovery

/-! # Tian's district factorization and recovery of c-factors

The density-level form of Tian's c-component (district) factorization. The chain-rule density of
the observed variables regroups as a product of one district density per c-component, where a
district density is the product of the conditional densities p(v | predecessors of v) over the
nodes v of that district. For models with finitely many values per variable and positive
observational probabilities, the district densities of the post-intervention ancestral law are
expressed through the causal mechanisms, and the recursive c-factor extraction of the ID
algorithm is shown to return the correct masses.

## Main definitions

* `tianPrefixStepDensity`, `tianDistrictDensity`, `tianDensityProduct` — the one-node
  conditional density, the district density, and the full chain-rule density of a law.
* `KernelObsCondIndepOn`, `KernelGlobalMarkovOn` — conditional independence of coordinate
  blocks, and the global Markov property of a law with respect to a graph.

## Main results

* `prod_tianDistrictDensity_eq_tianDensityProduct` — the chain-rule density is the product of
  the district densities over all c-components.
* `identifyMassRec_qLocalMass` — along a recursive c-factor reachability certificate, the
  extraction recursion returns the target district's mass from the source district's mass.
* `tianDistrictDensity_eq_mechCFactor_doModel` — for a c-component S of the original graph, the
  S-district density of the post-intervention ancestral law is the mechanism c-factor Q[S].
* `tianDistrictDensity_eq_qLocalMass_div_jointRef_district` — for any district of the
  post-intervention ancestral graph, its density is its local mass over its reference mass.
-/
