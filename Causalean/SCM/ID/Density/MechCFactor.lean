/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Density.MechCFactor.Invariance

/-! # The c-factor Q[S] as an interventional density

Tian's c-factor Q[S] of a set S of observed variables, defined through the causal mechanisms:
the density on S of the law obtained by intervening on every observed variable outside S. For
models with finitely many values per variable, positive observational probabilities, and
reference measures giving every value nonzero mass, this module proves the two facts on which
c-component identification rests: when S is a c-component, Q[S] equals the observational
product of the conditional densities p(v | predecessors of v) over v in S (Tian's Lemma 1), and
Q[S] is unchanged by a further intervention on variables outside S.

## Main definitions

* `mechComplementNames`, `mechDoValues` — the variables outside S to intervene on, and the
  values assigned to them.
* `QmechMeasure`, `mechCFactor` — the interventional law on S and its density.

## Main results

* `QmechMeasure_singleton_eq_qLocalMass`, `mechCFactor_eq_qLocalMass_div_jointRef` — Q[S] at a
  point is the latent-noise mass of the event that every mechanism in S produces its value,
  divided by the reference mass of the point.
* `obsStepCondDensity_eq_component_ratio_div_ref` — each one-node observational conditional
  density is a ratio of two such masses for the node's c-component.
* `cComponentDensityFactor_eq_mechCFactor` — Tian's Lemma 1 for a model without fixed nodes.
* `mechCFactor_fixSet_invariant` — invariance of Q[S] under interventions outside S.
-/
