/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Density.ChainRuleDensity.RadonNikodym

/-! # Chain rule for the observational density of a structural causal model

The joint density of the observed variables of a structural causal model, with respect to a
product of σ-finite reference measures, factorizes along the topological order as the product of
one-node conditional densities p(v_k | v_1, …, v_{k−1}). The statement is at the level of
Radon–Nikodym derivatives, so it covers continuous as well as discrete variables. It is
conditional on two hypotheses: the observational law is dominated by the joint reference measure,
and at every step the conditional law of the next variable given its predecessors is dominated
by that variable's reference measure with a jointly measurable density (the stepwise fibre
Radon–Nikodym condition).

## Main definitions

* `obsStepCondDensity` — the one-node conditional density factor.
* `qFactorDensityProduct`, `prefixDensityProduct` — the product of these factors over all
  observed nodes, and over an initial segment of the order.
* `ObsStepFiberRN` — the stepwise domination and measurability hypothesis.

## Main results

* `qFactorProduct_rnDeriv_eq_qFactorDensityProduct` — the Radon–Nikodym derivative of the
  sequentially composed observational kernel is the product of the stepwise derivatives.
* `obsDensity_eq_qFactorDensityProduct` — the observational density equals the product of
  one-node conditional densities, almost everywhere for the joint reference measure.
-/
