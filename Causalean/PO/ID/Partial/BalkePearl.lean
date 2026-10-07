/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.PO.ID.Partial.BalkePearl.ClosedFormAttainment
public import Causalean.PO.ID.Partial.BalkePearl.Sharp

/-!
# Balke–Pearl bounds for a binary instrument

Sharp bounds on the average treatment effect with a binary instrument, binary treatment and
binary outcome. Under consistency, exclusion, independence of the instrument from the potential
treatments and outcomes, and positive probability of both instrument values, the average
treatment effect is the value of a linear objective at some distribution over the 16 latent
response types that reproduces the observed cell probabilities, so it lies between the minimum
and maximum of that linear program. Conversely every feasible distribution is realized by a
potential-outcome model with the same observed data, and the closed-form Balke–Pearl endpoints,
computed from the observed cell probabilities alone, equal that minimum and maximum. The
closed-form interval therefore cannot be narrowed without further assumptions.

## Main definitions

* `POBalkePearlSystem`, `BaseAssumptions` — the binary instrument design and its assumptions.
* `BPFeasible`, `BPObjective`, `BPIdentifiedInterval` — the linear program over latent
  response-type tables and its set of objective values.
* `bpLower`, `bpUpper` — the closed-form endpoints, each the extreme of eight expressions.

## Main results

* `ATE_mem_BPIdentifiedInterval`, `ATE_mem_Icc_csInf_csSup` — the average treatment effect lies
  in the identified set, hence between its infimum and supremum.
* `ATE_mem_Icc_bpLower_bpUpper` — it lies between the closed-form endpoints.
* `balkePearl_sharp` — every feasible table arises from a model satisfying the assumptions with
  the same observed cell probabilities and average treatment effect equal to its objective value.
* `bpLower_bpUpper_eq_csInf_csSup` — the closed-form endpoints are the infimum and supremum of
  the identified set.

This file only gathers the `Sharp` and `ClosedFormAttainment` modules and what they depend on.
-/
