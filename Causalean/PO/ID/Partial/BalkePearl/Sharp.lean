/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

-/

module
public import Causalean.PO.ID.Partial.BalkePearl.Sharp.Sharpness

/-! # Balke–Pearl sharpness

The Balke–Pearl identified set for the average treatment effect is sharp on the model side: for
a binary instrument, treatment and outcome, every latent response-type table that is feasible
for the Balke–Pearl linear program is the response-type distribution of an actual
potential-outcome model. That model satisfies the base assumptions (consistency, exclusion,
instrument exogeneity, positive instrument probabilities), reproduces the observed cell
probabilities, and has average treatment effect equal to the table's objective value. Hence
every number in the identified set is the average treatment effect of some model that the data
cannot distinguish from the original.

## Contents

* `Sharp.CanonicalModel` — the canonical model: sample space instrument value × response type,
  product of the instrument marginal and the table's discrete measure, with the structural
  evaluator Z → D → Y; consistency and composition consistency (`canonicalPOSystem`,
  `canonicalBP`, `canonical_consistency`).
* `Sharp.Sharpness` — the canonical model satisfies the base assumptions and matches the
  observed cells and objective; `balkePearl_sharp` (every feasible table is realized) and
  `balkePearl_sharp_of_mem` (every point of the identified set is a realized treatment effect).
-/
