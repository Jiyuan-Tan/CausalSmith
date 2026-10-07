/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variable-intensity instrumental variables

A directed-pair Wald specialization of the Angrist--Imbens causal-response
algebra for finite ordered treatment intensities: one directed instrument
contrast identifies an average causal response over the treatment-intensity
margins crossed by that contrast. The exported 2SLS objects remain interfaces;
this barrel does not claim the paper's general population 2SLS theorem.
-/

module
public import Causalean.PO.ID.Exact.VariableIntensityIV.VariableIntensity.Basic
public import Causalean.PO.ID.Exact.VariableIntensityIV.VariableIntensity.Identification
public import Causalean.PO.ID.Exact.VariableIntensityIV.VariableIntensity.SpecialCases

/-!
# Instrumental variables with an ordered treatment: the average causal response

For a treatment with ordered levels 0, …, J and two instrument values z₀ and z₁, the Wald ratio
(E[Y | Z = z₁] − E[Y | Z = z₀]) / (E[D | Z = z₁] − E[D | Z = z₀]) equals the Angrist–Imbens
average causal response: a weighted average over margins j of the mean effect of moving from
level j to j + 1 among units whose treatment crosses that margin when the instrument moves from
z₀ to z₁, with weights proportional to the crossing probabilities. The assumptions are
consistency, independence of the instrument from the potential treatments and outcomes,
almost-sure monotonicity D(z₀) ≤ D(z₁), a positive first stage, integrable potential outcomes,
and positive probability of both instrument values. The result concerns one pair of instrument
values; it is not a characterization of two-stage least squares with a multivalued instrument.

## Contents

* `VariableIntensity.Basic` — the system `VariableIntensityIVSystem`, crossing events and
  weights, `wald`, `averageCausalResponse`, and the assumptions `ValidContrastAssumptions`.
* `VariableIntensity.Identification` — `firstStage_eq_sum_crossingProb`,
  `reducedForm_eq_sum_crossingEffects` and the main theorem
  `directedPairWald_eq_averageCausalResponse`.
* `VariableIntensity.SpecialCases` — with a single margin the Wald ratio is the local average
  treatment effect (`wald_eq_late_of_binaryIntensity`); with a common response τ at every margin
  it equals τ (`wald_eq_constantResponse`); `wald_eq_marginResponseAverage`; and the record
  `LinearScoreMomentSpec` for a linear-score moment ratio, a definition without an
  identification theorem here.

This file only gathers the modules above.
-/
