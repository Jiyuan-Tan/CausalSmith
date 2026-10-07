/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Quantile.MarkedSubsampleEmpiricalCDF.Basic
public import Causalean.Stat.Quantile.MarkedSubsampleEmpiricalCDF.ConditionalLaw
public import Causalean.Stat.Quantile.MarkedSubsampleEmpiricalCDF.Measurability
public import Causalean.Stat.Quantile.MarkedSubsampleEmpiricalCDF.TailLift

/-!
# Empirical CDF of a randomly selected subsample

Uniform empirical-CDF confidence bands for one arm of an i.i.d. sample of marked observations
`(Dᵢ, Yᵢ)` with a Boolean mark, where only the observations with `Dᵢ = a` are kept and the
retained sample size is random. Conditional on the full vector of marks, the retained outcomes,
taken in their original order, are i.i.d. from the conditional law of `Y` given `D = a`. Hence any
fixed-sample-size bound on the uniform deviation of the empirical CDF carries over to the selected
subsample with a radius depending on the realized count `m`; in particular, with probability at
least `1 − α/2` the selected arm is empty or its empirical CDF is uniformly within
`√(32 log(16 (m+1)/α) / m)` of the truth.

## Main definitions and results

* `Basic` — `selectedCount`, `selectedOutcomes`, `selectedEmpiricalCDF`, `uniformCDFDeviation`,
  and the bad event `selectedCDFBadEvent`.
* `ConditionalLaw` — `MarkedIID`, `BooleanMarkFactorization`;
  `MarkedIID.selectedOutcomes_conditionalLaw`, the conditional i.i.d. law given the mark vector.
* `Measurability` — `measurable_uniformCDFDeviation`: the supremum over thresholds is measurable.
* `TailLift` — `conditionalMarkedSubsample_empiricalCDF_tail` (transfer of a fixed-size tail
  bound, which is a hypothesis; with `dkwRadius` it gives the sharper radius
  `√(log(4/α)/(2m))` from a supplied fixed-size DKW bound) and
  `conditionalMarkedSubsample_vcMcDiarmidRadius` (the unconditional band above).
-/
