/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EPPerN

/-!
# The empirical-process inequality for the primal NPIV estimator

A weak-norm excess bound for the Tikhonov-regularized adversarial NPIV estimator ĥ_n that holds
simultaneously over all sample sizes. Conditional on the localized-complexity hypotheses at every
sample size, for each ζ in (0, 1) there is an event of probability at least 1 − ζ on which, for
every n with a nonempty estimation fold,

    ‖T(ĥ_n − h₀)‖² − ‖T(h*_λ − h₀)‖² ≤ λ·(‖h*_λ‖²_n − ‖ĥ_n‖²_n) + envelope_n,

where ‖·‖_n is the empirical second moment on the estimation fold and the envelope is a
combination of δ_n times the critical radii of the three localized classes and concentration
slack terms with log(4·2^{n+1}/ζ). The proof uses optimality of ĥ_n against the population
Tikhonov solution to cancel the empirical objective excess.

## Main results (all in `EPPerN`)

* `population_inner_eq_weakNorm_sq` — under the closedness condition, the critic-dependent
  part of the population objective at the witnessing critic equals ‖T(h − h₀)‖².
* `ep_per_n_inequality_from_deviations` — the deterministic step from an objective-level
  deviation bound to the weak-norm inequality at one sample point.
* `ep_inequality_from_localized` — the high-probability inequality displayed above.
-/

public section
