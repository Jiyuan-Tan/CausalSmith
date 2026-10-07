/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.PerSample

/-!
# The empirical-process event for the primal NPIV rate

High-probability control of the empirical process in the convergence-rate proof for the
Tikhonov-regularized adversarial estimator of a nonparametric instrumental-variable (inverse)
problem. At one sample size and one confidence level ζ in (0, 1), and conditional on a bundle of
localized-complexity hypotheses for the candidate class, the critic class and their product and
moment classes (critical radii at most δ, boundedness, realizability of the population Tikhonov
solution, closedness, and a peeling condition), there is an event of probability at least 1 − ζ
on which the population excess of the estimator over the Tikhonov solution — weak-norm error
difference plus λ times strong-norm difference — is at most 50·δ² plus
λ·(10·δ·‖ĥ − h*_λ‖ + 5·δ²). The event is uniform over candidates and critics; the localized
hypotheses are assumed, not derived from entropy conditions here.

## Contents

* `Regime` (also importable as `Core`) — the hypothesis bundles `LocalizedRegimeBundle`,
  `LocalizedRegimes` and `PeelingFloor`.
* `Algebra` — the Young/AM-GM envelope used to absorb cross terms.
* `LocalizedEventsBase`, `LocalizedEventF`, `LocalizedEventH`, `LocalizedEventHF`,
  `LocalizedEventMF` — transport from the product law of the sample to the underlying
  probability space, and the deviation event for critics, candidates, candidate–critic products
  and moment–critic products.
* `PerSample` — `per_sample_empirical_process_event`, the fixed-sample, fixed-confidence event
  above, with deviation term of order sqrt(log(4/ζ)/n).
* `EPMasterEvent`, `EPPerN` (also `EPInequality`), `Regulariser`, `EventAssembly` — the variant
  holding simultaneously over all sample sizes, ending in `ep_inequality_from_localized`.
-/
