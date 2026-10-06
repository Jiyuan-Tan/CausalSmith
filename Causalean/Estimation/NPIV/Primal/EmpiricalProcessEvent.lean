/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.PerSample

/-!
# Assembling `empirical_process_event` from `localized_uniform_deviation`

This umbrella module re-exports the localized empirical-process discharge
for the primal TRAE rate theorem.  The implementation is split by topic:

* `Core` re-exports the localized-regime structures and deterministic setup.
* `Algebra` contains the Young/AM-GM envelope used to absorb cross terms.
* `LocalizedEventsBase` provides the product-law-to-Ω transport shared by the
  class-specific files; `LocalizedEvents` is their aggregate import.
* `LocalizedEventF`, `LocalizedEventH`, `LocalizedEventHF`, and
  `LocalizedEventMF` specialize that transport to critics, candidates,
  candidate–critic products, and moment–critic products.
* `EPMasterEvent` assembles the raw localized empirical-process event.
* `EPPerN` removes the empirical sup-objective excess at a fixed sample size.
* `EPInequality` proves the explicit empirical-process inequality.
* `PerSample` assembles the current fixed-size, fixed-confidence event.
* `Regulariser` and `EventAssembly` retain the earlier simultaneous-in-sample-
  size regularizer and event-assembly route.
-/
