## Done
- `Basic.lean`, `ConditionalLaw.lean`, `FiniteAggregation.lean`, and `Measurability.lean` are sorry-free; exact-word conditioning, selected-coordinate reindexing/product law, finite aggregation, and real-supremum measurability are proved.
- The public generic lift and DKW-radius API is scaffolded in `TailLift.lean` without changing the stated hypotheses or event.
- Round-3 ground truth: direct `lake env lean .../TailLift.lean` and LSP diagnostics both succeed with exactly three `sorry` warnings and no errors; source scan finds no `admit` or declared `axiom`.
- Re-ran Causalean and Mathlib searches. The closed layers already expose the needed local lemmas; useful remaining primitives are `Measure.map_apply` and the finite-partition lift.
- Reconfirmed Massart's 1990 primary-paper record (DOI `10.1214/aop/1176990746`) and sharp constant 2; direct Project Euclid full-text fetch is blocked by its Incapsula interstitial. At the requested radius, `2 exp (-2m epsilon^2) = alpha/2`.

## Remaining
- `TailLift.lean`: `measurableSet_selectedCDFBadEvent`.
- `TailLift.lean`: `conditionalMarkedSubsample_empiricalCDF_tail`.
- `TailLift.lean`: `conditionalMarkedSubsample_dkwRadius` (a direct specialization once the generic lift is closed).

## Blocked
- No mathematical or dependency blocker.
- Mathlib/Causalean still exposes no fixed-size DKW--Massart theorem, so the DKW-radius theorem correctly accepts that result as the expressly allowed theorem-valued hypothesis.

## Decisions
- Preserve `Fin n` indexing, ENNReal tail probabilities, the genuine real-threshold `sSup`, and the positive-mark factorization API.
- Use one filler for `TailLift.lean`: its three obligations form one sequential import cluster, so parallel fillers would violate the shared-tree/import-closure rule.
- Prove event measurability and the tail bound by the finite exact-word partition; zero-selected-count cells are empty and positive-count cells rewrite via `selectedCDFBadEvent_inter_wordEvent` and `selectedOutcomes_conditionalLaw`.
