## Done
- `Basic.lean`: ordered retention, measurability, exact unequal-pool product law, and full `Q^m` auxiliary-law certificate are closed.
- `Failure.lean`: conditional two-tail, scale-floor decomposition, and prior-predictive failure bounds are closed.
- `Risk.lean`: bounded-loss rule transfer, Bayes-to-worst-case comparison, and risk measurability are closed.
- `Main.lean`: `minimaxDecisionRisk_lower_of_rawBayesTransfer` is closed.
- Ground truth: targeted build exits 0; LSP reports no errors and exactly one `sorry` warning.

## Remaining
- `Main.lean`: prove `randomScale_twoFuzzy_minimax_lower_transfer` (the only repository-tree `sorry`).

## Blocked
- None.

## Decisions
- Dispatch one filler for the sole remaining theorem; no decomposition helper is needed because all dependency-layer results are closed and a complete proof skeleton passed `lean_multi_attempt` without errors.
- Reuse `priorPredictive_retentionFailure_le`, `measurable_transferredRawRule`, `bayesDecisionRisk_transferredRawRule_le_worstCase_add`, `max_le`, and `minimaxDecisionRisk_lower_of_rawBayesTransfer`.
- Preserve the generic ENNReal API, shared random scale, arbitrary unequal `n,m`, and exact full auxiliary-law contract.
- Library search was completed first. No individually identifiable primary source was named, so external source fetching was skipped.