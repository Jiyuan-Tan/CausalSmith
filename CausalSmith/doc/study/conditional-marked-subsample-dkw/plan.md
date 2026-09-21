## Done
- All five modules (`Basic.lean`, `ConditionalLaw.lean`, `FiniteAggregation.lean`, `Measurability.lean`, `TailLift.lean`) are sorry-free and individually elaborate successfully.
- Exact-word conditioning, selected-coordinate reindexing, conditional iid product law, finite aggregation, real-supremum measurability, generic tail lifting, and the DKW-radius specialization are proved.
- Fresh LSP diagnostics and `lake build CausalSmith.Substrate.ConditionalMarkedSubsampleDkw.TailLift` succeed with no errors.
- Source scan finds no `sorry`, `admit`, or declared `axiom`; `#print axioms` for the public conditional-law, aggregation, measurability, generic-tail, and DKW declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Causalean and Mathlib searches found no existing fixed-size DKW–Massart theorem. Massart’s primary record/abstract confirms the unrestricted two-sided bound `2 exp (-2 λ²)`; the accessible full-PDF link failed.

## Remaining
- None.

## Blocked
- None. The absent library DKW theorem is handled by the explicitly permitted theorem-valued hypothesis.

## Decisions
- Preserve the genuine `Fin n`/ENNReal API, positive Boolean-mark factorization, exact selected-count event, real-threshold supremum, and count-dependent radius.
- Keep `α > 0` and `α ≤ 1` in the DKW-facing wrapper as its confidence-parameter domain; the wrapper directly specializes the generic lift at `sqrt (log (4 / α) / (2m))` and tail `α / 2`.
- Advance to review with no filler dispatches; only harmless unused-hypothesis/style warnings remain.