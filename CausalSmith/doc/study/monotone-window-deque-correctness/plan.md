## Done
- `Basic.lean`, `Deque.lean`, `Update.lean`, `Correctness.lean`, `Scan.lean`, and `Accounting.lean` are fully proved; all correctness, argmax, scan, accounting, linear-operation, and memory declarations are closed.
- Ground truth: LSP reports only three `sorry` warnings in `Passes.lean`; `lake build CausalSmith.Substrate.MonotoneWindowDequeCorrectness.Main` succeeds (866 jobs).
- Source audit finds no `admit`, declared `axiom`, or `unsafe`; exactly three `sorry`s remain.
- Library search found `Finset.sum_le_card_nsmul` and `Fin.sum_const` for the fixed-pass cost summation.

## Remaining
- `Passes.lean`: `FixedPasses.head_value_eq_windowMax`, `FixedPasses.totalCost_le`, `FixedPasses.memory_le_windowWidth`.

## Blocked
- None.

## Decisions
- Keep natural-number indices and the deterministic rightmost tie policy: a new equal value removes the older equal-valued index.
- Keep the genuine per-index uniqueness, charging, `2 * stream.length + schedule.steps` cost, and window-width storage contracts unchanged.
- Use one filler because all three remaining corollaries are small, share one file/import closure, and directly specialize already-proved scan/accounting results.
- No primary source was fetched: the requirement names the standard algorithm but no specific paper or canonical source.