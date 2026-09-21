## Done
- `Schedule.lean`: endpoint exactness/bounds, activity characterization, monotonicity, take/drop advancement, compilation, indexed laws, and empty-key behavior are proved with no holes.
- `RawScan.lean`: raw push/tie lemmas, raw scan length, full mapped-trace equivalence `scan_predicateSchedule_state_eq`, and per-step after-state equivalence are proved with no holes.
- Ground truth: source scan finds exactly 7 `sorry`s, all in `Main.lean`; Lean LSP reports no errors; `lake env lean .../Main.lean` and targeted `lake build CausalSmith.Substrate.MonotoneWindowPredicateCompiler.Main` succeed with only sorry/style warnings.
- Library search confirmed `scanCost_le`, `peakStored_le_length`, `scan_memory_le_windowWidth`, `scan_head_argmax`, `scan_valid_at`, and `ValidAt.dominates_omitted`; LeanSearch found `List.filterMap_eq_map_iff_forall_eq_some` for safe-lookup length preservation.

## Remaining
- `Main.lean`: `rawScanCost_eq_scanCost`, `rawPeakStored_eq_peakStored`, `rawScanCost_le`, `rawPeakStored_le_length`, `rawScan_memory_le_windowWidth`, `rawScan_head_argmax`, `PredicatePasses.totalRawCost_le`.
- After closure: full live-file check, forbidden-proof scan, targeted build, and `#print axioms` on representation, argmax, and resource theorems.

## Blocked
- None.

## Decisions
- Dispatch one filler for the remaining `Main.lean` import layer; earlier work already separated the lower `RawScan.lean` proof chain, and concurrent edits to the same dependent file would be unsafe.
- Preserve all public statements, Prop-valued predicates, sparse/duplicate raw keys, and the rightmost-stable `≤` tie policy. Private in-bounds/mapping helpers may be added without changing the API.
- No external primary source was named; this is a generic representation/accounting transfer, so no source was fetched.