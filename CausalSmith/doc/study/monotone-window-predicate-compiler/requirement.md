# Substrate requirement: monotone-window-predicate-compiler

## Goal
Extend the existing `Causalean.Mathlib.Algorithms.MonotoneWindowDeque` family with a paper-independent compiler from monotone predicates on sparse raw keys to its position-indexed window schedule API.

## Provides (API contract)
For `keys : List ι` and `steps : List κ`, expose a `PredicateWindowSchedule` specified by entry and stay predicates on raw keys and steps, with left and right position endpoints. Provide an `active_iff` characterization, exact take/drop endpoint laws, endpoint monotonicity and bounds, and a theorem named `scan_predicateSchedule_state_eq` (or an equivalently clear API name) identifying the generic position scan mapped through `keys.get` with the corresponding raw-key predicate scan. Derive raw-key head-argmax correctness and `scanCost_le` and `peakStored` bounds.

## Statement / milestones
- Characterize active positions exactly by the entry/stay predicates.
- Prove that newly entering keys are exactly the appropriate `takeWhile` segment and that right-end advancement agrees with it.
- Prove that expired keys are exactly the appropriate `dropWhile` segment and that left-end advancement agrees with it.
- Prove endpoint monotonicity, endpoint bounds, and validity for empty windows and sparse key lists.
- Show that mapping every generic position in the position-indexed scan through `keys.get` gives the same deque trace as a raw-key scan that enters keys with `takeWhile`, performs the generic monotone back-pruning pushes, and expires keys with `dropWhile`.
- Transfer head argmax correctness and the existing operation-cost and peak-storage bounds to the raw-key scan.
- Handle tied scores with a deterministic tie policy and expose an interface suitable for a constant number of scan passes.

## Standard reference
This is the standard representation equivalence between two-pointer predicate windows over a sorted sparse key array and index-endpoint sliding-window scans, composed with the already-promoted monotone deque correctness and amortized accounting API.

## Intended reuse
Consumers express feasibility windows naturally as monotone predicates on raw sparse keys, while the existing verified deque API operates on positions. The result must be reusable for arbitrary key, step, and score types and must not mention the motivating paper's masks, regret, measures, diagnostics, or allocations.

## May assume / must derive
May assume the explicit monotonicity hypotheses needed of the entry and stay predicates and may reuse `Causalean.Mathlib.Algorithms.MonotoneWindowDeque`. Must derive the endpoint/take/drop correspondence, state correspondence, and transferred correctness/accounting bounds. It may import Mathlib and Causalean, but must not import `CausalSmith` or any `*_Research` module. All declarations must be proved without `sorry`, `admit`, or new axioms.

## Non-goals
Do not formalize diagnostic-specific score formulas, four-mask reductions, regret identities, endpoint allocations, or theorem-specific output assembly.

## Known building blocks
Use the existing `Causalean.Mathlib.Algorithms.MonotoneWindowDeque` module family, especially its schedule, scan-state correctness, head-argmax, `scanCost_le`, and `peakStored` results, rather than duplicating the deque implementation.
