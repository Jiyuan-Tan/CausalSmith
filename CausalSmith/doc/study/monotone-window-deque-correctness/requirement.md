# Substrate requirement: monotone-window-deque-correctness

## Goal
Build a reusable, axiom-clean Lean API proving correctness and linear operation bounds for a monotone deque that reports maxima over a finite stream whose active windows have nondecreasing contiguous endpoints.

## Provides (API contract)
- A paper-independent specification of a finite ordered value stream, a sequence of contiguous half-open active windows `[left k, right k)`, and the hypotheses that both endpoints are nondecreasing and lie within the stream.
- A monotone-deque state or trace representation whose stored indices are active, strictly ordered by index, and undominated by later active values; ties must have an explicit deterministic policy.
- Initialization and one-step update operations that expire indices from the front and remove dominated indices from the back before inserting newly entered indices.
- Preservation theorems for the active/ordered/undominated invariant after each update, including empty windows, repeated endpoints, tied values, and windows that become empty.
- A head-correctness theorem: for every nonempty active window, the deque head is an active argmax and its value equals the finite-window maximum.
- A scan theorem assembling the one-step result over every window and returning the correct maximum/head witness at each step.
- Explicit operation accounting: every stream index is inserted at most once, removed from the front at most once, and removed from the back at most once. Deduce a linear bound on total deque operations and a linear (preferably window-width) bound on stored memory.
- A fixed-finite-pass interface suitable for composing a constant number of monotone-window scans while retaining the same asymptotic operation bound.

Names may vary, but the API must expose direct specialization theorems for correctness, head argmax, and total-operation/memory bounds without requiring consumers to re-prove the internal invariant.

## Statement / milestones
1. Define active-window membership and its finite list/Finset enumeration, including empty-window behavior.
2. Define the monotone deque invariant: all indices are active, indices are ordered, values are monotone under the chosen tie rule, and every active index omitted from the deque is dominated by a retained later index.
3. Prove front expiration and back pruning preserve the relevant parts of the invariant.
4. Prove insertion of the newly entered interval restores the full invariant for the next monotone window.
5. Prove a nonempty valid deque has a head, and invariant head value equals the maximum over the active window; return an argmax index as well as value equality.
6. Fold the update across the finite schedule and prove pointwise correctness for every scheduled window.
7. Define a trace-level count of pushes, front pops, and back pops. Charge each pop to its unique prior insertion and prove total operations are bounded by a constant times stream length plus schedule length; prove stored indices never exceed the active window size (or a clearly stated linear bound).
8. Prove a constant-number-of-passes corollary that sums the per-pass bounds.

## Standard reference
This is the standard sliding-window maximum algorithm using a monotone deque. The proof should be self-contained from finite list/Finset order facts, invariant preservation, and an amortized charging argument; no external algorithm oracle is needed.

## Intended reuse
The immediate consumer is the exact finite-support linear scan in `pid_imperfectref_cutoff_regret`, which has four fixed sign masks and monotone contiguous admissibility windows. The substrate must remain general over finite ordered streams and must not mention policies, regret, reference tests, allocations, sign masks, or any research-run type.

## May assume / must derive
May assume decidable linear orders on indices and values, valid bounded nondecreasing endpoints, and a supplied finite stream. May choose a stable leftmost or rightmost tie convention and state it explicitly. Must derive invariant preservation, head correctness, scan correctness, per-index insertion/removal uniqueness, total operation bounds, and memory bounds. No `sorry`, `admit`, new `axiom`, imperative runtime primitive, or unproved complexity assertion.

## Non-goals
Do not implement a mutable array runtime, benchmark executable code, prove lower bounds, handle arbitrary noncontiguous windows, or formalize the paper's regret objective and endpoint assembly.

## Known building blocks
Mathlib list/Finset ranges, folds, filtering, maxima, ordered-list lemmas, and `Nat` sum/cardinality bounds may be used. The qid-local `Helpers/Scan.lean` contains 13 proved generic lemmas for membership, nonemptiness, length, append, head maxima, and one-step storage, but reusable substrate must not import the research module; it may independently reproduce or generalize those facts.
