module
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Accounting
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Basic
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Correctness
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Deque
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Passes
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.PredicateAccounting
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.PredicateRawScan
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.PredicateSchedule
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Scan
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Update
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Accounting
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Basic
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Correctness
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Deque
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Passes
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.PredicateAccounting
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.PredicateRawScan
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.PredicateSchedule
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Scan
public import Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque.Update

/-!
# Correctness and mutation bounds for monotone window deques

Verified sliding-window maximum by a monotone deque. Given a finite stream of values in a linear
order and a list of contiguous index windows whose left and right endpoints are both
nondecreasing, the scan maintains a deque of indices with strictly decreasing values (ties keep
the rightmost index). At every nonempty window the head of the deque is an index in the window
whose value is the maximum over that window. The total number of recorded deque insertions and
deletions over the whole scan is at most twice the stream length plus the number of windows, and
the deque never holds more indices than the current window width. These are counts of recorded
mutations, not running-time bounds for the list implementation.

## Contents

* `Basic` — finite streams, half-open windows, and schedules with nondecreasing endpoints.
* `Deque`, `Update` — the deque operations (expire from the front, prune and push at the back),
  the validity invariant, and its preservation by one window update.
* `Scan`, `Correctness` — the scan over a schedule; `scan_head_value_eq_windowMax` (the head
  attains the window maximum).
* `Accounting` — `scanMutationCount_le` (at most 2·length + number of windows mutations) and
  `scan_memory_le_windowWidth`.
* `Passes` — finitely many schedules over one stream, with the summed bound
  `FixedPasses.totalMutationCount_le`.
* `PredicateSchedule`, `PredicateRawScan`, `PredicateAccounting` — windows specified by entry and
  stay predicates on a list of raw keys, a raw-key version of the scan shown to produce the same
  trace, and the same correctness and counting bounds for it.
-/
