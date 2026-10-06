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

This umbrella module exports a reusable, paper-independent API for finite ordered streams,
nondecreasing contiguous windows, a rightmost-stable monotone deque, scan correctness, exact event
accounting, window-width memory bounds, and finite indexed families of passes. The accounting
counts recorded mutations and scheduled-window events; it does not bound the runtime of the list
implementation.
-/
