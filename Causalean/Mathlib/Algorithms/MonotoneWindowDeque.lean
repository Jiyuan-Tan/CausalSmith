import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Passes
import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.PredicateAccounting

/-!
# Correctness and linear bounds for monotone window deques

This umbrella module exports a reusable, paper-independent API for finite ordered streams,
nondecreasing contiguous windows, a rightmost-stable monotone deque, scan correctness, exact event
accounting, window-width memory bounds, and constant-finite-pass composition.
-/
