import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Basic
import Mathlib.Data.List.DropRight

/-!
# Monotone deque operations and invariant

This module defines the purely functional deque kernel.  The deterministic tie policy is
rightmost-stable: inserting a value deletes every suffix entry with value less than or equal to the
new value.  Consequently retained values are strictly decreasing from front to back.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- [A monotone deque](goal) is represented by its front-to-back list of natural-number indices. -/
abbrev Deque := List ℕ

/-- [The initial deque](goal) is empty before any stream index enters. -/
def initialDeque : Deque := []

/-- [A left endpoint](hyp:left) and [a deque](hyp:q) determine [the deque after front expiration](goal). -/
def expireFront (left : ℕ) (q : Deque) : Deque :=
  q.dropWhile (fun i => decide (i < left))

/-- [A left endpoint](hyp:left) and [a deque](hyp:q) determine [the recorded front pops](goal). -/
def expiredFront (left : ℕ) (q : Deque) : List ℕ :=
  q.takeWhile (fun i => decide (i < left))

/-- [A stream](hyp:stream), [a deque](hyp:q), and [a new index](hyp:i) determine [the deque after
rightmost-stable back pruning](goal), which removes ties in favor of the newer index. -/
def pruneBack (stream : Stream α) (q : Deque) (i : ℕ) : Deque :=
  q.rdropWhile (fun j => decide (stream.value j ≤ stream.value i))

/-- [A stream](hyp:stream), [a deque](hyp:q), and [a new index](hyp:i) determine [the recorded
back pops](goal). -/
def prunedBack (stream : Stream α) (q : Deque) (i : ℕ) : List ℕ :=
  q.rtakeWhile (fun j => decide (stream.value j ≤ stream.value i))

/-- [A stream](hyp:stream), [a deque](hyp:q), and [a new index](hyp:i) determine [the deque after
one rightmost-stable insertion](goal). -/
def push (stream : Stream α) (q : Deque) (i : ℕ) : Deque :=
  pruneBack stream q i ++ [i]

/-- A batch insertion records its final deque, every pushed index, and every index removed from the
back while processing the batch. -/
structure PushBatch where
  state : Deque
  pushed : List ℕ
  backPopped : List ℕ

/-- [A stream](hyp:stream) determines [the recorded batch insertion](goal) from an initial deque
and a list of entering indices. -/
def pushAll (stream : Stream α) : Deque → List ℕ → PushBatch
  | q, [] => { state := q, pushed := [], backPopped := [] }
  | q, i :: is =>
      let removed := prunedBack stream q i
      let rest := pushAll stream (push stream q i) is
      { state := rest.state, pushed := i :: rest.pushed,
        backPopped := removed ++ rest.backPopped }

/-- [A stream](hyp:stream), [two raw endpoints](hyp:left,right), and [a deque](hyp:q) satisfy the
validity invariant when retained indices are active and ordered and omitted active indices are
dominated. -/
structure ValidAt (stream : Stream α) (left right : ℕ) (q : Deque) : Prop where
  active : ∀ i ∈ q, ActiveAt left right i ∧ i < stream.length
  index_ordered : q.Pairwise (· < ·)
  value_decreasing : q.Pairwise (fun i j => stream.value j < stream.value i)
  dominates_omitted : ∀ i, ActiveAt left right i → i < stream.length → i ∉ q →
    ∃ j ∈ q, i < j ∧ stream.value i ≤ stream.value j

/-- [A stream](hyp:stream), [a bounded window](hyp:w), and [a deque](hyp:q) determine [whether
the deque is valid for that window](goal). -/
def Valid (stream : Stream α) (w : Window stream.length) (q : Deque) : Prop :=
  ValidAt stream w.left w.right q

/-- [A stream](hyp:stream) has [an empty initial deque satisfying the zero-width invariant](goal). -/
theorem initialDeque_validAt (stream : Stream α) :
    ValidAt stream 0 0 initialDeque := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [initialDeque]
  · simp [initialDeque]
  · simp [initialDeque]
  · simp [initialDeque, ActiveAt]

/-- [A left endpoint](hyp:left) and [a deque](hyp:q) have [a reported front-pop prefix followed by
the retained deque exactly equal to the original deque](goal). -/
theorem expiredFront_append_expireFront (left : ℕ) (q : Deque) :
    expiredFront left q ++ expireFront left q = q := by
  exact List.takeWhile_append_dropWhile

/-- [A stream](hyp:stream), [a deque](hyp:q), and [a new index](hyp:i) have [a retained prefix and
reported back-pop suffix exactly equal to the original deque](goal). -/
theorem pruneBack_append_prunedBack (stream : Stream α) (q : Deque) (i : ℕ) :
    pruneBack stream q i ++ prunedBack stream q i = q := by
  exact List.rdropWhile_append_rtakeWhile

/-- [A stream](hyp:stream), [a deque](hyp:q), and [a new index](hyp:i) ensure [that back pruning
retains a prefix of the old deque](goal). -/
theorem pruneBack_prefix (stream : Stream α) (q : Deque) (i : ℕ) :
    pruneBack stream q i <+: q := by
  exact List.rdropWhile_prefix _ _

/-- [A stream](hyp:stream), [a new index](hyp:i), and [strictly ordered old deque indices](hyp:hq)
ensure [that back pruning preserves strict index order](goal). -/
theorem pruneBack_index_ordered (stream : Stream α) {q : Deque} {i : ℕ}
    (hq : q.Pairwise (· < ·)) : (pruneBack stream q i).Pairwise (· < ·) := by
  exact hq.sublist (pruneBack_prefix stream q i).sublist

/-- [A stream](hyp:stream), [a new index](hyp:i), and [strictly decreasing old deque values](hyp:hq)
ensure [that back pruning preserves strict value decrease](goal). -/
theorem pruneBack_value_decreasing (stream : Stream α) {q : Deque} {i : ℕ}
    (hq : q.Pairwise (fun j k => stream.value k < stream.value j)) :
    (pruneBack stream q i).Pairwise (fun j k => stream.value k < stream.value j) := by
  exact hq.sublist (pruneBack_prefix stream q i).sublist

/-- [A stream](hyp:stream), [a deque](hyp:q), [a new index](hyp:i), and [a queried index](hyp:k)
have [the stated membership characterization after one push](goal). -/
theorem mem_push_iff (stream : Stream α) (q : Deque) (i k : ℕ) :
    k ∈ push stream q i ↔ k ∈ pruneBack stream q i ∨ k = i := by
  simp [push]

/-- [A stream](hyp:stream), [strictly ordered old deque indices](hyp:hq), and [all old indices
being earlier than the new one](hyp:hi) ensure [that one push preserves strict index order](goal). -/
theorem push_index_ordered (stream : Stream α) {q : Deque} {i : ℕ}
    (hq : q.Pairwise (· < ·)) (hi : ∀ j ∈ q, j < i) :
    (push stream q i).Pairwise (· < ·) := by
  rw [push, List.pairwise_append]
  refine ⟨pruneBack_index_ordered stream hq, List.pairwise_singleton _ _, ?_⟩
  intro j hj k hk
  simp only [List.mem_singleton] at hk
  subst k
  exact hi j ((pruneBack_prefix stream q i).mem hj)

/-- [A stream](hyp:stream) and [strictly decreasing old deque values](hyp:hq) ensure [that one
rightmost-stable push leaves strictly decreasing values](goal). -/
theorem push_value_decreasing (stream : Stream α) {q : Deque} {i : ℕ}
    (hq : q.Pairwise (fun j k => stream.value k < stream.value j)) :
    (push stream q i).Pairwise (fun j k => stream.value k < stream.value j) := by
  rw [push, List.pairwise_append]
  refine ⟨pruneBack_value_decreasing stream hq, List.pairwise_singleton _ _, ?_⟩
  intro j hj k hk
  simp only [List.mem_singleton] at hk
  subst k
  let r := pruneBack stream q i
  have hr_ne : r ≠ [] := List.ne_nil_of_mem hj
  have hlast : stream.value i < stream.value (r.getLast hr_ne) := by
    have h := List.rdropWhile_last_not
      (fun j => decide (stream.value j ≤ stream.value i)) q hr_ne
    simpa [r, pruneBack] using h
  have hr : r.Pairwise (fun a b => stream.value b < stream.value a) := by
    exact pruneBack_value_decreasing stream (i := i) hq
  have hr_le : r.Pairwise (fun a b => stream.value b ≤ stream.value a) := by
    exact hr.imp (fun h => h.le)
  exact lt_of_lt_of_le hlast (hr_le.rel_getLast hj)

/-- [A stream](hyp:stream), [all old indices being earlier than the new index](hyp:hindex), and
[an index recorded as a back pop](hyp:hj) ensure [that the popped index is earlier and no larger
in value than the new index](goal). -/
theorem mem_prunedBack_dominated (stream : Stream α) {q : Deque} {i j : ℕ}
    (hindex : ∀ k ∈ q, k < i) (hj : j ∈ prunedBack stream q i) :
    j < i ∧ stream.value j ≤ stream.value i := by
  constructor
  · exact hindex j ((List.rtakeWhile_suffix _ _).mem hj)
  · have h := List.mem_rtakeWhile_imp hj
    simpa [prunedBack] using h

/-- [A valid raw-window deque](hyp:h) has [no duplicate indices](goal). -/
theorem ValidAt.nodup {stream : Stream α} {left right : ℕ} {q : Deque}
    (h : ValidAt stream left right q) : q.Nodup := by
  exact h.index_ordered.nodup

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque
