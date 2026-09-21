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

/-- A monotone deque state is represented by its front-to-back list of natural-number indices. -/
abbrev Deque := List ℕ

/-- The initial deque before any stream index has entered is empty. -/
def initialDeque : Deque := []

/-- Front expiration drops exactly the longest prefix whose indices lie strictly before the new
left endpoint. -/
def expireFront (left : ℕ) (q : Deque) : Deque :=
  q.dropWhile (fun i => decide (i < left))

/-- The indices reported as front pops are exactly the prefix discarded by front expiration. -/
def expiredFront (left : ℕ) (q : Deque) : List ℕ :=
  q.takeWhile (fun i => decide (i < left))

/-- Back pruning for a new index retains the longest prefix whose values are not in the dominated
suffix.  Entries tied with the new value are removed, implementing the rightmost tie policy. -/
def pruneBack (stream : Stream α) (q : Deque) (i : ℕ) : Deque :=
  q.rdropWhile (fun j => decide (stream.value j ≤ stream.value i))

/-- The indices reported as back pops are the suffix removed while inserting the new index. -/
def prunedBack (stream : Stream α) (q : Deque) (i : ℕ) : List ℕ :=
  q.rtakeWhile (fun j => decide (stream.value j ≤ stream.value i))

/-- Inserting one index first prunes its dominated suffix and then appends the new index. -/
def push (stream : Stream α) (q : Deque) (i : ℕ) : Deque :=
  pruneBack stream q i ++ [i]

/-- A batch insertion records its final deque, every pushed index, and every index removed from the
back while processing the batch. -/
structure PushBatch where
  state : Deque
  pushed : List ℕ
  backPopped : List ℕ

/-- Batch insertion processes new indices from left to right with the rightmost-stable push
operation and concatenates its back-pop log. -/
def pushAll (stream : Stream α) : Deque → List ℕ → PushBatch
  | q, [] => { state := q, pushed := [], backPopped := [] }
  | q, i :: is =>
      let removed := prunedBack stream q i
      let rest := pushAll stream (push stream q i) is
      { state := rest.state, pushed := i :: rest.pushed,
        backPopped := removed ++ rest.backPopped }

/-- A deque is valid between raw endpoints when all retained indices are active and stream-bounded,
indices strictly increase, retained values strictly decrease, and every omitted active index is
dominated by a retained later index. -/
structure ValidAt (stream : Stream α) (left right : ℕ) (q : Deque) : Prop where
  active : ∀ i ∈ q, ActiveAt left right i ∧ i < stream.length
  index_ordered : q.Pairwise (· < ·)
  value_decreasing : q.Pairwise (fun i j => stream.value j < stream.value i)
  dominates_omitted : ∀ i, ActiveAt left right i → i < stream.length → i ∉ q →
    ∃ j ∈ q, i < j ∧ stream.value i ≤ stream.value j

/-- A deque is valid for a bounded window when it satisfies the raw-endpoint invariant at that
window's endpoints. -/
def Valid (stream : Stream α) (w : Window stream.length) (q : Deque) : Prop :=
  ValidAt stream w.left w.right q

/-- The empty initial deque satisfies the invariant for the empty raw window from zero to zero. -/
theorem initialDeque_validAt (stream : Stream α) :
    ValidAt stream 0 0 initialDeque := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [initialDeque]
  · simp [initialDeque]
  · simp [initialDeque]
  · simp [initialDeque, ActiveAt]

/-- Front expiration splits the original deque into exactly its reported popped prefix and retained
suffix. -/
theorem expiredFront_append_expireFront (left : ℕ) (q : Deque) :
    expiredFront left q ++ expireFront left q = q := by
  exact List.takeWhile_append_dropWhile

/-- Back pruning splits the original deque into exactly its retained prefix and reported popped
suffix. -/
theorem pruneBack_append_prunedBack (stream : Stream α) (q : Deque) (i : ℕ) :
    pruneBack stream q i ++ prunedBack stream q i = q := by
  exact List.rdropWhile_append_rtakeWhile

/-- Back pruning retains a prefix of the old deque. -/
theorem pruneBack_prefix (stream : Stream α) (q : Deque) (i : ℕ) :
    pruneBack stream q i <+: q := by
  exact List.rdropWhile_prefix _ _

/-- Back pruning preserves strict index order. -/
theorem pruneBack_index_ordered (stream : Stream α) {q : Deque} {i : ℕ}
    (hq : q.Pairwise (· < ·)) : (pruneBack stream q i).Pairwise (· < ·) := by
  exact hq.sublist (pruneBack_prefix stream q i).sublist

/-- Back pruning preserves strict decrease of retained values. -/
theorem pruneBack_value_decreasing (stream : Stream α) {q : Deque} {i : ℕ}
    (hq : q.Pairwise (fun j k => stream.value k < stream.value j)) :
    (pruneBack stream q i).Pairwise (fun j k => stream.value k < stream.value j) := by
  exact hq.sublist (pruneBack_prefix stream q i).sublist

/-- A single push contains the new index, and every other retained index came from the old deque. -/
theorem mem_push_iff (stream : Stream α) (q : Deque) (i k : ℕ) :
    k ∈ push stream q i ↔ k ∈ pruneBack stream q i ∨ k = i := by
  simp [push]

/-- If the old deque has strictly increasing indices all below the new index, one push preserves
strict index order. -/
theorem push_index_ordered (stream : Stream α) {q : Deque} {i : ℕ}
    (hq : q.Pairwise (· < ·)) (hi : ∀ j ∈ q, j < i) :
    (push stream q i).Pairwise (· < ·) := by
  rw [push, List.pairwise_append]
  refine ⟨pruneBack_index_ordered stream hq, List.pairwise_singleton _ _, ?_⟩
  intro j hj k hk
  simp only [List.mem_singleton] at hk
  subst k
  exact hi j ((pruneBack_prefix stream q i).mem hj)

/-- If retained values were strictly decreasing, one rightmost-stable push again leaves strictly
decreasing values. -/
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

/-- Every index removed from the back by one push is earlier than the new index and has value at
most the new value, provided the old indices are earlier than the new one. -/
theorem mem_prunedBack_dominated (stream : Stream α) {q : Deque} {i j : ℕ}
    (hindex : ∀ k ∈ q, k < i) (hj : j ∈ prunedBack stream q i) :
    j < i ∧ stream.value j ≤ stream.value i := by
  constructor
  · exact hindex j ((List.rtakeWhile_suffix _ _).mem hj)
  · have h := List.mem_rtakeWhile_imp hj
    simpa [prunedBack] using h

/-- [A deque satisfying the raw-window invariant](hyp:h) [has no duplicate indices](goal). -/
theorem ValidAt.nodup {stream : Stream α} {left right : ℕ} {q : Deque}
    (h : ValidAt stream left right q) : q.Nodup := by
  exact h.index_ordered.nodup

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque
