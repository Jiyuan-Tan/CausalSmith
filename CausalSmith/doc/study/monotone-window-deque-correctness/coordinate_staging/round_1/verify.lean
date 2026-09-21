import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.DropRight
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite streams and monotone contiguous window schedules

This module gives the paper-independent input model for a monotone-window scan: a finite prefix of
an ordered value function, bounded half-open windows, and a finite schedule whose two endpoints are
nondecreasing.  It also relates predicate, list, and finset views of a window, including empty
windows.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

/-- A finite ordered stream consists of a length and a value function whose indices below that
length are the stream entries.  Values outside the finite prefix are deliberately irrelevant. -/
structure Stream (α : Type*) where
  length : ℕ
  value : ℕ → α

/-- A contiguous half-open window in a stream of length `n` has endpoints `left ≤ right ≤ n`. -/
structure Window (n : ℕ) where
  left : ℕ
  right : ℕ
  left_le_right : left ≤ right
  right_le_length : right ≤ n

/-- An index is active between raw half-open endpoints exactly when it is at least the left endpoint
and strictly below the right endpoint.  This predicate is empty when `right ≤ left`. -/
def ActiveAt (left right i : ℕ) : Prop := left ≤ i ∧ i < right

/-- An index is active in a bounded window exactly when it belongs to that window's half-open
interval. -/
def Active {n : ℕ} (w : Window n) (i : ℕ) : Prop := ActiveAt w.left w.right i

/-- The list enumeration of a bounded window contains its indices in increasing order. -/
def Window.indices {n : ℕ} (w : Window n) : List ℕ :=
  List.range' w.left (w.right - w.left)

/-- The finset enumeration of a bounded window is the natural-number interval from `left`
inclusive to `right` exclusive. -/
def Window.indexFinset {n : ℕ} (w : Window n) : Finset ℕ := Finset.Ico w.left w.right

/-- List membership in a window enumeration is equivalent to active-window membership. -/
theorem Window.mem_indices_iff {n i : ℕ} (w : Window n) : i ∈ w.indices ↔ Active w i := by
  rw [Window.indices, List.mem_range'_1, Nat.add_sub_of_le w.left_le_right]
  rfl

/-- Finset membership in a window enumeration is equivalent to active-window membership. -/
theorem Window.mem_indexFinset_iff {n i : ℕ} (w : Window n) : i ∈ w.indexFinset ↔ Active w i := by
  simp [Window.indexFinset, Active, ActiveAt]

/-- The number of active indices is exactly the window width `right - left`. -/
theorem Window.card_indexFinset {n : ℕ} (w : Window n) :
    w.indexFinset.card = w.right - w.left := by
  simp [Window.indexFinset]

/-- A bounded window has no active indices exactly when its endpoints coincide. -/
theorem Window.indices_eq_nil_iff {n : ℕ} (w : Window n) :
    w.indices = [] ↔ w.left = w.right := by
  constructor
  · intro h
    have hlen : w.indices.length = 0 := by simp [h]
    rw [Window.indices, List.length_range'] at hlen
    exact Nat.le_antisymm w.left_le_right (Nat.sub_eq_zero_iff_le.mp hlen)
  · intro h
    simp [Window.indices, h]

/-- A bounded window is nonempty exactly when its left endpoint is strictly below its right
endpoint. -/
theorem Window.indexFinset_nonempty_iff {n : ℕ} (w : Window n) :
    w.indexFinset.Nonempty ↔ w.left < w.right := by
  simp [Window.indexFinset]

/-- A finite schedule is a list of bounded windows whose left endpoints and right endpoints are
both nondecreasing in schedule order. -/
structure Schedule (n : ℕ) where
  windows : List (Window n)
  left_mono : windows.Pairwise (fun a b => a.left ≤ b.left)
  right_mono : windows.Pairwise (fun a b => a.right ≤ b.right)

/-- The number of scheduled observations is the number of windows in the schedule. -/
def Schedule.steps {n : ℕ} (schedule : Schedule n) : ℕ := schedule.windows.length

/-- Every earlier scheduled window has no larger left endpoint than every later scheduled window. -/
theorem Schedule.left_le_of_get_lt {n : ℕ} (schedule : Schedule n)
    {i j : ℕ} (hi : i < schedule.steps) (hj : j < schedule.steps) (hij : i < j) :
    (schedule.windows.get ⟨i, hi⟩).left ≤ (schedule.windows.get ⟨j, hj⟩).left := by
  exact schedule.left_mono.rel_get_of_lt hij

/-- [A monotone schedule](hyp:schedule), [a valid earlier position](hyp:hi),
[a valid later position](hyp:hj), and [the earlier-before-later ordering](hyp:hij) ensure that
[the earlier window has no larger right endpoint](goal). -/
theorem Schedule.right_le_of_get_lt {n : ℕ} (schedule : Schedule n)
    {i j : ℕ} (hi : i < schedule.steps) (hj : j < schedule.steps) (hij : i < j) :
    (schedule.windows.get ⟨i, hi⟩).right ≤ (schedule.windows.get ⟨j, hj⟩).right := by
  exact schedule.right_mono.rel_get_of_lt hij

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque

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

/-!
# Window update and invariant preservation

This module combines front expiration with batch insertion of the newly entered right-endpoint
interval.  Its preservation results cover repeated endpoints, empty batches, empty windows, and
windows that become empty.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- One update record exposes the before/after states and the exact push, front-pop, and back-pop
event lists used for correctness and amortized accounting. -/
structure StepTrace (stream : Stream α) where
  oldRight : ℕ
  window : Window stream.length
  before : Deque
  afterExpiration : Deque
  after : Deque
  pushed : List ℕ
  frontPopped : List ℕ
  backPopped : List ℕ

/-- Updating to a new window expires indices before its left endpoint, inserts precisely the part
of the newly crossed right-endpoint interval that is still active, and records all deque events.
Starting at `max oldRight window.left` is essential when the left endpoint jumps past the old right
endpoint: indices skipped by that jump must never enter the deque. -/
def update (stream : Stream α) (oldRight : ℕ) (window : Window stream.length)
    (q : Deque) : StepTrace stream :=
  let expired := expireFront window.left q
  let enteredLeft := max oldRight window.left
  let entered := List.range' enteredLeft (window.right - enteredLeft)
  let batch := pushAll stream expired entered
  { oldRight := oldRight
    window := window
    before := q
    afterExpiration := expired
    after := batch.state
    pushed := batch.pushed
    frontPopped := expiredFront window.left q
    backPopped := batch.backPopped }

/-- Batch insertion records every input index, in its original order, in the push log. -/
private theorem pushAll_pushed_eq (stream : Stream α) (q : Deque) (indices : List ℕ) :
    (pushAll stream q indices).pushed = indices := by
  induction indices generalizing q with
  | nil => rfl
  | cons i is ih => simp [pushAll, ih]

/-- In a strictly increasing list, dropping the entries below a cutoff retains exactly the
original entries at or above that cutoff. -/
private theorem mem_dropWhile_lt_iff
    (left : ℕ) {q : List ℕ} (hq : q.Pairwise (· < ·)) (i : ℕ) :
    i ∈ q.dropWhile (fun k => decide (k < left)) ↔ i ∈ q ∧ left ≤ i := by
  induction q with
  | nil => simp
  | cons a q ih =>
      rw [List.pairwise_cons] at hq
      by_cases ha : a < left
      · simp only [List.dropWhile_cons, decide_eq_true_eq, ha, ↓reduceIte]
        rw [ih hq.2]
        constructor
        · rintro ⟨hi, hli⟩
          exact ⟨List.mem_cons_of_mem _ hi, hli⟩
        · rintro ⟨hi, hli⟩
          rcases List.mem_cons.mp hi with rfl | hi
          · omega
          · exact ⟨hi, hli⟩
      · have hale : left ≤ a := Nat.le_of_not_gt ha
        constructor
        · intro hi
          have hiq : i = a ∨ i ∈ q := by simpa [ha] using hi
          refine ⟨by simp [hiq], ?_⟩
          rcases hiq with rfl | hiq
          · exact hale
          · exact le_trans hale (Nat.le_of_lt (hq.1 i hiq))
        · intro hi
          simpa [ha] using hi.1

/-- The push log of an update is exactly the increasing half-open interval from the larger of the
old right and new left endpoints to the new right endpoint. -/
theorem update_pushed (stream : Stream α) (oldRight : ℕ)
    (window : Window stream.length) (q : Deque) :
    (update stream oldRight window q).pushed =
      List.range' (max oldRight window.left) (window.right - max oldRight window.left) := by
  unfold update
  exact pushAll_pushed_eq _ _ _

/-- Expiring the front of a valid old state preserves the full invariant for the same right
endpoint and any nondecreasing new left endpoint, even when those intermediate raw endpoints form
an empty interval. -/
theorem expireFront_preserves {stream : Stream α} {oldLeft oldRight newLeft : ℕ} {q : Deque}
    (hq : ValidAt stream oldLeft oldRight q) (hleft : oldLeft ≤ newLeft) :
    ValidAt stream newLeft oldRight (expireFront newLeft q) := by
  by_cases hempty : oldRight < newLeft
  · have hexp : expireFront newLeft q = [] := by
      rw [expireFront, List.dropWhile_eq_nil_iff]
      intro i hi
      simp only [decide_eq_true_eq]
      exact lt_trans (hq.active i hi).1.2 hempty
    rw [hexp]
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro i hactive
    simp only [ActiveAt] at hactive
    exfalso
    omega
  · have hsub : (expireFront newLeft q).Sublist q := by
      exact List.dropWhile_sublist _
    refine
      ⟨?_, hq.index_ordered.sublist hsub, hq.value_decreasing.sublist hsub, ?_⟩
    · intro i hi
      have himem : i ∈ q ∧ newLeft ≤ i := by
        exact (mem_dropWhile_lt_iff newLeft hq.index_ordered i).mp hi
      have hiold := hq.active i himem.1
      exact ⟨⟨himem.2, hiold.1.2⟩, hiold.2⟩
    · intro i hi hbound hin
      have hiold : ActiveAt oldLeft oldRight i :=
        ⟨le_trans hleft hi.1, hi.2⟩
      have hiq : i ∉ q := by
        intro hiq
        apply hin
        exact (mem_dropWhile_lt_iff newLeft hq.index_ordered i).mpr ⟨hiq, hi.1⟩
      obtain ⟨j, hjq, hij, hvalue⟩ := hq.dominates_omitted i hiold hbound hiq
      refine ⟨j, ?_, hij, hvalue⟩
      exact (mem_dropWhile_lt_iff newLeft hq.index_ordered j).mpr
        ⟨hjq, le_trans hi.1 (Nat.le_of_lt hij)⟩

/-- A state valid up to a right endpoint is also valid up to the larger of that endpoint and the
left endpoint.  The only nontrivial case is an originally empty raw interval, whose valid deque is
necessarily empty. -/
theorem ValidAt.to_max_right {stream : Stream α} {left right : ℕ} {q : Deque}
    (hq : ValidAt stream left right q) :
    ValidAt stream left (max right left) q := by
  by_cases hempty : right < left
  · have hqnil : q = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      have hactive := (hq.active i hi).1
      simp only [ActiveAt] at hactive
      omega
    rw [hqnil]
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro i hactive
    simp only [ActiveAt] at hactive
    have hmax : max right left = left := max_eq_right (Nat.le_of_lt hempty)
    rw [hmax] at hactive
    omega
  · have hle : left ≤ right := Nat.le_of_not_gt hempty
    simpa [max_eq_left hle] using hq

/-- Pushing the index at the current right boundary extends a valid nonempty-or-empty raw window
by one position while preserving activity, strict index order, strict value decrease, and
domination of omitted active indices. -/
theorem push_succ_preserves {stream : Stream α} {left right : ℕ} {q : Deque}
    (hq : ValidAt stream left right q) (hleft : left ≤ right)
    (hbound : right < stream.length) :
    ValidAt stream left (right + 1) (push stream q right) := by
  have hold_lt : ∀ j ∈ q, j < right := by
    intro j hj
    exact (hq.active j hj).1.2
  have hright_mem : right ∈ push stream q right := by
    exact (mem_push_iff stream q right right).mpr (Or.inr rfl)
  refine ⟨?_, push_index_ordered stream hq.index_ordered hold_lt,
    push_value_decreasing stream hq.value_decreasing, ?_⟩
  · intro i hi
    rcases (mem_push_iff stream q right i).mp hi with hi | hiEq
    · have hiq : i ∈ q := (pruneBack_prefix stream q right).mem hi
      have hactive := hq.active i hiq
      exact ⟨⟨hactive.1.1, Nat.lt_succ_of_lt hactive.1.2⟩, hactive.2⟩
    · subst i
      exact ⟨⟨hleft, Nat.lt_succ_self right⟩, hbound⟩
  · intro i hi hifinite hin
    have hine : i ≠ right := by
      intro hiright
      apply hin
      simpa [hiright] using hright_mem
    have hiright : i < right := by
      simp only [ActiveAt] at hi
      omega
    have hiold : ActiveAt left right i := ⟨hi.1, hiright⟩
    by_cases hiq : i ∈ q
    · have hipruned : i ∈ prunedBack stream q right := by
        have hiappend : i ∈ pruneBack stream q right ++ prunedBack stream q right := by
          rw [pruneBack_append_prunedBack]
          exact hiq
        rcases List.mem_append.mp hiappend with hiretained | hipruned
        · exact False.elim (hin ((mem_push_iff stream q right i).mpr (Or.inl hiretained)))
        · exact hipruned
      have hidominated := mem_prunedBack_dominated stream hold_lt hipruned
      exact ⟨right, hright_mem, hidominated.1, hidominated.2⟩
    · obtain ⟨j, hjq, hij, hvalue⟩ :=
        hq.dominates_omitted i hiold hifinite hiq
      by_cases hjretained : j ∈ pruneBack stream q right
      · exact ⟨j, (mem_push_iff stream q right j).mpr (Or.inl hjretained), hij, hvalue⟩
      · have hjpruned : j ∈ prunedBack stream q right := by
          have hjappend : j ∈ pruneBack stream q right ++ prunedBack stream q right := by
            rw [pruneBack_append_prunedBack]
            exact hjq
          exact (List.mem_append.mp hjappend).resolve_left hjretained
        have hjdominated := mem_prunedBack_dominated stream hold_lt hjpruned
        exact ⟨right, hright_mem, lt_trans hij hjdominated.1,
          le_trans hvalue hjdominated.2⟩

/-- Repeatedly pushing a consecutive range from the current right boundary extends a valid deque
across the whole range. -/
theorem pushAll_range_preserves {stream : Stream α} {left start count : ℕ} {q : Deque}
    (hq : ValidAt stream left start q) (hleft : left ≤ start)
    (hbound : start + count ≤ stream.length) :
    ValidAt stream left (start + count)
      (pushAll stream q (List.range' start count)).state := by
  induction count generalizing start q with
  | zero => simpa [pushAll]
  | succ count ih =>
    rw [List.range'_succ]
    simp only [pushAll]
    have hpush : ValidAt stream left (start + 1) (push stream q start) :=
      push_succ_preserves hq hleft (by omega)
    have hrec := ih (start := start + 1) (q := push stream q start)
      hpush (by omega) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

/-- Inserting the still-active part of the interval newly crossed by the right endpoint into a
valid expired state restores the full invariant at the enlarged right endpoint. -/
theorem pushAll_interval_preserves {stream : Stream α} {left oldRight newRight : ℕ} {q : Deque}
    (hq : ValidAt stream left oldRight q) (hright : oldRight ≤ newRight)
    (hbound : newRight ≤ stream.length) (hwindow : left ≤ newRight) :
    ValidAt stream left newRight
      (pushAll stream q
        (List.range' (max oldRight left) (newRight - max oldRight left))).state := by
  have hright? : max oldRight left ≤ newRight := max_le hright hwindow
  have hq' : ValidAt stream left (max oldRight left) q := hq.to_max_right
  have hbatch := pushAll_range_preserves
    (start := max oldRight left) (count := newRight - max oldRight left) hq'
    (le_max_right oldRight left)
    (by simpa [Nat.add_sub_of_le hright?] using hbound)
  simpa [Nat.add_sub_of_le hright?] using hbatch

/-- [A deque valid for the old window](hyp:hq), [a nondecreasing left endpoint](hyp:hleft), and
[a nondecreasing right endpoint](hyp:hright) [produce a deque valid for the new window after one
update](goal). -/
theorem update_preserves {stream : Stream α} {oldWindow newWindow : Window stream.length}
    {q : Deque} (hq : Valid stream oldWindow q)
    (hleft : oldWindow.left ≤ newWindow.left)
    (hright : oldWindow.right ≤ newWindow.right) :
    Valid stream newWindow (update stream oldWindow.right newWindow q).after := by
  unfold Valid at hq ⊢
  unfold update
  exact pushAll_interval_preserves
    (expireFront_preserves hq hleft)
    hright
    newWindow.right_le_length
    newWindow.left_le_right

/-- Updating the empty initial interval at right endpoint zero produces a valid deque for every
bounded first window. -/
theorem update_initial_preserves (stream : Stream α) (window : Window stream.length) :
    Valid stream window (update stream 0 window []).after := by
  unfold Valid
  unfold update
  exact pushAll_interval_preserves
    (expireFront_preserves (initialDeque_validAt stream) (Nat.zero_le _))
    (Nat.zero_le _)
    window.right_le_length
    window.left_le_right

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque

/-!
# Finite-window maxima and scheduled scans

The invariant implies that the deque head is an active argmax. This module exposes both the argmax
witness formulation and equality with the maximum of the finite active-value set. It then folds
updates over an entire monotone schedule so consumers never need to unfold the internal invariant.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- The finite set of values in a bounded active window is the image of its active index finset
under the stream value function. -/
def windowValues (stream : Stream α) (window : Window stream.length) : Finset α :=
  window.indexFinset.image stream.value

/-- A nonempty bounded window has a nonempty finite set of active values. -/
theorem windowValues_nonempty (stream : Stream α) (window : Window stream.length)
    (hne : window.left < window.right) : (windowValues stream window).Nonempty := by
  refine ⟨stream.value window.left, ?_⟩
  rw [windowValues, Finset.mem_image]
  exact ⟨window.left, (Window.mem_indexFinset_iff window).mpr ⟨le_rfl, hne⟩, rfl⟩

/-- The maximum value of a provably nonempty bounded window is the maximum of its finite active
value set. -/
def windowMax (stream : Stream α) (window : Window stream.length)
    (hne : window.left < window.right) : α :=
  (windowValues stream window).max' (windowValues_nonempty stream window hne)

/-- Every valid deque for a nonempty raw window has a head; that head is active and its value is at
least the value at every active stream index. -/
theorem ValidAt.head_argmax {stream : Stream α} {left right : ℕ} {q : Deque}
    (hq : ValidAt stream left right q) (hne : left < right) (hbound : right ≤ stream.length) :
    ∃ head tail, q = head :: tail ∧ ActiveAt left right head ∧ head < stream.length ∧
      ∀ i, ActiveAt left right i → i < stream.length → stream.value i ≤ stream.value head := by
  have hq_ne : q ≠ [] := by
    intro hq_nil
    have hleft_bound : left < stream.length := lt_of_lt_of_le hne hbound
    obtain ⟨j, hj, -⟩ := hq.dominates_omitted left ⟨le_rfl, hne⟩ hleft_bound (by
      simp [hq_nil])
    simp [hq_nil] at hj
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hq_ne
  have hhead := hq.active head (by simp)
  refine ⟨head, tail, rfl, hhead.1, hhead.2, ?_⟩
  intro i hi hibound
  have hmember_le : ∀ j ∈ head :: tail, stream.value j ≤ stream.value head := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact le_rfl
    · exact (List.pairwise_cons.mp hq.value_decreasing).1 j hj |>.le
  by_cases hiq : i ∈ head :: tail
  · exact hmember_le i hiq
  · obtain ⟨j, hjq, -, hij⟩ := hq.dominates_omitted i hi hibound hiq
    exact le_trans hij (hmember_le j hjq)

/-- Every valid deque for a nonempty bounded window has a head that is an active argmax. -/
theorem Valid.head_argmax {stream : Stream α} {window : Window stream.length} {q : Deque}
    (hq : Valid stream window q) (hne : window.left < window.right) :
    ∃ head tail, q = head :: tail ∧ Active window head ∧
      ∀ i, Active window i → stream.value i ≤ stream.value head := by
  obtain ⟨head, tail, hqeq, hhead, -, hmax⟩ :=
    ValidAt.head_argmax hq hne window.right_le_length
  refine ⟨head, tail, hqeq, hhead, ?_⟩
  intro i hi
  exact hmax i hi (lt_of_lt_of_le hi.2 window.right_le_length)

/-- The head value of a valid deque equals the finite-window maximum, while the returned head is
also an active argmax index. -/
theorem Valid.head_value_eq_windowMax {stream : Stream α}
    {window : Window stream.length} {q : Deque}
    (hq : Valid stream window q) (hne : window.left < window.right) :
    ∃ head tail, q = head :: tail ∧ Active window head ∧
      stream.value head = windowMax stream window hne ∧
      ∀ i, Active window i → stream.value i ≤ stream.value head := by
  obtain ⟨head, tail, hqeq, hhead, hmax⟩ := hq.head_argmax hne
  refine ⟨head, tail, hqeq, hhead, ?_, hmax⟩
  unfold windowMax
  symm
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · rw [windowValues, Finset.mem_image]
    exact ⟨head, (Window.mem_indexFinset_iff window).mpr hhead, rfl⟩
  · intro value hvalue
    rw [windowValues, Finset.mem_image] at hvalue
    obtain ⟨i, hi, rfl⟩ := hvalue
    exact hmax i ((Window.mem_indexFinset_iff window).mp hi)

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque


/-!
# Folding updates across a monotone window schedule

This module runs the deque update over every scheduled window.  Its pointwise theorems return the
valid state, active head argmax, and exact maximum value at any requested schedule position.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- Scanning a list of windows from a prior right endpoint records one update per window and feeds
each after-state into the next update. -/
def scanFrom (stream : Stream α) : ℕ → Deque → List (Window stream.length) →
    List (StepTrace stream)
  | _, _, [] => []
  | oldRight, q, window :: windows =>
      let step := update stream oldRight window q
      step :: scanFrom stream window.right step.after windows

/-- Scanning a schedule starts from the empty deque and the empty prefix with right endpoint
zero. -/
def scan (stream : Stream α) (schedule : Schedule stream.length) : List (StepTrace stream) :=
  scanFrom stream 0 initialDeque schedule.windows

/-- A scan produces exactly one trace step for each scheduled window. -/
theorem length_scan (stream : Stream α) (schedule : Schedule stream.length) :
    (scan stream schedule).length = schedule.steps := by
  have hlength : ∀ (oldRight : ℕ) (q : Deque) (windows : List (Window stream.length)),
      (scanFrom stream oldRight q windows).length = windows.length := by
    intro oldRight q windows
    induction windows generalizing oldRight q with
    | nil => rfl
    | cons window windows ih =>
        simp only [scanFrom, List.length_cons]
        rw [ih]
  exact hlength 0 initialDeque schedule.windows

/-- Starting from a valid prior-window state, every later monotone update in `windows` is valid. -/
private theorem scanFrom_valid_at_of_valid (stream : Stream α)
    {oldWindow : Window stream.length} {q : Deque}
    (hq : Valid stream oldWindow q) (windows : List (Window stream.length))
    (hleft : (oldWindow :: windows).Pairwise (fun a b => a.left ≤ b.left))
    (hright : (oldWindow :: windows).Pairwise (fun a b => a.right ≤ b.right))
    {k : ℕ} (hk : k < windows.length) :
    ∃ step, (scanFrom stream oldWindow.right q windows)[k]? = some step ∧
      step.window = windows.get ⟨k, hk⟩ ∧ Valid stream step.window step.after := by
  induction windows generalizing oldWindow q k with
  | nil => simp at hk
  | cons window windows ih =>
      let step := update stream oldWindow.right window q
      have hleft' := List.pairwise_cons.mp hleft
      have hright' := List.pairwise_cons.mp hright
      have hstep : Valid stream window step.after := by
        exact update_preserves hq (hleft'.1 window (by simp)) (hright'.1 window (by simp))
      cases k with
      | zero =>
          refine ⟨step, ?_, ?_, hstep⟩
          · simp [scanFrom, step]
          · simp [step, update]
      | succ k =>
          have hk' : k < windows.length := by simpa using hk
          obtain ⟨later, hlater, hwindow, hvalid⟩ :=
            ih hstep hleft'.2 hright'.2 hk'
          refine ⟨later, ?_, ?_, hvalid⟩
          · simpa [scanFrom, step] using hlater
          · simpa using hwindow

/-- At every schedule position, the scan contains the corresponding window and a deque satisfying
the full invariant for that window. -/
theorem scan_valid_at (stream : Stream α) (schedule : Schedule stream.length)
    {k : ℕ} (hk : k < schedule.steps) :
    ∃ step, (scan stream schedule)[k]? = some step ∧
      step.window = schedule.windows.get ⟨k, hk⟩ ∧
      Valid stream step.window step.after := by
  let emptyWindow : Window stream.length :=
    { left := 0, right := 0, left_le_right := le_rfl,
      right_le_length := Nat.zero_le _ }
  have hinitial : Valid stream emptyWindow initialDeque := by
    exact initialDeque_validAt stream
  have hleft : (emptyWindow :: schedule.windows).Pairwise
      (fun a b => a.left ≤ b.left) := by
    rw [List.pairwise_cons]
    exact ⟨by simp [emptyWindow], schedule.left_mono⟩
  have hright : (emptyWindow :: schedule.windows).Pairwise
      (fun a b => a.right ≤ b.right) := by
    rw [List.pairwise_cons]
    exact ⟨by simp [emptyWindow], schedule.right_mono⟩
  simpa [scan, Schedule.steps, emptyWindow] using
    scanFrom_valid_at_of_valid stream hinitial schedule.windows hleft hright hk

/-- At every nonempty scheduled window, the scan returns a deque head that is active and maximizes
the stream value throughout that window. -/
theorem scan_head_argmax (stream : Stream α) (schedule : Schedule stream.length)
    {k : ℕ} (hk : k < schedule.steps)
    (hne : (schedule.windows.get ⟨k, hk⟩).left <
      (schedule.windows.get ⟨k, hk⟩).right) :
    ∃ step head tail,
      (scan stream schedule)[k]? = some step ∧
      step.window = schedule.windows.get ⟨k, hk⟩ ∧
      step.after = head :: tail ∧ Active step.window head ∧
      ∀ i, Active step.window i → stream.value i ≤ stream.value head := by
  obtain ⟨step, hstep, hwindow, hvalid⟩ := scan_valid_at stream schedule hk
  have hne_step : step.window.left < step.window.right := by
    simpa [hwindow] using hne
  obtain ⟨head, tail, hafter, hactive, hmax⟩ := hvalid.head_argmax hne_step
  exact ⟨step, head, tail, hstep, hwindow, hafter, hactive, hmax⟩

/-- [A finite stream](hyp:stream), [its monotone window schedule](hyp:schedule),
[a valid schedule position](hyp:hk), and [a nonempty window at that position](hyp:hne) ensure that
[the recorded head is an active argmax whose value is the window maximum](goal). -/
theorem scan_head_value_eq_windowMax (stream : Stream α)
    (schedule : Schedule stream.length) {k : ℕ} (hk : k < schedule.steps)
    (hne : (schedule.windows.get ⟨k, hk⟩).left <
      (schedule.windows.get ⟨k, hk⟩).right) :
    ∃ step head tail,
      (scan stream schedule)[k]? = some step ∧
      step.window = schedule.windows.get ⟨k, hk⟩ ∧
      step.after = head :: tail ∧ Active step.window head ∧
      stream.value head = windowMax stream (schedule.windows.get ⟨k, hk⟩) hne ∧
      ∀ i, Active step.window i → stream.value i ≤ stream.value head := by
  obtain ⟨step, hstep, hwindow, hvalid⟩ := scan_valid_at stream schedule hk
  have hne_step : step.window.left < step.window.right := by
    simpa [hwindow] using hne
  obtain ⟨head, tail, hafter, hactive, hvalue, hmax⟩ :=
    hvalid.head_value_eq_windowMax hne_step
  refine ⟨step, head, tail, hstep, hwindow, hafter, hactive, ?_, hmax⟩
  simpa [hwindow] using hvalue

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque

/-!
# Trace accounting and linear resource bounds

Exact event lists make the amortized proof explicit.  Each pushed stream index is unique, every pop
is charged to a prior unique push, the final deque contains the unpopped pushes, and therefore all
deque mutations are linear in stream length.  Pointwise storage is bounded by window width.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- The aggregate push log concatenates the pushed indices from every step of a fixed stream
trace. -/
def TracePushed (stream : Stream α) (trace : List (StepTrace stream)) : List ℕ :=
  trace.flatMap StepTrace.pushed

/-- The aggregate front-pop log concatenates the front-expired indices from every step. -/
def TraceFrontPopped (stream : Stream α) (trace : List (StepTrace stream)) : List ℕ :=
  trace.flatMap StepTrace.frontPopped

/-- The aggregate back-pop log concatenates the back-pruned indices from every step. -/
def TraceBackPopped (stream : Stream α) (trace : List (StepTrace stream)) : List ℕ :=
  trace.flatMap StepTrace.backPopped

/-- The number of deque mutations is the number of pushes plus front pops plus back pops. -/
def dequeOperations (stream : Stream α) (trace : List (StepTrace stream)) : ℕ :=
  (TracePushed stream trace).length + (TraceFrontPopped stream trace).length +
    (TraceBackPopped stream trace).length

/-- Total scan cost adds one unit of fixed bookkeeping per scheduled window to the deque mutation
count. -/
def scanCost (stream : Stream α) (schedule : Schedule stream.length) : ℕ :=
  schedule.steps + dequeOperations stream (scan stream schedule)

/-- The peak number of stored deque indices is the maximum after-state length across the trace. -/
def peakStored (stream : Stream α) (trace : List (StepTrace stream)) : ℕ :=
  (trace.map (fun step => step.after.length)).foldl max 0

/-- The state left after processing a suffix of windows. -/
private def scanFromFinal (stream : Stream α) : ℕ → Deque →
    List (Window stream.length) → Deque
  | _, q, [] => q
  | oldRight, q, window :: windows =>
      scanFromFinal stream window.right (update stream oldRight window q).after windows

/-- Exact multiplicity conservation for a batch of pushes. -/
private theorem pushAll_count_conservation (stream : Stream α) (q : Deque)
    (indices : List ℕ) (i : ℕ) :
    q.count i + indices.count i = (pushAll stream q indices).state.count i +
      (pushAll stream q indices).backPopped.count i := by
  induction indices generalizing q with
  | nil => simp [pushAll]
  | cons j js ih =>
      have hsplit : q.count i = (pruneBack stream q j).count i +
          (prunedBack stream q j).count i := by
        rw [← List.count_append, pruneBack_append_prunedBack]
      have hrec := ih (push stream q j)
      calc
        q.count i + (j :: js).count i =
            ((pruneBack stream q j).count i + (if j == i then 1 else 0) + js.count i) +
              (prunedBack stream q j).count i := by simp only [List.count_cons]; omega
        _ = (push stream q j).count i + js.count i +
              (prunedBack stream q j).count i := by
                by_cases hji : j = i <;> simp [push, hji]
        _ = (pushAll stream (push stream q j) js).state.count i +
              (pushAll stream (push stream q j) js).backPopped.count i +
                (prunedBack stream q j).count i := by omega
        _ = (pushAll stream q (j :: js)).state.count i +
              (pushAll stream q (j :: js)).backPopped.count i := by
                simp [pushAll, Nat.add_comm, Nat.add_left_comm]

/-- Exact multiplicity conservation over an arbitrary scan suffix. -/
private theorem scanFrom_count_conservation (stream : Stream α) (oldRight : ℕ)
    (q : Deque) (windows : List (Window stream.length)) (i : ℕ) :
    q.count i + (TracePushed stream (scanFrom stream oldRight q windows)).count i =
      (TraceFrontPopped stream (scanFrom stream oldRight q windows)).count i +
        (TraceBackPopped stream (scanFrom stream oldRight q windows)).count i +
          (scanFromFinal stream oldRight q windows).count i := by
  induction windows generalizing oldRight q with
  | nil => simp [scanFrom, scanFromFinal, TracePushed, TraceFrontPopped,
      TraceBackPopped]
  | cons window windows ih =>
      let step := update stream oldRight window q
      have hexp : q.count i = step.frontPopped.count i + step.afterExpiration.count i := by
        dsimp [step, update]
        rw [← List.count_append, expiredFront_append_expireFront]
      have hbatch : step.afterExpiration.count i + step.pushed.count i =
          step.after.count i + step.backPopped.count i := by
        dsimp [step]
        rw [update_pushed]
        change (expireFront window.left q).count i +
            (List.range' (max oldRight window.left)
              (window.right - max oldRight window.left)).count i = _
        exact pushAll_count_conservation stream _ _ i
      have hrec := ih window.right step.after
      simp only [scanFrom, scanFromFinal, TracePushed, TraceFrontPopped,
        TraceBackPopped, List.flatMap_cons, List.count_append]
      change q.count i + (step.pushed.count i +
          (TracePushed stream
            (scanFrom stream window.right step.after windows)).count i) =
        (step.frontPopped.count i +
            (TraceFrontPopped stream
              (scanFrom stream window.right step.after windows)).count i) +
          (step.backPopped.count i +
            (TraceBackPopped stream
              (scanFrom stream window.right step.after windows)).count i) +
            (scanFromFinal stream window.right step.after windows).count i
      omega

/-- Every index pushed by a scan suffix is at least its starting right endpoint. -/
private theorem mem_scanFrom_pushed_ge (stream : Stream α) (oldRight : ℕ) (q : Deque)
    (windows : List (Window stream.length))
    (hOld : ∀ w ∈ windows, oldRight ≤ w.right)
    (hright : windows.Pairwise (fun a b => a.right ≤ b.right)) {i : ℕ}
    (hi : i ∈ TracePushed stream (scanFrom stream oldRight q windows)) : oldRight ≤ i := by
  induction windows generalizing oldRight q with
  | nil => simp [scanFrom, TracePushed] at hi
  | cons window windows ih =>
      have hp := List.pairwise_cons.mp hright
      have hold := hOld window (by simp)
      simp only [scanFrom, TracePushed, List.flatMap_cons, List.mem_append] at hi
      rcases hi with hi | hi
      · rw [update_pushed] at hi
        exact le_trans (le_max_left _ _) (List.mem_range'_1.mp hi).1
      · exact le_trans hold
          (ih window.right (update stream oldRight window q).after hp.1 hp.2 hi)

/-- Under nondecreasing right endpoints, all indices pushed by a scan suffix are distinct. -/
private theorem scanFrom_pushed_nodup (stream : Stream α) (oldRight : ℕ) (q : Deque)
    (windows : List (Window stream.length))
    (hOld : ∀ w ∈ windows, oldRight ≤ w.right)
    (hright : windows.Pairwise (fun a b => a.right ≤ b.right)) :
    (TracePushed stream (scanFrom stream oldRight q windows)).Nodup := by
  induction windows generalizing oldRight q with
  | nil => simp [scanFrom, TracePushed]
  | cons window windows ih =>
      have hp := List.pairwise_cons.mp hright
      have hold : oldRight ≤ window.right := hOld window (by simp)
      have hstart : max oldRight window.left ≤ window.right :=
        max_le hold window.left_le_right
      have htail : ∀ w ∈ windows, window.right ≤ w.right := hp.1
      have hnTail := ih window.right (update stream oldRight window q).after htail hp.2
      simp only [scanFrom, TracePushed, List.flatMap_cons]
      rw [List.nodup_append]
      refine ⟨?_, hnTail, ?_⟩
      · rw [update_pushed]
        exact List.nodup_range'
      · intro a ha b hb hab
        rw [update_pushed] at ha
        have ha' := List.mem_range'_1.mp ha
        have hb' := mem_scanFrom_pushed_ge stream window.right
          (update stream oldRight window q).after windows htail hp.2 hb
        subst b
        omega

/-- Every pushed index lies in the finite stream prefix. -/
private theorem mem_scanFrom_pushed_lt_length (stream : Stream α) (oldRight : ℕ) (q : Deque)
    (windows : List (Window stream.length)) {i : ℕ}
    (hi : i ∈ TracePushed stream (scanFrom stream oldRight q windows)) :
    i < stream.length := by
  induction windows generalizing oldRight q with
  | nil => simp [scanFrom, TracePushed] at hi
  | cons window windows ih =>
      simp only [scanFrom, TracePushed, List.flatMap_cons, List.mem_append] at hi
      rcases hi with hi | hi
      · rw [update_pushed] at hi
        have hm := List.mem_range'_1.mp hi
        by_cases hs : max oldRight window.left ≤ window.right
        · exact lt_of_lt_of_le (by simpa [Nat.add_sub_of_le hs] using hm.2)
            window.right_le_length
        · have hz : window.right - max oldRight window.left = 0 :=
            Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hs)
          simp [hz] at hi
      · exact ih window.right (update stream oldRight window q).after hi

/-- Exact multiplicity conservation for a complete scan. -/
private theorem scan_count_conservation (stream : Stream α)
    (schedule : Schedule stream.length) (i : ℕ) :
    (TracePushed stream (scan stream schedule)).count i =
      (TraceFrontPopped stream (scan stream schedule)).count i +
        (TraceBackPopped stream (scan stream schedule)).count i +
          (scanFromFinal stream 0 initialDeque schedule.windows).count i := by
  simpa [scan, initialDeque] using
    scanFrom_count_conservation stream 0 initialDeque schedule.windows i

/-- Taking a fold maximum preserves any common upper bound. -/
private theorem foldl_max_le_of_forall (xs : List ℕ) (acc bound : ℕ)
    (hacc : acc ≤ bound) (hxs : ∀ x ∈ xs, x ≤ bound) :
    xs.foldl max acc ≤ bound := by
  induction xs generalizing acc with
  | nil => simpa
  | cons x xs ih =>
      apply ih (max acc x) (max_le hacc (hxs x (by simp)))
      intro y hy
      exact hxs y (by simp [hy])

/-- Every stream index appears in the aggregate scan push log at most once. -/
theorem scan_push_count_le_one (stream : Stream α) (schedule : Schedule stream.length) (i : ℕ) :
    (TracePushed stream (scan stream schedule)).count i ≤ 1 := by
  apply (List.nodup_iff_count_le_one.mp ?_) i
  unfold scan
  apply scanFrom_pushed_nodup stream 0 initialDeque schedule.windows
  · intro w hw
    exact Nat.zero_le _
  · exact schedule.right_mono

/-- Every stream index appears in the aggregate scan front-pop log at most once. -/
theorem scan_front_pop_count_le_one (stream : Stream α)
    (schedule : Schedule stream.length) (i : ℕ) :
    (TraceFrontPopped stream (scan stream schedule)).count i ≤ 1 := by
  have hp := scan_push_count_le_one stream schedule i
  have hc := scan_count_conservation stream schedule i
  omega

/-- Every stream index appears in the aggregate scan back-pop log at most once. -/
theorem scan_back_pop_count_le_one (stream : Stream α)
    (schedule : Schedule stream.length) (i : ℕ) :
    (TraceBackPopped stream (scan stream schedule)).count i ≤ 1 := by
  have hp := scan_push_count_le_one stream schedule i
  have hc := scan_count_conservation stream schedule i
  omega

/-- No index is both front-popped and back-popped during one scan. -/
theorem scan_pop_logs_disjoint (stream : Stream α) (schedule : Schedule stream.length) :
    List.Disjoint (TraceFrontPopped stream (scan stream schedule))
      (TraceBackPopped stream (scan stream schedule)) := by
  rw [List.disjoint_iff_ne]
  intro i hi j hj hij
  subst j
  have hfi : 0 < (TraceFrontPopped stream (scan stream schedule)).count i :=
    List.count_pos_iff.mpr hi
  have hbi : 0 < (TraceBackPopped stream (scan stream schedule)).count i :=
    List.count_pos_iff.mpr hj
  have hp := scan_push_count_le_one stream schedule i
  have hc := scan_count_conservation stream schedule i
  omega

/-- Every index popped during a scan belongs to the unique aggregate push log. -/
theorem scan_popped_was_pushed (stream : Stream α) (schedule : Schedule stream.length) {i : ℕ}
    (hi : i ∈ TraceFrontPopped stream (scan stream schedule) ∨
      i ∈ TraceBackPopped stream (scan stream schedule)) :
    i ∈ TracePushed stream (scan stream schedule) := by
  apply List.count_pos_iff.mp
  have hc := scan_count_conservation stream schedule i
  rcases hi with hi | hi
  · have : 0 < (TraceFrontPopped stream (scan stream schedule)).count i :=
      List.count_pos_iff.mpr hi
    omega
  · have : 0 < (TraceBackPopped stream (scan stream schedule)).count i :=
      List.count_pos_iff.mpr hi
    omega

/-- The total number of front and back pops is at most the total number of pushes. -/
theorem scan_total_pops_le_pushes (stream : Stream α) (schedule : Schedule stream.length) :
    (TraceFrontPopped stream (scan stream schedule)).length +
      (TraceBackPopped stream (scan stream schedule)).length ≤
        (TracePushed stream (scan stream schedule)).length := by
  let popped := TraceFrontPopped stream (scan stream schedule) ++
    TraceBackPopped stream (scan stream schedule)
  have hnodup : popped.Nodup := by
    rw [List.nodup_iff_count_le_one]
    intro i
    have hp := scan_push_count_le_one stream schedule i
    have hc := scan_count_conservation stream schedule i
    simp only [popped, List.count_append]
    omega
  have hsubset : popped ⊆ TracePushed stream (scan stream schedule) := by
    intro i hi
    apply scan_popped_was_pushed stream schedule
    simpa [popped] using hi
  have hlen := hnodup.length_le_of_subset hsubset
  simpa [popped] using hlen

/-- The total number of pushes is at most the finite stream length. -/
theorem scan_total_pushes_le_length (stream : Stream α)
    (schedule : Schedule stream.length) :
    (TracePushed stream (scan stream schedule)).length ≤ stream.length := by
  have hnodup : (TracePushed stream (scan stream schedule)).Nodup := by
    unfold scan
    apply scanFrom_pushed_nodup stream 0 initialDeque schedule.windows
    · intro w hw
      exact Nat.zero_le _
    · exact schedule.right_mono
  have hsubset : TracePushed stream (scan stream schedule) ⊆
      List.range stream.length := by
    intro i hi
    rw [List.mem_range]
    exact mem_scanFrom_pushed_lt_length stream 0 initialDeque schedule.windows hi
  simpa using hnodup.length_le_of_subset hsubset

/-- All deque mutations in a scan are bounded by twice the stream length. -/
theorem dequeOperations_le_two_mul_length (stream : Stream α)
    (schedule : Schedule stream.length) :
    dequeOperations stream (scan stream schedule) ≤ 2 * stream.length := by
  have hpops := scan_total_pops_le_pushes stream schedule
  have hpush := scan_total_pushes_le_length stream schedule
  unfold dequeOperations
  omega

/-- [A finite stream](hyp:stream) and [a monotone window schedule](hyp:schedule) ensure that
[the cost is at most twice the stream length plus its number of windows](goal). -/
theorem scanCost_le (stream : Stream α) (schedule : Schedule stream.length) :
    scanCost stream schedule ≤ 2 * stream.length + schedule.steps := by
  have h := dequeOperations_le_two_mul_length stream schedule
  unfold scanCost
  omega

/-- Any valid deque stores at most the width of its active window. -/
theorem Valid.length_le_windowWidth {stream : Stream α}
    {window : Window stream.length} {q : Deque} (hq : Valid stream window q) :
    q.length ≤ window.right - window.left := by
  have hn : q.Nodup := ValidAt.nodup hq
  rw [← List.toFinset_card_of_nodup hn, ← Window.card_indexFinset window]
  apply Finset.card_le_card
  intro i hi
  rw [Window.mem_indexFinset_iff]
  exact (hq.active i (by simpa using hi)).1

/-- At every scheduled position, the scan state uses no more cells than that position's active
window width. -/
theorem scan_memory_le_windowWidth (stream : Stream α)
    (schedule : Schedule stream.length) {k : ℕ} (hk : k < schedule.steps) :
    ∃ step, (scan stream schedule)[k]? = some step ∧
      step.after.length ≤ (schedule.windows.get ⟨k, hk⟩).right -
        (schedule.windows.get ⟨k, hk⟩).left := by
  obtain ⟨step, hstep, hwindow, hvalid⟩ := scan_valid_at stream schedule hk
  refine ⟨step, hstep, ?_⟩
  have hlen := Valid.length_le_windowWidth hvalid
  simpa [hwindow] using hlen

/-- Peak stored deque memory over a scan is bounded by the finite stream length. -/
theorem peakStored_le_length (stream : Stream α) (schedule : Schedule stream.length) :
    peakStored stream (scan stream schedule) ≤ stream.length := by
  unfold peakStored
  apply foldl_max_le_of_forall _ _ _ (Nat.zero_le _)
  intro n hn
  simp only [List.mem_map] at hn
  obtain ⟨step, hstep, rfl⟩ := hn
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hstep
  have hk' : k < schedule.steps := by simpa [length_scan stream schedule] using hk
  obtain ⟨found, hfound, hwindow, hvalid⟩ := scan_valid_at stream schedule hk'
  have heq : found = step := by
    apply Option.some.inj
    rw [← hfound, List.getElem?_eq_getElem hk, hget]
  subst found
  have hwidth := Valid.length_le_windowWidth hvalid
  have hright := step.window.right_le_length
  omega

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque

/-!
# Fixed finite families of monotone-window passes

This module packages a constant number of independent schedules over the same finite stream.  It
exports per-pass correctness and the sum of the linear per-pass cost bounds, which is the interface
needed by algorithms that run a fixed collection of monotone scans.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- A family of `passes` monotone-window scans shares one finite stream but may use a different
window schedule in each pass. -/
structure FixedPasses (stream : Stream α) (passes : ℕ) where
  schedule : Fin passes → Schedule stream.length

/-- Total cost of a fixed family of passes is the sum of the individual scan costs. -/
def FixedPasses.totalCost {stream : Stream α} {passes : ℕ}
    (family : FixedPasses stream passes) : ℕ :=
  ∑ p, scanCost stream (family.schedule p)

/-- The total number of scheduled windows across fixed passes is the sum of their schedule
lengths. -/
def FixedPasses.totalSteps {stream : Stream α} {passes : ℕ}
    (family : FixedPasses stream passes) : ℕ :=
  ∑ p, (family.schedule p).steps

/-- Every nonempty window in every pass has a scan head that is active, is an argmax, and has value
equal to that window's finite maximum. -/
theorem FixedPasses.head_value_eq_windowMax {stream : Stream α} {passes : ℕ}
    (family : FixedPasses stream passes) (p : Fin passes) {k : ℕ}
    (hk : k < (family.schedule p).steps)
    (hne : ((family.schedule p).windows.get ⟨k, hk⟩).left <
      ((family.schedule p).windows.get ⟨k, hk⟩).right) :
    ∃ step head tail,
      (scan stream (family.schedule p))[k]? = some step ∧
      step.window = (family.schedule p).windows.get ⟨k, hk⟩ ∧
      step.after = head :: tail ∧ Active step.window head ∧
      stream.value head =
        windowMax stream ((family.schedule p).windows.get ⟨k, hk⟩) hne ∧
      ∀ i, Active step.window i → stream.value i ≤ stream.value head := by
  exact scan_head_value_eq_windowMax stream (family.schedule p) hk hne

/-- [A fixed family of monotone-window passes](hyp:family) ensures that [its total cost is at most
twice the pass count times the stream length plus its total number of scheduled windows](goal). -/
theorem FixedPasses.totalCost_le {stream : Stream α} {passes : ℕ}
    (family : FixedPasses stream passes) :
    family.totalCost ≤ 2 * passes * stream.length + family.totalSteps := by
  unfold FixedPasses.totalCost FixedPasses.totalSteps
  calc
    ∑ p, scanCost stream (family.schedule p) ≤
        ∑ p, (2 * stream.length + (family.schedule p).steps) := by
      classical
      induction (Finset.univ : Finset (Fin passes)) using Finset.induction_on with
      | empty => simp
      | @insert p s hp ih =>
          simp only [Finset.sum_insert hp]
          exact Nat.add_le_add (scanCost_le stream (family.schedule p)) ih
    _ = 2 * passes * stream.length + ∑ p, (family.schedule p).steps := by
      simp [Finset.sum_add_distrib, Nat.mul_comm, Nat.mul_left_comm]

/-- Each state in each fixed pass stores at most its own active-window width. -/
theorem FixedPasses.memory_le_windowWidth {stream : Stream α} {passes : ℕ}
    (family : FixedPasses stream passes) (p : Fin passes) {k : ℕ}
    (hk : k < (family.schedule p).steps) :
    ∃ step, (scan stream (family.schedule p))[k]? = some step ∧
      step.after.length ≤ ((family.schedule p).windows.get ⟨k, hk⟩).right -
        ((family.schedule p).windows.get ⟨k, hk⟩).left := by
  exact scan_memory_le_windowWidth stream (family.schedule p) hk

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque
