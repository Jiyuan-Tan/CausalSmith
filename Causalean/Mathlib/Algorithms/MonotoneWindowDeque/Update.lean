import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque

/-!
# Window update and invariant preservation

This module combines front expiration with batch insertion of the newly entered right-endpoint
interval.  Its preservation results cover repeated endpoints, empty batches, empty windows, and
windows that become empty.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- [A stream](hyp:stream) has a step record containing its before and after deques and exact
push, front-pop, and back-pop event lists. -/
structure StepTrace (stream : Stream α) where
  oldRight : ℕ
  window : Window stream.length
  before : Deque
  afterExpiration : Deque
  after : Deque
  pushed : List ℕ
  frontPopped : List ℕ
  backPopped : List ℕ

/-- [A stream](hyp:stream), [the prior right endpoint](hyp:oldRight), [a new bounded window](hyp:window),
and [the prior deque](hyp:q) determine [the recorded monotone-deque update](goal), expiring the
front before inserting newly entered active indices. -/
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

/-- [A stream](hyp:stream), [a prior right endpoint](hyp:oldRight), [a new window](hyp:window), and
[a prior deque](hyp:q) have [an update push log equal to the newly entered active interval](goal). -/
theorem update_pushed (stream : Stream α) (oldRight : ℕ)
    (window : Window stream.length) (q : Deque) :
    (update stream oldRight window q).pushed =
      List.range' (max oldRight window.left) (window.right - max oldRight window.left) := by
  unfold update
  exact pushAll_pushed_eq _ _ _

/-- [A valid old raw-window deque](hyp:hq) and [a nondecreasing new left endpoint](hyp:hleft)
ensure [that front expiration preserves the full raw-window invariant](goal), including an empty
intermediate interval. -/
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

/-- [A valid raw-window deque](hyp:hq) remains [valid when its right endpoint is enlarged to at
least its left endpoint](goal). -/
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

/-- [A valid raw-window deque](hyp:hq), [a left endpoint no larger than the current right endpoint](hyp:hleft),
and [room for one more stream index](hyp:hbound) ensure [that pushing the right-boundary index
preserves the invariant for the enlarged window](goal). -/
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

/-- [A valid raw-window deque](hyp:hq), [a left endpoint no larger than the range start](hyp:hleft),
and [a range ending within the stream](hyp:hbound) ensure [that pushing the whole consecutive
range preserves the invariant](goal). -/
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

/-- [A valid deque after front expiration](hyp:hq), [a nondecreasing right endpoint](hyp:hright),
[a new endpoint within the stream](hyp:hbound), and [a valid new raw interval](hyp:hwindow) ensure
[that inserting newly entered active indices restores the invariant](goal). -/
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

/-- [A valid old-window deque](hyp:hq), [a nondecreasing left endpoint](hyp:hleft), and [a
nondecreasing right endpoint](hyp:hright) ensure [that one update produces a valid new-window
deque](goal). -/
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

/-- [A stream](hyp:stream) and [its first bounded window](hyp:window) ensure [that updating from
the empty initial interval produces a valid deque](goal). -/
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
