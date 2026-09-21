import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Scan

/-!
# Trace accounting and linear resource bounds

Exact event lists make the amortized proof explicit.  Each pushed stream index is unique, every pop
is charged to a prior unique push, the final deque contains the unpopped pushes, and therefore all
deque mutations are linear in stream length.  Pointwise storage is bounded by window width.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- [A stream](hyp:stream) and [a scan trace](hyp:trace) determine [the aggregate push log](goal). -/
def TracePushed (stream : Stream α) (trace : List (StepTrace stream)) : List ℕ :=
  trace.flatMap StepTrace.pushed

/-- [A stream](hyp:stream) and [a scan trace](hyp:trace) determine [the aggregate front-pop log](goal). -/
def TraceFrontPopped (stream : Stream α) (trace : List (StepTrace stream)) : List ℕ :=
  trace.flatMap StepTrace.frontPopped

/-- [A stream](hyp:stream) and [a scan trace](hyp:trace) determine [the aggregate back-pop log](goal). -/
def TraceBackPopped (stream : Stream α) (trace : List (StepTrace stream)) : List ℕ :=
  trace.flatMap StepTrace.backPopped

/-- [A stream](hyp:stream) and [a scan trace](hyp:trace) determine [the total number of deque
mutations](goal). -/
def dequeOperations (stream : Stream α) (trace : List (StepTrace stream)) : ℕ :=
  (TracePushed stream trace).length + (TraceFrontPopped stream trace).length +
    (TraceBackPopped stream trace).length

/-- [A stream](hyp:stream) and [a monotone window schedule](hyp:schedule) determine [the scan
cost, including one bookkeeping unit per window](goal). -/
def scanCost (stream : Stream α) (schedule : Schedule stream.length) : ℕ :=
  schedule.steps + dequeOperations stream (scan stream schedule)

/-- [A stream](hyp:stream) and [a scan trace](hyp:trace) determine [the peak stored deque size](goal). -/
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

/-- [A stream](hyp:stream), [a monotone window schedule](hyp:schedule), and [an index](hyp:i)
ensure [that the index is pushed at most once in the aggregate scan log](goal). -/
theorem scan_push_count_le_one (stream : Stream α) (schedule : Schedule stream.length) (i : ℕ) :
    (TracePushed stream (scan stream schedule)).count i ≤ 1 := by
  apply (List.nodup_iff_count_le_one.mp ?_) i
  unfold scan
  apply scanFrom_pushed_nodup stream 0 initialDeque schedule.windows
  · intro w hw
    exact Nat.zero_le _
  · exact schedule.right_mono

/-- [A stream](hyp:stream), [a monotone window schedule](hyp:schedule), and [an index](hyp:i)
ensure [that the index is front-popped at most once in the aggregate scan log](goal). -/
theorem scan_front_pop_count_le_one (stream : Stream α)
    (schedule : Schedule stream.length) (i : ℕ) :
    (TraceFrontPopped stream (scan stream schedule)).count i ≤ 1 := by
  have hp := scan_push_count_le_one stream schedule i
  have hc := scan_count_conservation stream schedule i
  omega

/-- [A stream](hyp:stream), [a monotone window schedule](hyp:schedule), and [an index](hyp:i)
ensure [that the index is back-popped at most once in the aggregate scan log](goal). -/
theorem scan_back_pop_count_le_one (stream : Stream α)
    (schedule : Schedule stream.length) (i : ℕ) :
    (TraceBackPopped stream (scan stream schedule)).count i ≤ 1 := by
  have hp := scan_push_count_le_one stream schedule i
  have hc := scan_count_conservation stream schedule i
  omega

/-- [A stream](hyp:stream) and [a monotone window schedule](hyp:schedule) ensure [that no index
appears in both front-pop and back-pop logs](goal). -/
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

/-- [A stream](hyp:stream), [a monotone window schedule](hyp:schedule), and [an index recorded as
a front or back pop](hyp:hi) ensure [that the index was previously pushed](goal). -/
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

/-- [A stream](hyp:stream) and [a monotone window schedule](hyp:schedule) ensure [that total front
and back pops are no more numerous than total pushes](goal). -/
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

/-- [A stream](hyp:stream) and [a monotone window schedule](hyp:schedule) ensure [that total
pushes are at most the stream length](goal). -/
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

/-- [A stream](hyp:stream) and [a monotone window schedule](hyp:schedule) ensure [that total deque
mutations are at most twice the stream length](goal). -/
theorem dequeOperations_le_two_mul_length (stream : Stream α)
    (schedule : Schedule stream.length) :
    dequeOperations stream (scan stream schedule) ≤ 2 * stream.length := by
  have hpops := scan_total_pops_le_pushes stream schedule
  have hpush := scan_total_pushes_le_length stream schedule
  unfold dequeOperations
  omega

/-- [A stream](hyp:stream) and [a monotone window schedule](hyp:schedule) ensure [that scan cost
is at most twice stream length plus the number of scheduled windows](goal). -/
theorem scanCost_le (stream : Stream α) (schedule : Schedule stream.length) :
    scanCost stream schedule ≤ 2 * stream.length + schedule.steps := by
  have h := dequeOperations_le_two_mul_length stream schedule
  unfold scanCost
  omega

/-- [A valid bounded-window deque](hyp:hq) has [stored length at most its window width](goal). -/
theorem Valid.length_le_windowWidth {stream : Stream α}
    {window : Window stream.length} {q : Deque} (hq : Valid stream window q) :
    q.length ≤ window.right - window.left := by
  have hn : q.Nodup := ValidAt.nodup hq
  rw [← List.toFinset_card_of_nodup hn, ← Window.card_indexFinset window]
  apply Finset.card_le_card
  intro i hi
  rw [Window.mem_indexFinset_iff]
  exact (hq.active i (by simpa using hi)).1

/-- [A stream](hyp:stream), [a monotone window schedule](hyp:schedule), and [a valid schedule
position](hyp:hk) ensure [that the corresponding scan state stores no more indices than its
window width](goal). -/
theorem scan_memory_le_windowWidth (stream : Stream α)
    (schedule : Schedule stream.length) {k : ℕ} (hk : k < schedule.steps) :
    ∃ step, (scan stream schedule)[k]? = some step ∧
      step.after.length ≤ (schedule.windows.get ⟨k, hk⟩).right -
        (schedule.windows.get ⟨k, hk⟩).left := by
  obtain ⟨step, hstep, hwindow, hvalid⟩ := scan_valid_at stream schedule hk
  refine ⟨step, hstep, ?_⟩
  have hlen := Valid.length_le_windowWidth hvalid
  simpa [hwindow] using hlen

/-- [A stream](hyp:stream) and [a monotone window schedule](hyp:schedule) ensure [that peak deque
storage is at most the stream length](goal). -/
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
