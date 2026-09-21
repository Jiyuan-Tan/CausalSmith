import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Update
import Mathlib.Data.Finset.Max

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
