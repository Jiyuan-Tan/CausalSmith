import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Correctness

/-!
# Folding updates across a monotone window schedule

This module runs the deque update over every scheduled window.  Its pointwise theorems return the
valid state, active head argmax, and exact maximum value at any requested schedule position.
-/

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- [A stream](hyp:stream) determines [the scan trace produced from a prior right endpoint, deque,
and list of windows](goal). -/
def scanFrom (stream : Stream α) : ℕ → Deque → List (Window stream.length) →
    List (StepTrace stream)
  | _, _, [] => []
  | oldRight, q, window :: windows =>
      let step := update stream oldRight window q
      step :: scanFrom stream window.right step.after windows

/-- [A stream](hyp:stream) and [a monotone window schedule](hyp:schedule) determine [the complete
scan trace from the empty initial state](goal). -/
def scan (stream : Stream α) (schedule : Schedule stream.length) : List (StepTrace stream) :=
  scanFrom stream 0 initialDeque schedule.windows

/-- [A stream](hyp:stream) and [a monotone window schedule](hyp:schedule) ensure [that the scan
has exactly one trace step for each scheduled window](goal). -/
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

/-- [A stream](hyp:stream), [a monotone window schedule](hyp:schedule), and [a valid schedule
position](hyp:hk) ensure [that the corresponding scan step has a valid deque for its window](goal). -/
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

/-- [A stream](hyp:stream), [a monotone window schedule](hyp:schedule), [a valid schedule
position](hyp:hk), and [a nonempty window at that position](hyp:hne) ensure [that the scan head
is active and maximizes the stream value in that window](goal). -/
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

/-- [A stream](hyp:stream), [a monotone window schedule](hyp:schedule), [a valid schedule
position](hyp:hk), and [a nonempty window at that position](hyp:hne) ensure [that the scan head
is an active argmax whose value equals the finite-window maximum](goal). -/
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
