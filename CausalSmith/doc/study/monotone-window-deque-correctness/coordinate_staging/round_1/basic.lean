import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Order.Interval.Finset.Nat

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
