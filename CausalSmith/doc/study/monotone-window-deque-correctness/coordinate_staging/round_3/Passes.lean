import Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Accounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fixed finite families of monotone-window passes

This module packages a constant number of independent schedules over the same finite stream.  It
exports per-pass correctness and the sum of the linear per-pass cost bounds, which is the interface
needed by algorithms that run a fixed collection of monotone scans.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Algorithms.MonotoneWindowDeque

variable {α : Type*} [LinearOrder α]

/-- [A stream](hyp:stream) and [a finite pass count](hyp:passes) have a family of monotone-window
schedules, one for each pass. -/
structure FixedPasses (stream : Stream α) (passes : ℕ) where
  schedule : Fin passes → Schedule stream.length

/-- [A fixed family of passes](hyp:family) determines [the sum of its individual scan costs](goal). -/
def FixedPasses.totalCost {stream : Stream α} {passes : ℕ}
    (family : FixedPasses stream passes) : ℕ :=
  ∑ p, scanCost stream (family.schedule p)

/-- [A fixed family of passes](hyp:family) determines [its total number of scheduled windows](goal). -/
def FixedPasses.totalSteps {stream : Stream α} {passes : ℕ}
    (family : FixedPasses stream passes) : ℕ :=
  ∑ p, (family.schedule p).steps

/-- [A fixed family of passes](hyp:family), [a selected pass](hyp:p), [a valid position in that
pass](hyp:hk), and [a nonempty window there](hyp:hne) ensure [that the scan head is an active
argmax with the finite-window maximum value](goal). -/
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

/-- [A fixed family of passes](hyp:family) ensures [that its total cost is at most twice the pass
count times stream length plus its total scheduled-window count](goal). -/
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

/-- [A fixed family of passes](hyp:family), [a selected pass](hyp:p), and [a valid position in
that pass](hyp:hk) ensure [that the corresponding state stores no more than its window width](goal). -/
theorem FixedPasses.memory_le_windowWidth {stream : Stream α} {passes : ℕ}
    (family : FixedPasses stream passes) (p : Fin passes) {k : ℕ}
    (hk : k < (family.schedule p).steps) :
    ∃ step, (scan stream (family.schedule p))[k]? = some step ∧
      step.after.length ≤ ((family.schedule p).windows.get ⟨k, hk⟩).right -
        ((family.schedule p).windows.get ⟨k, hk⟩).left := by
  exact scan_memory_le_windowWidth stream (family.schedule p) hk

end Causalean.Mathlib.Algorithms.MonotoneWindowDeque
