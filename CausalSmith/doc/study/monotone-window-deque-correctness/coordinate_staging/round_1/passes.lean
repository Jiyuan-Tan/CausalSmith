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
