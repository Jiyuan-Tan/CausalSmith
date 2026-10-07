module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Finite dependent transcript histories

This module provides dependent finite histories, their product measurable spaces, and the
basic operations that restrict, extend, or split a transcript.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- Given [an output family](hyp:Z), [a history length](hyp:k), and [evidence that the length
does not exceed the horizon](hyp:hk), [a dependent history](goal) records one output at each
earlier stage. It is [given by the dependent function space](step:1) indexed by the first `k`
stages. -/
def History {n : ℕ} (Z : Fin n → Type*) (k : ℕ) (hk : k ≤ n) : Type _ :=
  (j : Fin k) → Z (Fin.castLE hk j)

/-- Given [measurable output spaces](hyp:mZ), [a history length](hyp:k), and [evidence that it
lies within the output horizon](hyp:hk), [the measurable structure on the dependent history](goal)
is [given by the product σ-algebra of its coordinates](step:1). -/
instance historyMeasurableSpace {n : ℕ} {Z : Fin n → Type*}
    [mZ : ∀ i, MeasurableSpace (Z i)] (k : ℕ) (hk : k ≤ n) :
    MeasurableSpace (History Z k hk) := by
  unfold History
  letI : ∀ j : Fin k, MeasurableSpace (Z (Fin.castLE hk j)) := fun j => mZ _
  infer_instance

/-- Given [an output family](hyp:Z), [a complete dependent transcript](goal) is [given by a
history spanning the whole horizon](step:1). -/
abbrev Transcript {n : ℕ} (Z : Fin n → Type*) := History Z n le_rfl

/-- Given [a prefix bound](hyp:hk) and [a complete transcript](hyp:u), [the requested prefix
history](goal) is [given by retaining exactly its first coordinates](step:1). -/
def take {n k : ℕ} {Z : Fin n → Type*} (hk : k ≤ n)
    (u : Transcript Z) : History Z k hk :=
  fun j => u (Fin.castLE hk j)

/-- Given [evidence that stage k + 1 lies within the horizon](hyp:hk), [the next output
index](goal) is [the zero-based position k, which is the position of the (k + 1)-th
output](step:1). -/
def nextIndex {n k : ℕ} (hk : k + 1 ≤ n) : Fin n :=
  ⟨k, Nat.lt_of_succ_le hk⟩

/-- Given [a valid successor bound](hyp:hk), [a preceding history](hyp:u), and [its next
output](hyp:z), [the extended history](goal) is [given by appending that output](step:1). -/
def snoc {n k : ℕ} {Z : Fin n → Type*} (hk : k + 1 ≤ n)
    (u : History Z k (Nat.le_of_succ_le hk)) (z : Z (nextIndex hk)) :
    History Z (k + 1) hk :=
  Fin.snoc u z

/-- Given [a valid successor bound](hyp:hk) and [a nonempty history](hyp:u), [its preceding
history](goal) is [given by removing the final coordinate](step:1). -/
def init {n k : ℕ} {Z : Fin n → Type*} (hk : k + 1 ≤ n)
    (u : History Z (k + 1) hk) : History Z k (Nat.le_of_succ_le hk) :=
  Fin.init u

/-- Given [a valid successor bound](hyp:hk) and [a nonempty history](hyp:u), [its final
output](goal) is [given by its last coordinate](step:1). -/
def last {n k : ℕ} {Z : Fin n → Type*} (hk : k + 1 ≤ n)
    (u : History Z (k + 1) hk) : Z (nextIndex hk) :=
  u (Fin.last k)

end Causalean.Mathlib.Probability.Kernel.FiniteSequence
