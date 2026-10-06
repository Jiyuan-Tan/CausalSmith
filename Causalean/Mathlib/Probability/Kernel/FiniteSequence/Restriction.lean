module

public import Causalean.Mathlib.Probability.Kernel.FiniteSequence.Basic

/-!
# Restriction maps for finite dependent histories

This module provides measurable maps which forget later coordinates of dependent finite
histories and records their basic compatibility with transcript prefixes.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.Kernel.FiniteSequence

variable {n : ℕ} {Z : Fin n → Type*} [∀ i, MeasurableSpace (Z i)]

/-- Given [a target prefix bound](hyp:hk), [a source prefix bound](hyp:hl), [an ordering of the
two lengths](hyp:hkl), and [a source history](hyp:u), [the restricted history](goal) is [given
by retaining its first coordinates](step:1). -/
def restrictHistory {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) (hkl : k ≤ l)
    (u : History Z l hl) : History Z k hk :=
  fun i => u (Fin.castLE hkl i)

/-- Given [a target prefix bound](hyp:hk), [a source prefix bound](hyp:hl), and [an ordering of
the two lengths](hyp:hkl), [the restriction map is measurable](goal). -/
theorem measurable_restrictHistory {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n)
    (hkl : k ≤ l) : Measurable (restrictHistory (Z := Z) hk hl hkl) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply (Fin.castLE hkl i)

/-- Given [a prefix bound](hyp:hk) and [a history of that exact length](hyp:u), [restricting it
to the same length returns the original history](goal). -/
theorem restrictHistory_self {k : ℕ} (hk : k ≤ n)
    (u : History Z k hk) : restrictHistory hk hk le_rfl u = u := by
  funext i
  rfl

/-- Given [a target prefix bound](hyp:hk), [a successor source bound](hyp:hs), [an ordering of
the target and preceding source lengths](hyp:hkl), and [a successor history](hyp:u), [restricting
it factors through removal of the final coordinate](goal). -/
theorem restrictHistory_succ {k l : ℕ} (hk : k ≤ n) (hs : l + 1 ≤ n)
    (hkl : k ≤ l) (u : History Z (l + 1) hs) :
    restrictHistory hk hs (Nat.le_trans hkl (Nat.le_succ l)) u =
      restrictHistory hk (Nat.le_of_succ_le hs) hkl (init hs u) := by
  funext i
  rfl

/-- Given [a prefix bound](hyp:hk) and [a complete transcript](hyp:u), [restricting the
transcript agrees with taking its prefix](goal). -/
theorem restrictHistory_transcript {k : ℕ} (hk : k ≤ n)
    (u : Transcript Z) : restrictHistory hk le_rfl hk u = take hk u := by
  funext i
  rfl

end Causalean.Mathlib.Probability.Kernel.FiniteSequence
