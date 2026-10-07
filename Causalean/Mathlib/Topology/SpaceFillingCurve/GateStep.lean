module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.GrayGates

/-!
# Gates across neighboring dyadic cells

An oriented path through the children of one dyadic cell needs an exit vertex
that meets the next parent's entry vertex. This module isolates that local
choice from the recursive assembly of finite traversals.
-/

@[expose] public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [two integer grid points](hyp:u,v), [face adjacency](goal) is [the condition that one coordinate differs by one and the others agree](step:1). -/
def FaceAdjacentGrid {d : ℕ} (u v : Fin d → ℕ) : Prop :=
  ∃ i : Fin d, (u i + 1 = v i ∨ v i + 1 = u i) ∧
    ∀ j : Fin d, j ≠ i → u j = v j

/-- Given [a parent grid cell and binary child vertex](hyp:u,b), [the child-grid coordinate](goal) is [twice the parent coordinate plus the child bit](step:1). -/
def childGridCoord {d : ℕ} (u : Fin d → ℕ) (b : Fin d → Bool) : Fin d → ℕ :=
  fun i => 2 * u i + if b i then 1 else 0

/-- Given [a dimension](hyp:d) of [at least two](hyp:hd), [two face-adjacent parent cells](hyp:u,v,huv), and [an entry vertex](hyp:a),
[there are an exit vertex differing from the entry vertex in exactly one coordinate and a binary vertex of the second cell such that
the exit child of the first cell is face-adjacent to that child of the second cell](goal). -/
theorem exists_adjacent_child_gate (d : ℕ) (hd : 2 ≤ d)
    (u v : Fin d → ℕ) (huv : FaceAdjacentGrid u v)
    (a : Fin d → Bool) :
    ∃ b c : Fin d → Bool,
      FaceAdjacentVertex a b ∧
      FaceAdjacentGrid (childGridCoord u b) (childGridCoord v c) := by
  classical
  obtain ⟨i, hi, hsame⟩ := huv
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨j, hji⟩ := exists_ne i
  have hij : i ≠ j := Ne.symm hji
  rcases hi with hforward | hbackward
  · by_cases hai : a i = true
    · let b : Fin d → Bool := fun k => if k = j then !a k else a k
      let c : Fin d → Bool := fun k => if k = i then false else b k
      refine ⟨b, c, ?_, ?_⟩
      · unfold FaceAdjacentVertex
        refine ⟨j, ?_, ?_⟩
        · simp [b]
        · intro k hk
          simp [b, hk]
      · unfold FaceAdjacentGrid
        refine ⟨i, ?_, ?_⟩
        · simp [childGridCoord, b, c, hij, hai]
          omega
        · intro k hk
          simp [childGridCoord, b, c, hk, hsame k hk]
    · let b : Fin d → Bool := fun k => if k = i then true else a k
      let c : Fin d → Bool := fun k => if k = i then false else b k
      refine ⟨b, c, ?_, ?_⟩
      · unfold FaceAdjacentVertex
        refine ⟨i, ?_, ?_⟩
        · simp [b, hai]
        · intro k hk
          simp [b, hk]
      · unfold FaceAdjacentGrid
        refine ⟨i, ?_, ?_⟩
        · simp [childGridCoord, b, c]
          omega
        · intro k hk
          simp [childGridCoord, b, c, hk, hsame k hk]
  · by_cases hai : a i = false
    · let b : Fin d → Bool := fun k => if k = j then !a k else a k
      let c : Fin d → Bool := fun k => if k = i then true else b k
      refine ⟨b, c, ?_, ?_⟩
      · unfold FaceAdjacentVertex
        refine ⟨j, ?_, ?_⟩
        · simp [b]
        · intro k hk
          simp [b, hk]
      · unfold FaceAdjacentGrid
        refine ⟨i, ?_, ?_⟩
        · simp [childGridCoord, b, c, hij, hai]
          omega
        · intro k hk
          simp [childGridCoord, b, c, hk, hsame k hk]
    · let b : Fin d → Bool := fun k => if k = i then false else a k
      let c : Fin d → Bool := fun k => if k = i then true else b k
      refine ⟨b, c, ?_, ?_⟩
      · unfold FaceAdjacentVertex
        refine ⟨i, ?_, ?_⟩
        · simp [b, hai]
        · intro k hk
          simp [b, hk]
      · unfold FaceAdjacentGrid
        refine ⟨i, ?_, ?_⟩
        · simp [childGridCoord, b, c]
          omega
        · intro k hk
          simp [childGridCoord, b, c, hk, hsame k hk]

end Causalean.Mathlib.Topology.SpaceFillingCurve
