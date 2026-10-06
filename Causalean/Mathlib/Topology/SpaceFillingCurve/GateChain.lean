module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.GateStep

/-!
# Compatible gates along a finite parent traversal

Local gates can be chosen successively along a face-adjacent path of parent
cells. The resulting binary entry and exit vertices determine the endpoints
of each child's reflected Gray path.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a dimension and level](hyp:d,n), [a dimension of at least two](hyp:hd), [a parent grid](hyp:parent),
[its consecutive-face adjacency](hyp:hadj), and [an initial entry vertex](hyp:first), [compatible child-grid entry and exit gates exist](goal). -/
theorem exists_compatible_child_gates (d n : ℕ) (hd : 2 ≤ d)
    (parent : Fin (2 ^ (d * n)) → Fin d → ℕ)
    (hadj : ∀ k l : Fin (2 ^ (d * n)), l.val = k.val + 1 →
      FaceAdjacentGrid (parent k) (parent l))
    (first : Fin d → Bool) :
    ∃ entry exit : Fin (2 ^ (d * n)) → Fin d → Bool,
      entry 0 = first ∧
      (∀ k, FaceAdjacentVertex (entry k) (exit k)) ∧
      (∀ k l : Fin (2 ^ (d * n)), l.val = k.val + 1 →
        FaceAdjacentGrid
          (childGridCoord (parent k) (exit k))
          (childGridCoord (parent l) (entry l))) := by
  classical
  let m := 2 ^ (d * n)
  let step (k : ℕ) (a : Fin d → Bool) :
      {bc : (Fin d → Bool) × (Fin d → Bool) //
        FaceAdjacentVertex a bc.1 ∧
        (∀ h : k + 1 < m,
          FaceAdjacentGrid
            (childGridCoord (parent (Fin.ofNat m k)) bc.1)
            (childGridCoord (parent (Fin.ofNat m (k + 1))) bc.2))} := by
    by_cases h : k + 1 < m
    · have hk : k < m := by omega
      have hvals : (Fin.ofNat m (k + 1)).val = (Fin.ofNat m k).val + 1 := by
        simp [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hk]
      have hex : ∃ bc : (Fin d → Bool) × (Fin d → Bool),
          FaceAdjacentVertex a bc.1 ∧
            FaceAdjacentGrid
              (childGridCoord (parent (Fin.ofNat m k)) bc.1)
              (childGridCoord (parent (Fin.ofNat m (k + 1))) bc.2) := by
        obtain ⟨b, c, hab, hbc⟩ :=
          exists_adjacent_child_gate d hd
            (parent (Fin.ofNat m k)) (parent (Fin.ofNat m (k + 1)))
            (hadj _ _ hvals) a
        exact ⟨(b, c), hab, hbc⟩
      let bc := Classical.choose hex
      exact ⟨bc, (Classical.choose_spec hex).1, fun _ => (Classical.choose_spec hex).2⟩
    · let i : Fin d := ⟨0, by omega⟩
      let b : Fin d → Bool := fun j => if j = i then !a j else a j
      refine ⟨(b, a), ?_, ?_⟩
      · unfold FaceAdjacentVertex
        refine ⟨i, ?_, ?_⟩
        · simp [b]
        · intro j hj
          simp [b, hj]
      · intro h'
        omega
  let entryNat : ℕ → Fin d → Bool :=
    Nat.rec first (fun k a => (step k a).1.2)
  let entry : Fin m → Fin d → Bool := fun k => entryNat k.val
  let exit : Fin m → Fin d → Bool := fun k => (step k.val (entryNat k.val)).1.1
  refine ⟨entry, exit, ?_, ?_, ?_⟩
  · simp [entry, entryNat]
  · intro k
    exact (step k.val (entryNat k.val)).2.1
  · intro k l hkl
    have hk : k.val + 1 < m := by omega
    have hnext : entryNat l.val = (step k.val (entryNat k.val)).1.2 := by
      rw [hkl]
    have hkfin : Fin.ofNat m k.val = k := by
      apply Fin.ext
      simp
    have hlfin : Fin.ofNat m (k.val + 1) = l := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt hk, hkl]
    simpa only [entry, exit, hkfin, hlfin, hnext] using
      (step k.val (entryNat k.val)).2.2 hk

end Causalean.Mathlib.Topology.SpaceFillingCurve
