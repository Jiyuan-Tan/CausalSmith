module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.GateChain

/-!
# Compatible reflected Gray paths inside parent cells

The gate chain supplies adjacent entry and exit vertices in each parent cell.
This module turns those gates into Hamiltonian child paths, including the
face-adjacency condition between consecutive parent blocks.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a cube dimension and dyadic depth](hyp:d,n), [a dimension of at least two](hyp:hd),
[a parent grid](hyp:parent), and [face adjacency of consecutive parent cells](hyp:hadj),
[there is, for every parent cell, an ordering of its `2^d` binary child vertices that
visits each vertex exactly once with consecutive vertices differing in exactly one
coordinate, such that for consecutive parent cells the last child of the earlier parent
and the first child of the later parent are face-adjacent cells of the refined grid](goal). -/
theorem exists_compatible_child_paths (d n : ℕ) (hd : 2 ≤ d)
    (parent : Fin (2 ^ (d * n)) → Fin d → ℕ)
    (hadj : ∀ k l : Fin (2 ^ (d * n)), l.val = k.val + 1 →
      FaceAdjacentGrid (parent k) (parent l)) :
    ∃ path : Fin (2 ^ (d * n)) → Fin (2 ^ d) → Fin d → Bool,
      (∀ k, Function.Bijective (path k)) ∧
      (∀ k : Fin (2 ^ (d * n)), ∀ a b : Fin (2 ^ d), b.val = a.val + 1 →
        FaceAdjacentVertex (path k a) (path k b)) ∧
      (∀ k l : Fin (2 ^ (d * n)), l.val = k.val + 1 →
        FaceAdjacentGrid
          (childGridCoord (parent k) (path k (Fin.rev 0)))
          (childGridCoord (parent l) (path l 0))) := by
  classical
  obtain ⟨entry, exit, _, hgate, hbridge⟩ :=
    exists_compatible_child_gates d n hd parent hadj (fun _ => false)
  have hpaths : ∀ k : Fin (2 ^ (d * n)),
      ∃ p : Fin (2 ^ d) → Fin d → Bool,
        Function.Bijective p ∧
        (∀ a b : Fin (2 ^ d), b.val = a.val + 1 →
          FaceAdjacentVertex (p a) (p b)) ∧
        p 0 = entry k ∧ p (Fin.rev 0) = exit k := by
    intro k
    exact exists_grayPath_between_adjacent_vertices d (by omega)
      (entry k) (exit k) (hgate k)
  choose path hpath using hpaths
  refine ⟨path, (fun k => (hpath k).1),
    (fun k a b hab => (hpath k).2.1 a b hab), ?_⟩
  intro k l hkl
  rw [(hpath k).2.2.2, (hpath l).2.2.1]
  exact hbridge k l hkl

end Causalean.Mathlib.Topology.SpaceFillingCurve
