module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.TraversalCompactness

/-!
# Coherent dyadic cube traversals

A traversal orders every dyadic grid of the unit cube, respects parent cells,
and visits face-adjacent cells consecutively. The existence theorem is the
finite recursive Gray-order construction, including the orientation changes
needed for coherence between levels.
-/

@[expose] public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- A coherent face-adjacent order of all dyadic grids in dimension `d`.
At every level `n` it lists the `2^(dn)` cells of the grid with `2^n` cells
per side exactly once, consecutive cells in the list share a face, and each
consecutive block of `2^d` cells at level `n+1` consists of the children of
the corresponding level-`n` cell.

Here `cell n k i` is the `i`th integer coordinate of the `k`th visited cell
at level `n`. -/
structure DyadicTraversal (d : ℕ) where
  cell : ∀ n : ℕ, Fin (2 ^ (d * n)) → Fin d → Fin (2 ^ n)
  bijective : ∀ n, Function.Bijective (cell n)
  adjacent : ∀ n (k l : Fin (2 ^ (d * n))), l.val = k.val + 1 →
    ∃ i : Fin d,
      ((cell n k i).val + 1 = (cell n l i).val ∨
        (cell n l i).val + 1 = (cell n k i).val) ∧
      ∀ j : Fin d, j ≠ i → cell n k j = cell n l j
  nested : ∀ n (k : Fin (2 ^ (d * n))) (l : Fin (2 ^ (d * (n + 1)))),
    l.val / 2 ^ d = k.val →
    ∀ i : Fin d, (cell (n + 1) l i).val / 2 = (cell n k i).val

/-- Coherent traversals of every finite depth yield one traversal of all
dyadic grids. The proof extracts a consistent branch from the finitely
branching tree of finite cell orders. -/
theorem exists_dyadicTraversal_of_finite (d : ℕ)
    (hfinite : ∀ n, Nonempty (FiniteDyadicTraversal d n)) :
    Nonempty (DyadicTraversal d) := by
  obtain ⟨F, hF⟩ := exists_coherent_finiteDyadicTraversals d hfinite
  let cell : ∀ n : ℕ, Fin (2 ^ (d * n)) → Fin d → Fin (2 ^ n) :=
    fun n k i => (F n).cell n (Nat.le_refl n) k i
  refine ⟨{ cell := cell, bijective := ?_, adjacent := ?_, nested := ?_ }⟩
  · intro n
    exact (F n).bijective n (Nat.le_refl n)
  · intro n k l hkl
    exact (F n).adjacent n (Nat.le_refl n) k l hkl
  · intro n k l hkl i
    have hn := (F (n + 1)).nested n (Nat.le_refl (n + 1)) k l hkl i
    have hcell : (F (n + 1)).cell n (Nat.le_succ n) k i =
        (F n).cell n (Nat.le_refl n) k i := by
      have heq := congrArg
        (fun T : FiniteDyadicTraversal d n => T.cell n (Nat.le_refl n) k i) (hF n)
      exact heq
    exact hn.trans (congrArg Fin.val hcell)

/-- Given [a positive cube dimension](hyp:d,hd), [a coherent dyadic traversal exists](goal). -/
theorem exists_dyadicTraversal (d : ℕ) (hd : 0 < d) :
    Nonempty (DyadicTraversal d) :=
  exists_dyadicTraversal_of_finite d
    (fun n => exists_finiteDyadicTraversal d n hd)

end Causalean.Mathlib.Topology.SpaceFillingCurve
