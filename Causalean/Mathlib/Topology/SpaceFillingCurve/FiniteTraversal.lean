module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.GridExtension

/-!
# Finite coherent dyadic traversals

A finite traversal orders every dyadic grid through a prescribed level. This
separates the recursive orientation problem from the compactness argument that
extracts one infinite coherent traversal.
-/

@[expose] public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- A finite coherent traversal of the dyadic grids through level `n` in
dimension `d`. Every grid is visited exactly once, neighboring visits share a
face, and each block of `2^d` children lies in its parent cell. -/
structure FiniteDyadicTraversal (d n : ℕ) where
  cell : ∀ m : ℕ, m ≤ n → Fin (2 ^ (d * m)) → Fin d → Fin (2 ^ m)
  bijective : ∀ m (hm : m ≤ n), Function.Bijective (cell m hm)
  adjacent : ∀ m (hm : m ≤ n) (k l : Fin (2 ^ (d * m))),
    l.val = k.val + 1 →
    ∃ i : Fin d,
      ((cell m hm k i).val + 1 = (cell m hm l i).val ∨
        (cell m hm l i).val + 1 = (cell m hm k i).val) ∧
      ∀ j : Fin d, j ≠ i → cell m hm k j = cell m hm l j
  nested : ∀ m (hm : m + 1 ≤ n)
    (k : Fin (2 ^ (d * m))) (l : Fin (2 ^ (d * (m + 1)))),
    l.val / 2 ^ d = k.val →
    ∀ i : Fin d,
      (cell (m + 1) hm l i).val / 2 =
      (cell m (by omega) k i).val

/-- At depth zero, the unique dyadic cell gives a finite coherent traversal
in every dimension. -/
theorem exists_finiteDyadicTraversal_zero (d : ℕ) :
    Nonempty (FiniteDyadicTraversal d 0) := by
  refine ⟨{
    cell := fun m hm k i => ⟨0, by
      have hm0 : m = 0 := by omega
      subst m
      simp⟩
    bijective := by
      intro m hm
      constructor
      · intro k l _
        have hm0 : m = 0 := by omega
        subst m
        apply Fin.ext
        have hk := k.isLt
        have hl := l.isLt
        simp only [mul_zero, pow_zero] at hk hl
        omega
      · intro f
        have hm0 : m = 0 := by omega
        subst m
        refine ⟨⟨0, by simp⟩, ?_⟩
        funext i
        apply Fin.ext
        have hi := (f i).isLt
        simp only [pow_zero] at hi
        omega
    adjacent := by
      intro m hm k l hkl
      have hm0 : m = 0 := by omega
      subst m
      have hk : k.val = 0 := by simpa using k.isLt
      have hl : l.val = 0 := by simpa using l.isLt
      omega
    nested := by
      intro m hm
      omega
  }⟩

/-- A coherent traversal through depth `n` in dimension at least two extends
one level by replacing each parent cell with a compatible Gray child path. -/
theorem exists_finiteDyadicTraversal_succ (d n : ℕ) (hd : 2 ≤ d)
    (T : FiniteDyadicTraversal d n) :
    Nonempty (FiniteDyadicTraversal d (n + 1)) := by
  have hadj : ∀ k l : Fin (2 ^ (d * n)), l.val = k.val + 1 →
      FaceAdjacentGrid
        (fun i => (T.cell n (Nat.le_refl n) k i).val)
        (fun i => (T.cell n (Nat.le_refl n) l i).val) := by
    intro k l hkl
    obtain ⟨i, hi, hsame⟩ := T.adjacent n (Nat.le_refl n) k l hkl
    exact ⟨i, hi, fun j hj => congrArg Fin.val (hsame j hj)⟩
  obtain ⟨child, hbij, hchildadj, hchildnest⟩ :=
    exists_child_grid_order d n hd (T.cell n (Nat.le_refl n))
      (T.bijective n (Nat.le_refl n)) hadj
  let cell : ∀ m : ℕ, m ≤ n + 1 →
      Fin (2 ^ (d * m)) → Fin d → Fin (2 ^ m) := fun m hm =>
    if h : m ≤ n then T.cell m h else by
      have heq : m = n + 1 := by omega
      subst m
      exact child
  refine ⟨{ cell := cell, bijective := ?_, adjacent := ?_, nested := ?_ }⟩
  · intro m hm
    by_cases h : m ≤ n
    · simpa [cell, h] using T.bijective m h
    · have heq : m = n + 1 := by omega
      subst m
      simpa [cell, h] using hbij
  · intro m hm k l hkl
    by_cases h : m ≤ n
    · simpa [cell, h] using T.adjacent m h k l hkl
    · have heq : m = n + 1 := by omega
      subst m
      obtain ⟨i, hi, hsame⟩ := hchildadj k l hkl
      refine ⟨i, ?_, ?_⟩
      · simpa [cell, h] using hi
      · intro j hj
        apply Fin.ext
        simpa [cell, h] using hsame j hj
  · intro m hm k l hkl i
    by_cases h : m + 1 ≤ n
    · have hbase : m ≤ n := by omega
      simpa [cell, h, hbase] using T.nested m h k l hkl i
    · have heq : m = n := by omega
      subst m
      have htop : ¬ n + 1 ≤ n := by omega
      simpa [cell, htop] using hchildnest k l hkl i

/-- The unit interval has a finite coherent dyadic traversal through every
depth, using the natural increasing order of its dyadic cells. -/
theorem exists_finiteDyadicTraversal_one (n : ℕ) :
    Nonempty (FiniteDyadicTraversal 1 n) := by
  let cell : ∀ m : ℕ, m ≤ n → Fin (2 ^ (1 * m)) → Fin 1 → Fin (2 ^ m) :=
    fun m hm k i => ⟨k.val, by simpa using k.isLt⟩
  refine ⟨{ cell := cell, bijective := ?_, adjacent := ?_, nested := ?_ }⟩
  · intro m hm
    constructor
    · intro k l hkl
      apply Fin.ext
      have hi := congrFun hkl (0 : Fin 1)
      dsimp [cell] at hi
      have hv := congrArg Fin.val hi
      exact hv
    · intro f
      refine ⟨⟨(f 0).val, by simpa using (f 0).isLt⟩, ?_⟩
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      apply Fin.ext
      rfl
  · intro m hm k l hkl
    refine ⟨0, Or.inl ?_, ?_⟩
    · change k.val + 1 = l.val
      omega
    · intro j hj
      exact (hj (Subsingleton.elim j 0)).elim
  · intro m hm k l hkl i
    simpa [cell] using hkl

/-- Given [a positive cube dimension](hyp:d,hd) and [a finite depth](hyp:n), [a coherent traversal of all dyadic grids through that depth exists](goal). -/
theorem exists_finiteDyadicTraversal (d n : ℕ) (hd : 0 < d) :
    Nonempty (FiniteDyadicTraversal d n) := by
  by_cases h1 : d = 1
  · subst d
    exact exists_finiteDyadicTraversal_one n
  · have hd2 : 2 ≤ d := by omega
    induction n with
    | zero => exact exists_finiteDyadicTraversal_zero d
    | succ n ih =>
        obtain ⟨T⟩ := ih
        exact exists_finiteDyadicTraversal_succ d n hd2 T

end Causalean.Mathlib.Topology.SpaceFillingCurve
