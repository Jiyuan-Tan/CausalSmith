import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Sign-invariant decompositions of the real line

This module isolates the fixed-coefficient univariate layer used when lifting a cylindrical
decomposition.  A finite family of real polynomials has finitely many relevant roots; the roots
and the intervening intervals form a finite preconnected partition on which every polynomial has
constant exact sign.  The later parametric projection layer must prove that these partitions vary
cylindrically with the parameter point.
-/

open Set

namespace CausalSmith.Substrate.SemialgebraicCadDefinableChoice

/-- Two real numbers have the same exact sign when they are simultaneously negative, zero, or
positive. -/
def SameExactSign (left right : ℝ) : Prop :=
  (left < 0 ↔ right < 0) ∧ (left = 0 ↔ right = 0) ∧ (0 < left ↔ 0 < right)

/-- The roots of finitely many nonzero real polynomials are contained in one finite set.

The intended witness is the union of the `roots.toFinset` of the family.  Zero polynomials are
excluded because their root locus is the whole line, while their sign is already constant. -/
theorem exists_finite_root_cover (polynomials : Finset (Polynomial ℝ)) :
    ∃ roots : Finset ℝ, ∀ polynomial ∈ polynomials, polynomial ≠ 0 →
      ∀ x : ℝ, Polynomial.eval x polynomial = 0 → x ∈ roots := by
  refine ⟨polynomials.biUnion (fun polynomial => polynomial.roots.toFinset), ?_⟩
  intro polynomial hPolynomial hNonzero x hx
  rw [Finset.mem_biUnion]
  exact ⟨polynomial, hPolynomial,
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hNonzero).mpr hx)⟩

/-- A real polynomial has one exact sign throughout any preconnected set on which it never
vanishes.

The proof is the intermediate-value step of univariate sign sampling: opposite strict signs at
two points would force a zero between them. -/
theorem sameExactSign_on_preconnected_of_avoids_zero
    (polynomial : Polynomial ℝ) {cell : Set ℝ} (hCell : IsPreconnected cell)
    (hNoZero : ∀ x ∈ cell, Polynomial.eval x polynomial ≠ 0) :
    ∀ x ∈ cell, ∀ y ∈ cell,
      SameExactSign (Polynomial.eval x polynomial) (Polynomial.eval y polynomial) := by
  have hNoOpposite :
      ∀ ⦃x y : ℝ⦄, x ∈ cell → y ∈ cell →
        Polynomial.eval x polynomial < 0 → 0 < Polynomial.eval y polynomial → False := by
    intro x y hx hy hxneg hypos
    have hzero :
        (0 : ℝ) ∈ Set.Icc (Polynomial.eval x polynomial) (Polynomial.eval y polynomial) :=
      ⟨le_of_lt hxneg, le_of_lt hypos⟩
    rcases hCell.intermediate_value hx hy polynomial.continuousOn hzero with
      ⟨z, hzCell, hzZero⟩
    exact hNoZero z hzCell hzZero
  intro x hx y hy
  constructor
  · constructor
    · intro hxneg
      rcases lt_or_gt_of_ne (hNoZero y hy) with hyneg | hypos
      · exact hyneg
      · exact (hNoOpposite hx hy hxneg hypos).elim
    · intro hyneg
      rcases lt_or_gt_of_ne (hNoZero x hx) with hxneg | hxpos
      · exact hxneg
      · exact (hNoOpposite hy hx hyneg hxpos).elim
  constructor
  · constructor
    · intro hxzero
      exact (hNoZero x hx hxzero).elim
    · intro hyzero
      exact (hNoZero y hy hyzero).elim
  · constructor
    · intro hxpos
      rcases lt_or_gt_of_ne (hNoZero y hy) with hyneg | hypos
      · exact (hNoOpposite hy hx hyneg hxpos).elim
      · exact hypos
    · intro hypos
      rcases lt_or_gt_of_ne (hNoZero x hx) with hxneg | hxpos
      · exact (hNoOpposite hx hy hxneg hypos).elim
      · exact hxpos

/-- A finite partition of the real line into nonempty preconnected cells on each of which every
polynomial in a supplied finite family has constant exact sign. -/
structure UnivariateSignInvariantPartition (polynomials : Finset (Polynomial ℝ)) where
  /-- The finite number of sign-invariant cells. -/
  cellCount : ℕ
  /-- The subset of the real line represented by each cell index. -/
  cells : Fin cellCount → Set ℝ
  /-- Every indexed cell contains a real point. -/
  cellNonempty : ∀ cell, (cells cell).Nonempty
  /-- Every indexed cell is preconnected. -/
  cellPreconnected : ∀ cell, IsPreconnected (cells cell)
  /-- The cells cover the whole real line. -/
  cellsCover : Set.univ = ⋃ cell, cells cell
  /-- Distinct cells are disjoint. -/
  cellsDisjoint : ∀ left right, left ≠ right → Disjoint (cells left) (cells right)
  /-- Every supplied polynomial has constant exact sign on every cell. -/
  signInvariant : ∀ cell polynomial, polynomial ∈ polynomials →
    ∀ x ∈ cells cell, ∀ y ∈ cells cell,
      SameExactSign (Polynomial.eval x polynomial) (Polynomial.eval y polynomial)

/-- Every finite family of real univariate polynomials admits a finite sign-invariant partition
of the real line into nonempty preconnected cells.

A proof should sort the finite root cover, use singleton cells at roots and open interval cells
between consecutive roots (including the two unbounded sectors), and apply
`sameExactSign_on_preconnected_of_avoids_zero` on each sector. -/
theorem exists_univariateSignInvariantPartition (polynomials : Finset (Polynomial ℝ)) :
    Nonempty (UnivariateSignInvariantPartition polynomials) := by
  classical
  rcases exists_finite_root_cover polynomials with ⟨roots, hRoots⟩
  by_cases hEmpty : roots = ∅
  · refine ⟨{
      cellCount := 1
      cells := fun _ => Set.univ
      cellNonempty := fun _ => Set.univ_nonempty
      cellPreconnected := fun _ => isPreconnected_univ
      cellsCover := by
        ext x
        constructor
        · intro hx
          exact Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
        · intro hx
          exact Set.mem_univ x
      cellsDisjoint := ?_
      signInvariant := ?_ }⟩
    · intro left right hne
      exact (hne (Subsingleton.elim left right)).elim
    · intro cell polynomial hPolynomial x hx y hy
      by_cases hPolynomialZero : polynomial = 0
      · subst polynomial
        simp [SameExactSign]
      · have hNoZero : ∀ z ∈ (Set.univ : Set ℝ), Polynomial.eval z polynomial ≠ 0 := by
          intro z hz hzZero
          have hzRoot := hRoots polynomial hPolynomial hPolynomialZero z hzZero
          rw [hEmpty] at hzRoot
          have hzNotRoot : z ∉ (∅ : Finset ℝ) := by simp
          exact hzNotRoot hzRoot
        exact sameExactSign_on_preconnected_of_avoids_zero polynomial isPreconnected_univ
          hNoZero x hx y hy
  · let n := roots.card
    have hn : 0 < n := by
      dsimp [n]
      exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
    let orderedRoots : Fin n ↪o ℝ := roots.orderEmbOfFin (by rfl)
    let rootCell : Fin n → Set ℝ := fun i => {orderedRoots i}
    let sectorCell : Fin (n + 1) → Set ℝ := fun i =>
      {x | (∀ j : Fin n, j.val < i.val → orderedRoots j < x) ∧
        (∀ j : Fin n, i.val ≤ j.val → x < orderedRoots j)}
    let cellEquiv : Fin n ⊕ Fin (n + 1) ≃ Fin (n + (n + 1)) := finSumFinEquiv
    let allCells : Fin (n + (n + 1)) → Set ℝ := fun i =>
      Sum.elim rootCell sectorCell (cellEquiv.symm i)
    have hOrderedMem (i : Fin n) : orderedRoots i ∈ roots := by
      exact Finset.orderEmbOfFin_mem roots (by rfl) i
    have hSectorAvoidsRoot (i : Fin (n + 1)) (j : Fin n) :
        orderedRoots j ∉ sectorCell i := by
      intro hj
      change (∀ k : Fin n, k.val < i.val → orderedRoots k < orderedRoots j) ∧
        (∀ k : Fin n, i.val ≤ k.val → orderedRoots j < orderedRoots k) at hj
      by_cases hji : j.val < i.val
      · exact (lt_irrefl _ (hj.1 j hji))
      · exact (lt_irrefl _ (hj.2 j (Nat.le_of_not_gt hji)))
    have hSectorNonempty (i : Fin (n + 1)) : (sectorCell i).Nonempty := by
      by_cases hiZero : i.val = 0
      · let first : Fin n := ⟨0, hn⟩
        refine ⟨orderedRoots first - 1, ?_⟩
        change (∀ j : Fin n, j.val < i.val → orderedRoots j < orderedRoots first - 1) ∧
          (∀ j : Fin n, i.val ≤ j.val → orderedRoots first - 1 < orderedRoots j)
        constructor
        · intro j hj
          omega
        · intro j hj
          have hle : orderedRoots first ≤ orderedRoots j :=
            orderedRoots.monotone (by apply Fin.mk_le_mk.mpr; exact Nat.zero_le _)
          linarith
      · by_cases hiLast : i.val = n
        · let last : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
          refine ⟨orderedRoots last + 1, ?_⟩
          change (∀ j : Fin n, j.val < i.val → orderedRoots j < orderedRoots last + 1) ∧
            (∀ j : Fin n, i.val ≤ j.val → orderedRoots last + 1 < orderedRoots j)
          constructor
          · intro j hj
            have hle : orderedRoots j ≤ orderedRoots last :=
              orderedRoots.monotone (by apply Fin.mk_le_mk.mpr; omega)
            linarith
          · intro j hj
            omega
        · let left : Fin n := ⟨i.val - 1, by omega⟩
          let right : Fin n := ⟨i.val, by omega⟩
          have hiPos : 0 < i.val := Nat.pos_of_ne_zero hiZero
          have hiLe : i.val ≤ n := Nat.le_of_lt_succ i.isLt
          have hiLt : i.val < n := lt_of_le_of_ne hiLe hiLast
          have hLeftRight : orderedRoots left < orderedRoots right :=
            orderedRoots.strictMono (by apply Fin.mk_lt_mk.mpr; omega)
          refine ⟨(orderedRoots left + orderedRoots right) / 2, ?_⟩
          change
            (∀ j : Fin n, j.val < i.val →
              orderedRoots j < (orderedRoots left + orderedRoots right) / 2) ∧
            (∀ j : Fin n, i.val ≤ j.val →
              (orderedRoots left + orderedRoots right) / 2 < orderedRoots j)
          constructor
          · intro j hj
            have hle : orderedRoots j ≤ orderedRoots left :=
              orderedRoots.monotone (by apply Fin.mk_le_mk.mpr; omega)
            linarith
          · intro j hj
            have hle : orderedRoots right ≤ orderedRoots j :=
              orderedRoots.monotone (by apply Fin.mk_le_mk.mpr; omega)
            linarith
    have hSectorPreconnected (i : Fin (n + 1)) : IsPreconnected (sectorCell i) := by
      apply Set.OrdConnected.isPreconnected
      rw [Set.ordConnected_def]
      intro x hx y hy z hz
      change (∀ j : Fin n, j.val < i.val → orderedRoots j < z) ∧
        (∀ j : Fin n, i.val ≤ j.val → z < orderedRoots j)
      constructor
      · intro j hj
        exact (hx.1 j hj).trans_le hz.1
      · intro j hj
        exact hz.2.trans_lt (hy.2 j hj)
    have hCover (x : ℝ) : x ∈ ⋃ i, allCells i := by
      by_cases hxRoot : x ∈ roots
      · have hxRange : x ∈ Set.range orderedRoots := by
          change x ∈ Set.range (roots.orderEmbOfFin (by rfl))
          rw [Finset.range_orderEmbOfFin]
          exact hxRoot
        rcases hxRange with ⟨j, rfl⟩
        refine Set.mem_iUnion.mpr ⟨cellEquiv (Sum.inl j), ?_⟩
        simp [allCells, cellEquiv, rootCell]
      · let above : Finset (Fin n) := Finset.univ.filter (fun j => x < orderedRoots j)
        by_cases hAbove : above.Nonempty
        · rcases Finset.exists_min_image above (fun j : Fin n => j.val) hAbove with
            ⟨firstAbove, hFirstAbove, hFirstAboveMin⟩
          let sectorIndex : Fin (n + 1) := ⟨firstAbove.val, by omega⟩
          have hxSector : x ∈ sectorCell sectorIndex := by
            change (∀ j : Fin n, j.val < sectorIndex.val → orderedRoots j < x) ∧
              (∀ j : Fin n, sectorIndex.val ≤ j.val → x < orderedRoots j)
            constructor
            · intro j hj
              by_contra hnot
              have hxle : x ≤ orderedRoots j := le_of_not_gt hnot
              have hxne : x ≠ orderedRoots j := fun h => hxRoot (h ▸ hOrderedMem j)
              have hjAbove : j ∈ above := by
                simp only [above, Finset.mem_filter, Finset.mem_univ, true_and]
                exact lt_of_le_of_ne hxle hxne
              have := hFirstAboveMin j hjAbove
              simp [sectorIndex] at hj
              omega
            · intro j hj
              have hxFirst : x < orderedRoots firstAbove := by
                simpa [above] using (Finset.mem_filter.mp hFirstAbove).2
              exact hxFirst.trans_le (orderedRoots.monotone (by
                apply Fin.mk_le_mk.mpr
                simpa [sectorIndex] using hj))
          refine Set.mem_iUnion.mpr ⟨cellEquiv (Sum.inr sectorIndex), ?_⟩
          simpa [allCells, cellEquiv] using hxSector
        · let sectorIndex : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
          have hxSector : x ∈ sectorCell sectorIndex := by
            change (∀ j : Fin n, j.val < sectorIndex.val → orderedRoots j < x) ∧
              (∀ j : Fin n, sectorIndex.val ≤ j.val → x < orderedRoots j)
            constructor
            · intro j hj
              have hnotAbove : ¬x < orderedRoots j := by
                intro hlt
                apply hAbove
                exact ⟨j, by simp [above, hlt]⟩
              have hle : orderedRoots j ≤ x := le_of_not_gt hnotAbove
              have hne : orderedRoots j ≠ x := fun h => hxRoot (h ▸ hOrderedMem j)
              exact lt_of_le_of_ne hle hne
            · intro j hj
              change n ≤ j.val at hj
              exact (not_lt_of_ge hj j.isLt).elim
          refine Set.mem_iUnion.mpr ⟨cellEquiv (Sum.inr sectorIndex), ?_⟩
          simpa [allCells, cellEquiv] using hxSector
    have hAllCellsNonempty (i : Fin (n + (n + 1))) : (allCells i).Nonempty := by
      rcases cellEquiv.surjective i with ⟨j, rfl⟩
      cases j with
      | inl j => simp [allCells, cellEquiv, rootCell]
      | inr j => simpa [allCells, cellEquiv] using hSectorNonempty j
    have hAllCellsPreconnected (i : Fin (n + (n + 1))) : IsPreconnected (allCells i) := by
      rcases cellEquiv.surjective i with ⟨j, rfl⟩
      cases j with
      | inl j =>
          simpa [allCells, cellEquiv, rootCell] using
            (isPreconnected_singleton : IsPreconnected ({orderedRoots j} : Set ℝ))
      | inr j => simpa [allCells, cellEquiv] using hSectorPreconnected j
    have hAllCellsDisjoint :
        ∀ left right, left ≠ right → Disjoint (allCells left) (allCells right) := by
      intro left right hne
      rcases cellEquiv.surjective left with ⟨left, rfl⟩
      rcases cellEquiv.surjective right with ⟨right, rfl⟩
      have hne' : left ≠ right := fun h => hne (congrArg cellEquiv h)
      cases left with
      | inl left =>
          cases right with
          | inl right =>
              rw [show allCells (cellEquiv (Sum.inl left)) = {orderedRoots left} by
                simp [allCells, cellEquiv, rootCell]]
              rw [show allCells (cellEquiv (Sum.inl right)) = {orderedRoots right} by
                simp [allCells, cellEquiv, rootCell]]
              rw [Set.disjoint_singleton_left]
              simp only [Set.mem_singleton_iff]
              intro h
              apply hne'
              simp only [Sum.inl.injEq]
              exact orderedRoots.injective h
          | inr right =>
              rw [show allCells (cellEquiv (Sum.inl left)) = {orderedRoots left} by
                simp [allCells, cellEquiv, rootCell]]
              rw [show allCells (cellEquiv (Sum.inr right)) = sectorCell right by
                simp [allCells, cellEquiv]]
              exact Set.disjoint_singleton_left.mpr (hSectorAvoidsRoot right left)
      | inr left =>
          cases right with
          | inl right =>
              rw [show allCells (cellEquiv (Sum.inr left)) = sectorCell left by
                simp [allCells, cellEquiv]]
              rw [show allCells (cellEquiv (Sum.inl right)) = {orderedRoots right} by
                simp [allCells, cellEquiv, rootCell]]
              exact Set.disjoint_singleton_right.mpr (hSectorAvoidsRoot left right)
          | inr right =>
              rw [show allCells (cellEquiv (Sum.inr left)) = sectorCell left by
                simp [allCells, cellEquiv]]
              rw [show allCells (cellEquiv (Sum.inr right)) = sectorCell right by
                simp [allCells, cellEquiv]]
              rw [Set.disjoint_left]
              intro x hxLeft hxRight
              have hneSector : left ≠ right := by
                intro h
                apply hne'
                simp [h]
              rcases lt_or_gt_of_ne hneSector with hlt | hgt
              · let rootIndex : Fin n := ⟨left.val, by omega⟩
                exact (not_lt_of_ge (le_of_lt (hxRight.1 rootIndex (by simp [rootIndex]; omega))))
                  (hxLeft.2 rootIndex (by simp [rootIndex]))
              · let rootIndex : Fin n := ⟨right.val, by omega⟩
                exact (not_lt_of_ge (le_of_lt (hxLeft.1 rootIndex (by simp [rootIndex]; omega))))
                  (hxRight.2 rootIndex (by simp [rootIndex]))
    refine ⟨{
      cellCount := n + (n + 1)
      cells := allCells
      cellNonempty := hAllCellsNonempty
      cellPreconnected := hAllCellsPreconnected
      cellsCover := by
        ext x
        simp only [Set.mem_univ, true_iff]
        exact hCover x
      cellsDisjoint := hAllCellsDisjoint
      signInvariant := ?_ }⟩
    intro cell polynomial hPolynomial x hx y hy
    rcases cellEquiv.surjective cell with ⟨cell, rfl⟩
    cases cell with
    | inl rootIndex =>
        have hx' : x = orderedRoots rootIndex := by
          simpa [allCells, cellEquiv, rootCell] using hx
        have hy' : y = orderedRoots rootIndex := by
          simpa [allCells, cellEquiv, rootCell] using hy
        subst x
        subst y
        exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
    | inr sectorIndex =>
        have hx' : x ∈ sectorCell sectorIndex := by
          simpa [allCells, cellEquiv] using hx
        have hy' : y ∈ sectorCell sectorIndex := by
          simpa [allCells, cellEquiv] using hy
        by_cases hPolynomialZero : polynomial = 0
        · subst polynomial
          simp [SameExactSign]
        · apply sameExactSign_on_preconnected_of_avoids_zero polynomial
            (hSectorPreconnected sectorIndex) _ x hx' y hy'
          intro z hz hzZero
          have hzRoot := hRoots polynomial hPolynomial hPolynomialZero z hzZero
          rw [← Finset.image_orderEmbOfFin_univ roots (by rfl)] at hzRoot
          rcases Finset.mem_image.mp hzRoot with ⟨rootIndex, hrootIndex, hrootEq⟩
          exact hSectorAvoidsRoot sectorIndex rootIndex (hrootEq ▸ hz)

end CausalSmith.Substrate.SemialgebraicCadDefinableChoice
