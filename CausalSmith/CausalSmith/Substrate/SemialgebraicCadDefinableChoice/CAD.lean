import CausalSmith.Substrate.SemialgebraicCadDefinableChoice.Sets

/-!
# Finite cylindrical decompositions

This module packages the proposition-level output of cylindrical algebraic decomposition for a
chosen ordering of finitely many real coordinates.  Cells are nonempty, connected,
semialgebraic, pairwise disjoint, and their projections to every initial coordinate segment are
either identical or disjoint.
-/

open Set

namespace CausalSmith.Substrate.SemialgebraicCadDefinableChoice

universe u

/-- The coordinates lying strictly before a cut in a supplied finite coordinate order. -/
def PrefixIndex {ι : Type u} [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (cut : Fin (Fintype.card ι + 1)) : Type u :=
  {coordinate : ι // (order coordinate).1 < cut.1}

namespace PrefixIndex

/-- A prefix coordinate embeds into the full coordinate index type by forgetting its proof. -/
def embedding {ι : Type*} [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (cut : Fin (Fintype.card ι + 1)) : PrefixIndex order cut ↪ ι :=
  ⟨Subtype.val, Subtype.val_injective⟩

end PrefixIndex

/-- The projection of a set onto the coordinates preceding a cut in the supplied order. -/
def prefixProjection {ι : Type*} [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (cut : Fin (Fintype.card ι + 1)) (set : Set (ι → ℝ)) :
    Set (PrefixIndex order cut → ℝ) :=
  coordinateProjection (PrefixIndex.embedding order cut) '' set

/-- A finite cylindrical partition of a semialgebraic set along a supplied coordinate order. -/
structure CylindricalPartition {ι : Type*} [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι)) (set : Set (ι → ℝ)) where
  /-- The finite number of cells. -/
  cellCount : ℕ
  /-- The subset represented by each cell index. -/
  cells : Fin cellCount → Set (ι → ℝ)
  /-- Every indexed cell contains a point. -/
  cellNonempty : ∀ cell, (cells cell).Nonempty
  /-- Every cell is semialgebraic. -/
  cellSemialgebraic : ∀ cell, IsSemialgebraicSet (cells cell)
  /-- Every cell is connected. -/
  cellPreconnected : ∀ cell, IsPreconnected (cells cell)
  /-- The cells cover exactly the decomposed set. -/
  cellsCover : set = ⋃ cell, cells cell
  /-- Distinct cells are disjoint. -/
  cellsDisjoint : ∀ left right, left ≠ right → Disjoint (cells left) (cells right)
  /-- At every initial coordinate segment, two cell projections coincide or are disjoint. -/
  cylindrical : ∀ left right (cut : Fin (Fintype.card ι + 1)),
    prefixProjection order cut (cells left) = prefixProjection order cut (cells right) ∨
      Disjoint (prefixProjection order cut (cells left))
        (prefixProjection order cut (cells right))

/-- Every semialgebraic set has a finite cylindrical partition along any supplied coordinate
order.  This is the proposition-level CAD existence theorem; its standard proof is the finite
projection-and-lifting construction with sign-invariant cells. -/
theorem exists_cylindricalPartition {ι : Type*} [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι)) {set : Set (ι → ℝ)}
    (hSet : IsSemialgebraicSet set) : Nonempty (CylindricalPartition order set) := by
  sorry

end CausalSmith.Substrate.SemialgebraicCadDefinableChoice
