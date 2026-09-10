import CausalSmith.Substrate.AffineSignCellClosure.Closure
import Mathlib.Topology.Order.OrderClosed

/-!
# Preservation of bounded coordinate extrema

Continuous real objectives have dense images when restricted from a weak affine cell to its
nonempty strict cell. Consequently their bounded infima and suprema agree on the two cells.
-/

open Set

namespace CausalSmith.Substrate.AffineSignCellClosure

/-- For a nonempty strict cell and a continuous real objective, the strict and weak image
sets have the same closure. -/
/- Proof strategy: one inclusion follows from `strictCell_subset_weakCell`; for the other,
rewrite the weak cell using `closure_strictCell_eq_weakCell` and use
`image_closure_subset_closure_image`. -/
theorem closure_image_strictCell_eq_closure_image_weakCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ) :
    closure (φ '' strictCell Γ) = closure (φ '' weakCell Γ) := by
  sorry

/-- A lower bound on the strict-cell objective image is also a lower bound on the weak-cell
objective image. -/
theorem bddBelow_image_weakCell_of_strictCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ)
    (hBdd : BddBelow (φ '' strictCell Γ)) :
    BddBelow (φ '' weakCell Γ) := by
  sorry

/-- An upper bound on the strict-cell objective image is also an upper bound on the weak-cell
objective image. -/
theorem bddAbove_image_weakCell_of_strictCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ)
    (hBdd : BddAbove (φ '' strictCell Γ)) :
    BddAbove (φ '' weakCell Γ) := by
  sorry

/-- A continuous real objective has the same infimum on a nonempty strict cell and its weak
relaxation, provided its strict-cell image is bounded below. -/
/- Proof strategy: show that strict and weak images have the same lower bounds via their
equal closures and `lowerBounds_closure`, then identify their conditional infima. -/
theorem sInf_image_strictCell_eq_weakCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ)
    (hBdd : BddBelow (φ '' strictCell Γ)) :
    sInf (φ '' strictCell Γ) = sInf (φ '' weakCell Γ) := by
  sorry

/-- A continuous real objective has the same supremum on a nonempty strict cell and its weak
relaxation, provided its strict-cell image is bounded above. -/
/- Proof strategy: use equal image closures and `upperBounds_closure`; nonemptiness comes
from the supplied strict point, while boundedness transfers to the weak image. -/
theorem sSup_image_strictCell_eq_weakCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ)
    (hBdd : BddAbove (φ '' strictCell Γ)) :
    sSup (φ '' strictCell Γ) = sSup (φ '' weakCell Γ) := by
  sorry

/-- An affine coordinate objective has the same bounded-below infimum on the strict and weak
cells. -/
theorem sInf_affineEval_strictCell_eq_weakCell {n : ℕ}
    {Γ : AffineSystem n} (f : AffineFn n)
    (hΓ : (strictCell Γ).Nonempty)
    (hBdd : BddBelow (f.eval '' strictCell Γ)) :
    sInf (f.eval '' strictCell Γ) = sInf (f.eval '' weakCell Γ) := by
  sorry

/-- An affine coordinate objective has the same bounded-above supremum on the strict and
weak cells. -/
theorem sSup_affineEval_strictCell_eq_weakCell {n : ℕ}
    {Γ : AffineSystem n} (f : AffineFn n)
    (hΓ : (strictCell Γ).Nonempty)
    (hBdd : BddAbove (f.eval '' strictCell Γ)) :
    sSup (f.eval '' strictCell Γ) = sSup (f.eval '' weakCell Γ) := by
  sorry

end CausalSmith.Substrate.AffineSignCellClosure
