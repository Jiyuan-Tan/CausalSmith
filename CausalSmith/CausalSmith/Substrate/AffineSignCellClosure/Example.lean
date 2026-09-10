import CausalSmith.Substrate.AffineSignCellClosure.Closure
import CausalSmith.Substrate.AffineSignCellClosure.CommonSlack

/-!
# Small mixed strict/weak sign-cell example

This module instantiates the API with the interval cut out by the strict inequality `0 < x`
and the weak inequality `x ≤ 1`.
-/

open Set

namespace CausalSmith.Substrate.AffineSignCellClosure

/-- The one-dimensional example system consists of `-x < 0` and `x - 1 ≤ 0`. -/
def mixedExample : AffineSystem 1 :=
  [ { fn := { coeff := fun _ => -1, constant := 0 }, kind := .strict },
    { fn := { coeff := fun _ => 1, constant := -1 }, kind := .weak } ]

/-- The strict cell of the example is the half-open interval `(0,1]`. -/
theorem mem_strictCell_mixedExample (x : Fin 1 → ℝ) :
    x ∈ strictCell mixedExample ↔ 0 < x 0 ∧ x 0 ≤ 1 := by
  sorry

/-- The weak relaxation of the example is the closed interval `[0,1]`. -/
theorem mem_weakCell_mixedExample (x : Fin 1 → ℝ) :
    x ∈ weakCell mixedExample ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 := by
  sorry

/-- The midpoint belongs to the strict cell of the mixed example. -/
theorem half_mem_strictCell_mixedExample :
    (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ strictCell mixedExample := by
  sorry

/-- The closure of the example's half-open strict cell is its closed weak relaxation. -/
theorem closure_strictCell_mixedExample :
    closure (strictCell mixedExample) = weakCell mixedExample := by
  sorry

end CausalSmith.Substrate.AffineSignCellClosure
