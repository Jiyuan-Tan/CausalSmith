/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.AffineSignCellClosure.Closure
import Causalean.Mathlib.Optimization.AffineSignCellClosure.CommonSlack

/-! # Mixed strict/weak sign-cell example

This module instantiates the API with the interval cut out by the strict inequality `0 < x`
and the weak inequality `x ≤ 1`.
-/

open Set

namespace Causalean.Mathlib.Optimization.AffineSignCellClosure

/-- The [mixed one-dimensional example system](goal) is given by [the strict lower inequality
`-x < 0` and the weak upper inequality `x - 1 ≤ 0`](step:1). -/
def mixedExample : AffineSystem 1 :=
  [ { fn := { coeff := fun _ => -1, constant := 0 }, kind := .strict },
    { fn := { coeff := fun _ => 1, constant := -1 }, kind := .weak } ]

/-- Given [a one-dimensional coordinate vector](hyp:x), [it belongs to the example's strict
cell exactly when its coordinate lies above zero and at most one](goal). -/
theorem mem_strictCell_mixedExample (x : Fin 1 → ℝ) :
    x ∈ strictCell mixedExample ↔ 0 < x 0 ∧ x 0 ≤ 1 := by
  simp [strictCell, mixedExample, Constraint.strictHolds, AffineFn.eval]

/-- Given [a one-dimensional coordinate vector](hyp:x), [it belongs to the example's weak
cell exactly when its coordinate lies between zero and one inclusively](goal). -/
theorem mem_weakCell_mixedExample (x : Fin 1 → ℝ) :
    x ∈ weakCell mixedExample ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 := by
  simp [weakCell, mixedExample, Constraint.weakHolds, AffineFn.eval]

/-- [The constant one-half coordinate vector belongs to the example's strict cell](goal). -/
theorem half_mem_strictCell_mixedExample :
    (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ strictCell mixedExample := by
  rw [mem_strictCell_mixedExample]
  norm_num

/-- [The closure of the example's half-open strict interval equals its closed weak interval](goal). -/
theorem closure_strictCell_mixedExample :
    closure (strictCell mixedExample) = weakCell mixedExample := by
  apply closure_strictCell_eq_weakCell
  exact ⟨_, half_mem_strictCell_mixedExample⟩

end Causalean.Mathlib.Optimization.AffineSignCellClosure
