/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Core

/-! # Finite-partition predictors

A finite-partition predictor has a finite set of cells, a map sending each input
to its cell, and a value per cell. The predictor is piecewise constant on those
cells.
-/

@[expose] public section

namespace Causalean.ML

/-- A piecewise-constant predictor on a finite partition: [a finite index type `cell` of
partition cells](hyp:cell,fintypeCell), [a map `chooseCell` assigning each input to its
cell](hyp:chooseCell), and [a constant predicted value `value` on each cell](hyp:value). -/
structure FinitePartitionPredictor (X : Type*) where
  /-- The (finite) index type of partition cells. -/
  cell : Type
  /-- Finiteness of the cell index. -/
  [fintypeCell : Fintype cell]
  /-- The cell that an input falls into. -/
  chooseCell : X → cell
  /-- The constant predicted value on each cell. -/
  value : cell → ℝ

attribute [instance] FinitePartitionPredictor.fintypeCell

/-- [A finite-partition prediction](goal) returns [its cell's constant](step:1). It evaluates
[a finite-partition predictor](hyp:T) on [an input](hyp:x) from
[its domain](hyp:X). -/
def FinitePartitionPredictor.eval {X : Type*} (T : FinitePartitionPredictor X) (x : X) : ℝ :=
  T.value (T.chooseCell x)

/-- [A finite-partition predictor is constant on each cell](goal): [the predictor](hyp:T)
returns the cell's assigned value throughout [the inputs mapped to that cell](hyp:c). -/
theorem FinitePartitionPredictor.eval_eqOn_cell {X : Type*}
    (T : FinitePartitionPredictor X) (c : T.cell) :
    Set.EqOn T.eval (fun _ => T.value c) {x | T.chooseCell x = c} := by
  intro x hx
  simp only [FinitePartitionPredictor.eval, Set.mem_setOf_eq] at hx ⊢
  rw [hx]

end Causalean.ML
