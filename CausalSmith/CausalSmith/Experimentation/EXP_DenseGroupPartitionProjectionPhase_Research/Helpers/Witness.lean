import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Estimator
import Mathlib.Tactic.NormNum

/-!
# Balanced eight-unit witness

This file defines the balanced four-plus/four-minus vector and its composition
schedule for the paper's finite exact-moment witness.
-/

open scoped BigOperators

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

/-- The balanced eight-unit sign vector. -/
-- @node: a8
def a8 (i : Fin 8) : ℝ := if i.1 < 4 then 1 else -1
  -- @realizes \mathbf a_8(four plus signs followed by four minus signs)

/-- A bundled witness whose type fixes the paper's population, group size,
group count, treated count, and grouped-unit count. -/
structure EightUnitWitness where
  schedule : PotentialOutcome 8 2
  groups : ℕ := 4
  treated : ℕ := 2
  groupedUnits : ℕ := 8
  groups_eq : groups = 4
  treated_eq : treated = 2
  grouped_eq : groupedUnits = 2 * groups

-- @node: def:eight-unit-witness
/-- The bundled balanced `n = N = 8`, `M = 2`, `G = 4`, `G1 = 2` witness. -/
noncomputable def witness8Bundle : EightUnitWitness where
  schedule := fun A _ z => if z then (∑ j ∈ A.1, a8 j) / 2 else 0
  groups := 4
  treated := 2
  groupedUnits := 8
  groups_eq := rfl
  treated_eq := rfl
  grouped_eq := rfl
  -- @realizes n(witness population 8) @realizes M(witness group size 2)
  -- @realizes G_n(witness group count 4) @realizes G_{1n}(witness treated count 2)
  -- @realizes N_n(witness grouped count 8)

/-- The schedule component of the bundled eight-unit witness. -/
noncomputable def witness8 : PotentialOutcome 8 2 := witness8Bundle.schedule

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
