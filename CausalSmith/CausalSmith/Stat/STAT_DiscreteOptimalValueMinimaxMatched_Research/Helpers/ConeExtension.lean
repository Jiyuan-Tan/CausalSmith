import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Basic

/-! Four-cell overlap geometry and the global optimal-value extension. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open scoped BigOperators

-- @env: S3
variable (u : Cell → ℝ) -- @realizes \(u\)(four-cell real vector)

/-- Treatment-arm mass of a four-vector. -/
def vectorArmMass (u : Cell → ℝ) (a : Fin 2) : ℝ := u (a, 0) + u (a, 1)
  -- @realizes \(s_a(u)\)(sum over outcomes)

/-- Total mass of a four-vector. -/
def vectorMass (u : Cell → ℝ) : ℝ := vectorArmMass u 0 + vectorArmMass u 1
  -- @realizes \(s(u)\)(sum over arms)

-- @node: def:overlap-cone
/-- Nonnegative four-vectors whose treated mass is in the overlap band. -/
def overlapCone (epsilon : ℝ) : Set (Cell → ℝ) :=
  {u | (∀ j, 0 ≤ u j) ∧
    epsilon * vectorMass u ≤ vectorArmMass u 1 ∧
    vectorArmMass u 1 ≤ (1 - epsilon) * vectorMass u}
  -- @realizes \(\mathcal C_\epsilon\)(nonnegative overlap cone)

/-- The arm-specific totalized global extension. -/
noncomputable def armCellValue (epsilon : ℝ) (a : Fin 2) (u : Cell → ℝ) : ℝ :=
  if vectorMass u = 0 then 0
  else vectorMass u * u (a, 1) / max (vectorArmMass u a) (epsilon * vectorMass u)

/-- Totalized implementation of the optimal-value cell extension on ambient real vectors. -/
noncomputable def globalCellValue (epsilon : ℝ) (u : Cell → ℝ) : ℝ :=
  max (armCellValue epsilon 0 u) (armCellValue epsilon 1 u)

/-- The nonnegative four-vector domain appearing in the paper. -/
abbrev NonnegativeCellVector := {u : Cell → ℝ // ∀ j, 0 ≤ u j}

-- @node: def:global-extension
/-- The paper-facing global extension on the nonnegative four-vector cone. -/
noncomputable def globalCellValueNonnegative (epsilon : ℝ)
    (u : NonnegativeCellVector) : ℝ :=
  globalCellValue epsilon u.1
  -- @realizes \(\bar f_\epsilon\)(maximum of arm-specific extensions)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
