import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T3_Complete32Certificate
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.Inference
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.AtomicTieSubsampling
import Causalean.Mathlib.StandardGaussian
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option linter.style.openClassical false

/-! # Exact nondegenerate atomic-tie certificate -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped ENNReal Classical
open MeasureTheory Set

noncomputable def witness32PDagger : Fin 12 → ℝ :=
  ![0, 1/4, 1/4, 0, 0, 0, 1/2, 0, 0, 0, 0, 0]

noncomputable def witness32G0 : Fin 12 → ℝ :=
  ![0, -1, -3, 0, 0, 0, 4, 0, 0, 0, 0, 0]

noncomputable def witness32G1 : Fin 12 → ℝ :=
  ![0, 1, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0]

noncomputable def witness32Z0 : Fin 12 → ℝ :=
  ![4/5, -1/5, -11/5, 4/5, 4/5, 0, 0, 0, 0, 0, 0, 0]

noncomputable def witness32Z1 : Fin 12 → ℝ :=
  ![0, 0, 0, 0, 0, 0, -8/5, 2/5, 2/5, 0, 2/5, 2/5]

/-- The two-dimensional effective multinomial support at `p_dagger`. -/
def witness32EffectiveSpace : Set (Fin 12 → ℝ) :=
  {g | ∃ x y : ℝ, g =
    ![0, x, y, 0, 0, 0, -(x + y), 0, 0, 0, 0, 0]}

/-- The full-dimensional zero cone in the effective support. -/
def witness32ZeroCone : Set (Fin 12 → ℝ) :=
  {g | ∃ x y : ℝ, g =
      ![0, x, y, 0, 0, 0, -(x + y), 0, 0, 0, 0, 0] ∧
    x + y < 0 ∧ x > y ∧ 0 < 3 * x - 2 * y}

noncomputable def witness32DLower (g : Fin 12 → ℝ) : ℝ :=
  (projectionComposedDerivative witness32Geometry witness32PDagger g).1

noncomputable def witness32DUpper (g : Fin 12 → ℝ) : ℝ :=
  (projectionComposedDerivative witness32Geometry witness32PDagger g).2

noncomputable def witness32LimitStatistic (g : Fin 12 → ℝ) : ℝ :=
  endpointLimitStatistic witness32DLower witness32DUpper g

/-- The rational projection, dual-slope, open-cone, and Gaussian-mass
certificate showing that the zero atom is genuine and nondegenerate. -/
-- @node: prop:32-nondegenerate-atomic-tie-certificate
theorem nondegenerate_atomic_tie_certificate_32 :
    witness32PDagger =
      (2 : ℝ)⁻¹ • (fun o => witness32Incidence o 2 + witness32Incidence o 4) ∧
    witness32PDagger ∈ observablePolytope witness32Geometry ∧
    polyhedralTangentCone witness32Geometry witness32PDagger ≠ Set.univ ∧
    (∃ a ∈ lowerOptimalFace witness32Geometry witness32PDagger,
      ∃ b ∈ lowerOptimalFace witness32Geometry witness32PDagger, a.2 ≠ b.2) ∧
    (∃ a ∈ upperOptimalFace witness32Geometry witness32PDagger,
      ∃ b ∈ upperOptimalFace witness32Geometry witness32PDagger, a.2 ≠ b.2) ∧
    tangentProjection witness32Geometry witness32PDagger witness32G0 = witness32Z0 ∧
    tangentProjection witness32Geometry witness32PDagger witness32G1 = witness32Z1 ∧
    witness32DLower witness32G0 = 0 ∧
    witness32DUpper witness32G0 = 6 / 5 ∧
    witness32LimitStatistic witness32G0 = 0 ∧
    witness32DLower witness32G1 = 12 / 5 ∧
    witness32DUpper witness32G1 = 0 ∧
    witness32LimitStatistic witness32G1 = 12 / 5 ∧
    (∀ g ∈ witness32ZeroCone, witness32LimitStatistic g = 0) ∧
    (∀ U : Set (Fin 12 → ℝ), IsOpen U → U.Nonempty →
      U ⊆ witness32EffectiveSpace →
      0 < (multinomialGaussianLaw witness32PDagger) U) ∧
    0 < ENNReal.toReal ((multinomialGaussianLaw witness32PDagger)
      {g | witness32LimitStatistic g = 0}) ∧
    ENNReal.toReal ((multinomialGaussianLaw witness32PDagger)
      {g | witness32LimitStatistic g = 0}) < 1 := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
