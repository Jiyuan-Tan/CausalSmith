import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentGeometry
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.Convex.Intrinsic

/-! # Dirac boundary regression -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open MeasureTheory

/-- For plate size at least two, the moment vector of a point mass has a
singleton fiber and is point identified at the causal integrand. -/
-- @node: prop:boundary-dirac-regression
theorem boundary_dirac_regression (m : ℕ) (ε : ℝ) :
    2 ≤ m → ∀ qstar ∈ overlapSimplex ε,
      momentFiber m ε (momentMap m qstar) = {Measure.dirac qstar} ∧
      lowerEndpoint m ε (momentMap m qstar) = causalIntegrand qstar ∧
      upperEndpoint m ε (momentMap m qstar) = causalIntegrand qstar ∧
      momentMap m qstar ∈ intrinsicFrontier ℝ (bernsteinMomentBody m ε) := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
