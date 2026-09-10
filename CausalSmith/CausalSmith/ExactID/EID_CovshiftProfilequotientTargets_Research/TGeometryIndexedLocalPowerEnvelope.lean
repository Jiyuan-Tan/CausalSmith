import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.PowerEnvelope
import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.InformationDistance

/-! # Geometry-indexed local power and failure of a scalar envelope -/

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

/-- One-sided one-dimensional opposite tangent geometry. -/
def oneSidedGeometry (c : ℝ) : TangentGeometry where
  k := 1
  focal := 0
  opposite := {g | c ≤ g 0}

/-- Two-sided one-dimensional opposite tangent geometry. -/
def twoSidedGeometry (c : ℝ) : TangentGeometry where
  k := 1
  focal := 0
  opposite := {g | g 0 ≤ -c ∨ c ≤ g 0}

-- @node: thm:geometry-indexed-local-power-envelope
theorem geometry_indexed_local_power_envelope (α c : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (hc : 0 < c) :
    nearestOppositeDistance (oneSidedGeometry c) = c ∧
    nearestOppositeDistance (twoSidedGeometry c) = c ∧
    gaussianPowerSupremum (oneSidedGeometry c) α =
      Causalean.Mathlib.stdNormalCDF (Causalean.Mathlib.probit α + c) ∧
    (∃ t : ℝ, 0 < t ∧
      Causalean.Mathlib.stdNormalCDF (t - c) -
          Causalean.Mathlib.stdNormalCDF (-t - c) = α ∧
      (∀ u : ℝ, 0 < u →
        Causalean.Mathlib.stdNormalCDF (u - c) -
            Causalean.Mathlib.stdNormalCDF (-u - c) = α → u = t) ∧
      gaussianPowerSupremum (twoSidedGeometry c) α =
        2 * Causalean.Mathlib.stdNormalCDF t - 1 ∧
      gaussianPowerSupremum (twoSidedGeometry c) α <
        gaussianPowerSupremum (oneSidedGeometry c) α) := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets
