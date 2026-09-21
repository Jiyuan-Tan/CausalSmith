module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinGrid

set_option linter.style.longLine false

/-! # Certified finite insulin-policy demonstration -/

public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

-- @node: prop:finite-insulin-demonstration
/-- The refreshed insulin witness has 360 states, contraction at most one half,
policy overlap `10/3`, stationary overlap at most 720, and interval-certified
strictly negative immediate-weighting bias. [the stated conclusion](goal). -/
theorem finite_insulin_demonstration (T : Nat) :
    Fintype.card (JointState 90 4) = 360 ∧
    UniformContraction (1 / 2) (insulinGrid T) ∧
    PolicyOverlap (10 / 3) (insulinGrid T) ∧
    LatentStationaryOverlap 720 (insulinGrid T) ∧
    (-(6 / 1000 : ℝ) < immediateWeightBias T ∧
      immediateWeightBias T < -(58 / 10000 : ℝ)) := by
  exact ⟨insulinGrid_card, insulinGrid_contraction T, insulinGrid_policyOverlap T,
    insulinGrid_stationaryOverlap T, insulinGrid_bias_certificate T⟩

end CausalSmith.Stat.PomdpLatentOverlapMinimax
