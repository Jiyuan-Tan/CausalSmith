import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T1_FiniteResponseConverse
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.Duality

/-! # Sharp selective-label interval -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open Set

/-- Model targets compatible with one observable law. -/
noncomputable def identifiedModelTargets (d : SLCCDesign)
    (p : ObservableCell d → ℝ) : Set ℝ :=
  {tau | ∃ R : SLCCRealization d,
    modelObservableLaw d R = p ∧ modelUntrialedMean d R = tau}

/-- The identified set is exactly the compact sharp interval; both endpoints
and every intermediate value are attained by legal finite models. -/
-- @node: prop:sharp-selective-label-interval
theorem sharp_selective_label_interval (d : SLCCDesign) :
    ∀ p ∈ observablePolytope (designGeometry d),
      identifiedModelTargets d p =
        Set.Icc (lowerEndpoint (designGeometry d) p) (upperEndpoint (designGeometry d) p) ∧
      (∃ R : SLCCRealization d,
        modelObservableLaw d R = p ∧
        modelUntrialedMean d R = lowerEndpoint (designGeometry d) p) ∧
      (∃ R : SLCCRealization d,
        modelObservableLaw d R = p ∧
        modelUntrialedMean d R = upperEndpoint (designGeometry d) p) := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
