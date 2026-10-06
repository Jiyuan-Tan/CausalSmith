module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketEndpoint
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketInterior

/-! TWeightedPacketConstruction -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Conditional on the four disclosed classical gates, the explicit normalized packet has every stated weighted bound and cancellation. [Under the stated conditions](hyp:hLocalization_of_gate,hLipschitz_of_gate,hNorm_of_gate,hGamma_of_gate). [This is the stated conclusion](goal). -/
-- @node: thm:weighted-packet-construction
theorem weighted_packet_construction (hLocalization_of_gate : FilteredJacobiLocalization)
    (hLipschitz_of_gate : FilteredJacobiLipschitz)
    (hNorm_of_gate : JacobiNormOrthogonality)
    (hGamma_of_gate : GammaRatioAsymptotic) :
    ∀ kappa ∈ Icc (0 : ℝ) 2, -- @realizes kappa(fixed degeneracy exponent in [0,2])
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ m : ℕ, 4 ≤ m → PacketBounds kappa C c m := by -- @realizes m(packet degrees m≥4)
  intro kappa hkappa
  by_cases hpos : 0 < kappa
  · exact packetendpoint_bounds hLocalization_of_gate hLipschitz_of_gate
      hNorm_of_gate hGamma_of_gate kappa ⟨hpos, hkappa.2⟩
  · have hzero : kappa = 0 := le_antisymm (le_of_not_gt hpos) hkappa.1
    exact packetinterior_bounds hLocalization_of_gate hLipschitz_of_gate
      hNorm_of_gate hGamma_of_gate kappa hzero

end CausalSmith.Stat.NoisydoseWeakdesignTransition
