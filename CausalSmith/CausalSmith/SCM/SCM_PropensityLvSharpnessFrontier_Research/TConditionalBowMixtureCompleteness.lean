import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TConditionalOneSidedBowMixtureCompleteness
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TConditionalMutualSupportIntersection

/-! # Conditional mutual-support bow-mixture completeness -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set

/-- Under common-conull reverse support, the globally realizable conditional
bow class equals the dominated-residual kernel-mixture class, equivalently the
mutual likelihood-ratio-cap class.  For the specified model objects, [the stated conditions](hyp:hOverlap,hP), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:conditional-bow-mixture-completeness
theorem condBowCompatible_eq_condMixtureClass
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [PolishSpace X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
    (kappa : ℝ) (muX : Measure X) [IsProbabilityMeasure muX]
    (e : Bool → X → ℝ) (P : Bool → Kernel X Y)
    (hOverlap : CondOverlap kappa e) (hP : ∀ a, IsMarkovKernel (P a)) :
    condBowCompatibleSet kappa muX e P = condMixtureClassSet kappa muX e P ∧
    condMixtureClassSet kappa muX e P =
      condCapSet muX e P ∩ reverseSupportSet muX P := by
  have hOne := condBowCompatibleOneSided_eq_condMixtureClassOneSided
    kappa muX e P hOverlap hP
  have hInter := cond_mutual_support_intersection kappa muX e P hOverlap hP
  constructor
  · calc
      condBowCompatibleSet kappa muX e P =
          condBowCompatibleOneSidedSet kappa muX e P ∩ reverseSupportSet muX P :=
        hInter.1
      _ = condMixtureClassOneSidedSet kappa muX e P ∩ reverseSupportSet muX P :=
        congrArg (fun S => S ∩ reverseSupportSet muX P) hOne.1
      _ = condMixtureClassSet kappa muX e P := hInter.2.1.symm
  · calc
      condMixtureClassSet kappa muX e P =
          condMixtureClassOneSidedSet kappa muX e P ∩ reverseSupportSet muX P :=
        hInter.2.1
      _ = condCapSet muX e P ∩ reverseSupportSet muX P :=
        congrArg (fun S => S ∩ reverseSupportSet muX P) hOne.2

end CausalSmith.SCM.PropensityLvSharpnessFrontier
