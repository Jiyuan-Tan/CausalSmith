import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.AdaptiveHinge
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TConditionalBowMixtureCompleteness

/-! # Conditional propensity-adaptive hinge exactness -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set

/-- The jointly indexed adaptive hinge is measurable and fiberwise admissible,
has zero calibrated radius, and gives the exact global conditional classes in
both support regimes on one common conull set.  For the specified model objects, [the stated conditions](hyp:hOverlap,hP), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:conditional-adaptive-hinge-exactness
theorem cond_adaptiveHinge_exactness
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [PolishSpace X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
    (kappa : ℝ) (muX : Measure X) [IsProbabilityMeasure muX]
    (e : Bool → X → ℝ) (P : Bool → Kernel X Y)
    (hOverlap : CondOverlap kappa e) (hP : ∀ a, IsMarkovKernel (P a)) :
    Measurable (fun z : Bool × X × ℝ => adaptiveHinge (e z.1 z.2.1) z.2.2) ∧
    (∀ a x, AdmissibleGenerator (adaptiveHinge (e a x)) ∧
      divRadius (adaptiveHinge (e a x)) (e a x) = 0) ∧
    condAdaptiveHingeBallOneSidedSet kappa muX e P =
      condMixtureClassOneSidedSet kappa muX e P ∧
    condMixtureClassOneSidedSet kappa muX e P =
      condBowCompatibleOneSidedSet kappa muX e P ∧
    condAdaptiveHingeBallSet kappa muX e P = condMixtureClassSet kappa muX e P ∧
    condMixtureClassSet kappa muX e P = condBowCompatibleSet kappa muX e P := by
  have hOne := condBowCompatibleOneSided_eq_condMixtureClassOneSided
    kappa muX e P hOverlap hP
  have hMut := condBowCompatible_eq_condMixtureClass kappa muX e P hOverlap hP
  have hInter := cond_mutual_support_intersection kappa muX e P hOverlap hP
  have hBallCap := condAdaptiveHingeBallOneSided_eq_condCap
    kappa muX e P hOverlap hP
  refine ⟨measurable_adaptiveHinge_joint e hOverlap.2.2.1.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro a x
    have heRange := hOverlap.2.2.2 x a
    have hePos : StrictPositivity (e a x) := by
      constructor <;> linarith [hOverlap.1, heRange.1, heRange.2]
    exact adaptiveHinge_admissible_and_radius (e a x) hePos
  · calc
      condAdaptiveHingeBallOneSidedSet kappa muX e P = condCapSet muX e P :=
        hBallCap
      _ = condMixtureClassOneSidedSet kappa muX e P := hOne.2.symm
  · exact hOne.1.symm
  · calc
      condAdaptiveHingeBallSet kappa muX e P =
          condAdaptiveHingeBallOneSidedSet kappa muX e P ∩
            reverseSupportSet muX P := hInter.2.2.1
      _ = condCapSet muX e P ∩ reverseSupportSet muX P :=
        congrArg (fun S => S ∩ reverseSupportSet muX P) hBallCap
      _ = condMixtureClassSet kappa muX e P := hMut.2.symm
  · exact hMut.1.symm

end CausalSmith.SCM.PropensityLvSharpnessFrontier
