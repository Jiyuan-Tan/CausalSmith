import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T2_SharpInterval

/-! # Reduction to a trialed configuration and a full-revelation counterexample -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped ENNReal
open MeasureTheory

/-- The randomized arm mean written without conditional-expectation notation. -/
noncomputable def randomizedArmMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {J : Type*} [DecidableEq J]
    (D : Ω → J) (Y : Ω → Bool) (j : J) : ℝ :=
  (∫ ω, if D ω = j ∧ Y ω then 1 else 0 ∂μ) /
    ENNReal.toReal (μ {ω | D ω = j})

/-- Configuration overlap with a randomized arm point-identifies the
untrialed mean.  Separately, complete label revelation does not identify a
distinct untrialed configuration, as witnessed by two legal models with the
same fully labelled trial law and different targets. -/
-- @node: prop:trialed-policy-reduction
theorem trialed_policy_reduction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : SLCCDesign) (D : Ω → d.TrialArm) (S : Ω → d.Stratum)
    (Z : Ω → Bool) (Ac Yc : Ω → (Bool × d.Performance) → Bool)
    (A Y R : Ω → Bool) (Zobs : Ω → MaskedLabel)
    (hRandomized : RandomizedPolicyAssignment d μ D S Z Ac Yc)
    (hKnown : KnownArmLaw d μ D)
    (hAction : CommonActionResponse d D S Ac A)
    (hOutcome : CommonOutcomeResponse d D S Yc Y)
    (hReveal : RevealAction μ R A)
    (hMask : MaskedTruth μ Z R Zobs)
    (hCorrect : ∀ ω, CounterfactualCorrectness d (Z ω) (Yc ω))
    (hCorrectOrder : ∀ ω, CorrectPerformanceOrder d (Z ω) (Yc ω))
    (hIncorrectOrder : ∀ ω, IncorrectPerformanceOrder d (Z ω) (Yc ω))
    (hNeutral : ∀ ω, NeutralPerformanceInvariance d (Yc ω)) :
    (∀ jStar : d.TrialArm,
      (∀ s, d.config d.untrialed s = d.config (d.trialPolicy jStar) s) →
      let p : ObservableCell d → ℝ := fun o => ENNReal.toReal
        (μ {ω | D ω = o.arm ∧ S ω = o.stratum ∧ A ω = o.action ∧
          Y ω = o.outcome ∧ Zobs ω = o.label})
      lowerEndpoint (designGeometry d) p = randomizedArmMean μ D Y jStar ∧
      upperEndpoint (designGeometry d) p = randomizedArmMean μ D Y jStar) ∧
    (∃ d' : SLCCDesign, ∃ R1 R2 : SLCCRealization d',
      (∀ ω c, R1.model.Ac ω c = true) ∧
      (∀ ω c, R2.model.Ac ω c = true) ∧
      modelObservableLaw d' R1 = modelObservableLaw d' R2 ∧
      modelUntrialedMean d' R1 ≠ modelUntrialedMean d' R2) := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
