import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.BowConstruction

/-! # One-sided bow-mixture completeness -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- Unrestricted bow-compatible laws are exactly arbitrary-residual mixtures
and exactly the forward-support likelihood-ratio-cap class.  For the specified model objects, [the stated conditions](hyp:hPos), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:one-sided-bow-mixture-completeness
theorem bowCompatibleOneSided_eq_mixtureClassOneSided
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
    (a : Bool) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) :
    bowCompatibleOneSidedSet a e P = mixtureClassOneSidedSet e P ∧
    ∀ Q : Measure Y, Q ∈ mixtureClassOneSidedSet e P ↔
      IsProbabilityMeasure Q ∧ P.AbsolutelyContinuous Q ∧
      ∀ᵐ x ∂Q, (P.rnDeriv Q x).toReal ≤ 1 / e := by
  constructor
  · ext Q
    constructor
    · intro hQ
      rcases hQ.realization with hboundary | ⟨w, _, _, hCons, hProp, hArm, hInterv⟩
      · exact (ne_of_lt hPos.2 hboundary.1).elim
      · apply (mixture_oneSided_iff_measure_le e P Q hPos).2
        refine ⟨hQ.intervention_probability, ?_⟩
        have hle := scaled_armLaw_le_interventionalLaw w a hCons
          (hProp.symm ▸ hPos.1)
        simpa [hProp, hArm, hInterv] using hle
    · intro hQ
      obtain ⟨R, hRprob, hDecomp⟩ := hQ.representation (ne_of_lt hPos.2)
      let _ : IsProbabilityMeasure R := hRprob
      let w :=
        canonicalBowWitness a e P R hPos.1.le hPos.2.le
      have hwCons : POConsistency w :=
        canonicalBowWitness_consistency a e P R hPos.1.le hPos.2.le
      have hwProp : armPropensity w a = e :=
        canonicalBowWitness_propensity a e P R hPos.1.le hPos.2.le
      have hwArm : armLaw w a = P :=
        canonicalBowWitness_armLaw a e P R hPos.1 hPos.2.le
      have hwInterv : interventionalLaw w a = Q := by
        rw [canonicalBowWitness_interventionalLaw a e P R hPos.1.le hPos.2.le]
        exact hDecomp.symm
      exact
        { observed_probability := inferInstance
          intervention_probability := hQ.candidate_probability
          realization := Or.inr ⟨w, hPos, w.probability, hwCons, hwProp, hwArm, hwInterv⟩
          bow_structure := Or.inr ⟨w, w.probability⟩
          consistency := Or.inr ⟨w, hwCons⟩
          positivity := Or.inr hPos
          boundary := fun he => (ne_of_lt hPos.2 he).elim }
  · intro Q
    exact mixture_oneSided_iff_cap e P Q hPos

end CausalSmith.SCM.PropensityLvSharpnessFrontier
