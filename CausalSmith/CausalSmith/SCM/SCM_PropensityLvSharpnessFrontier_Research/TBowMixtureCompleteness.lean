import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TOneSidedBowMixtureCompleteness

/-! # Mutual-support bow-mixture completeness -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- Mutual-support bow-compatible laws are exactly dominated-residual mixtures
and exactly the mutual-support likelihood-ratio-cap class.  For the specified model objects, [the stated conditions](hyp:hPos), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:bow-mixture-completeness
theorem bowCompatible_eq_mixtureClass
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
    (a : Bool) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) :
    bowCompatibleSet a e P = mixtureClassSet e P ∧
    ∀ Q : Measure Y, Q ∈ mixtureClassSet e P ↔
      IsProbabilityMeasure Q ∧ MutuallyAC Q P ∧
      ∀ᵐ x ∂Q, (P.rnDeriv Q x).toReal ≤ 1 / e := by
  constructor
  · ext Q
    constructor
    · intro hQ
      have hOne : BowCompatibleOneSided a e P Q :=
        { observed_probability := hQ.observed_probability
          intervention_probability := hQ.intervention_probability
          realization := hQ.realization.elim Or.inl
            (fun ⟨w, hp, hb, hc, _, he, hP, hQ⟩ =>
              Or.inr ⟨w, hp, hb, hc, he, hP, hQ⟩)
          bow_structure := hQ.bow_structure
          consistency := hQ.consistency
          positivity := hQ.positivity
          boundary := hQ.boundary }
      have hMixOne : Q ∈ mixtureClassOneSidedSet e P := by
        rw [← (bowCompatibleOneSided_eq_mixtureClassOneSided a e P hPos).1]
        exact hOne
      rcases hQ.realization with hboundary | ⟨w, _, _, hCons, hMut, _, hArm, hInterv⟩
      · exact (ne_of_lt hPos.2 hboundary.1).elim
      · have hPotentialArm := conditionalPotentialOutcomeLaw_eq_armLaw w a hCons
        exact (mixture_reverse_support e P Q hPos).2
          ⟨hMixOne, by simpa [hPotentialArm, hArm, hInterv] using hMut.2⟩
    · intro hQ
      have hsplit := (mixture_reverse_support e P Q hPos).1 hQ
      have hBowOne : BowCompatibleOneSided a e P Q := by
        change Q ∈ bowCompatibleOneSidedSet a e P
        rw [(bowCompatibleOneSided_eq_mixtureClassOneSided a e P hPos).1]
        exact hsplit.1
      rcases hBowOne.realization with hboundary | ⟨w, hp, hb, hc, he, hArm, hInterv⟩
      · exact (ne_of_lt hPos.2 hboundary.1).elim
      · have hForward : P.AbsolutelyContinuous Q :=
          ((bowCompatibleOneSided_eq_mixtureClassOneSided a e P hPos).2 Q).1
            hsplit.1 |>.2.1
        have hMut : MutualAbsCont w a := by
          have hPotentialArm := conditionalPotentialOutcomeLaw_eq_armLaw w a hc
          constructor
          · simpa [hPotentialArm, hArm, hInterv] using hForward
          · simpa [hPotentialArm, hArm, hInterv] using hsplit.2
        exact
          { observed_probability := hQ.observed_probability
            intervention_probability := hQ.candidate_probability
            realization := Or.inr ⟨w, hp, hb, hc, hMut, he, hArm, hInterv⟩
            bow_structure := Or.inr ⟨w, hb⟩
            consistency := Or.inr ⟨w, hc⟩
            positivity := Or.inr hPos
            mutual_ac := Or.inr ⟨w, hMut⟩
            boundary := fun he1 => (ne_of_lt hPos.2 he1).elim }
  · intro Q
    rw [mixture_reverse_support e P Q hPos,
      (bowCompatibleOneSided_eq_mixtureClassOneSided a e P hPos).2 Q]
    constructor
    · rintro ⟨⟨hQ, hPQ, hcap⟩, hQP⟩
      exact ⟨hQ, ⟨hQP, hPQ⟩, hcap⟩
    · rintro ⟨hQ, ⟨hQP, hPQ⟩, hcap⟩
      exact ⟨⟨hQ, hPQ, hcap⟩, hQP⟩

end CausalSmith.SCM.PropensityLvSharpnessFrontier
