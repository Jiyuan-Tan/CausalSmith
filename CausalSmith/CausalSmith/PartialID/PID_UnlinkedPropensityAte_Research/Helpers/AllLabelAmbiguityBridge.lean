module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLaw

/-! Structural endpoint bridge for all-label ambiguity. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatible_endpointGap_eq_sharpATELength {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) :
    (∃ P : Measure (FullRow ε J), IsProbabilityMeasure P ∧
      CompatibleCausalLaw H g Prel P) ∧
    (∃ Pminus Pplus : Measure (FullRow ε J),
      IsProbabilityMeasure Pminus ∧ IsProbabilityMeasure Pplus ∧
      CompatibleCausalLaw H g Prel Pminus ∧
      CompatibleCausalLaw H g Prel Pplus ∧
      ate Pminus = muLower H g Prel hMass true -
        muUpper H g Prel hMass false ∧
      ate Pplus = muUpper H g Prel hMass true -
        muLower H g Prel hMass false ∧
      ate Pplus - ate Pminus = sharpATELength H g Prel hMass) := by
  let Pminus := endpointFullLaw H g Prel hMass hOverlap true false
  let Pplus := endpointFullLaw H g Prel hMass hOverlap false true
  have hminus : CompatibleCausalLaw H g Prel Pminus :=
    endpointFullLaw_compatibleCausalLaw H g Prel hMass hOverlap true false
  have hplus : CompatibleCausalLaw H g Prel Pplus :=
    endpointFullLaw_compatibleCausalLaw H g Prel hMass hOverlap false true
  have hminusAte : ate Pminus = muLower H g Prel hMass true -
      muUpper H g Prel hMass false := by
    letI : IsProbabilityMeasure Pminus := hminus.probability
    rw [ate_eq_potentialOutcomeMeans_sub]
    have h1 := endpointFullLaw_armMean H g Prel hMass hOverlap true false true
    have h0 := endpointFullLaw_armMean H g Prel hMass hOverlap true false false
    simpa [Pminus] using congrArg₂ (· - ·) h1 h0
  have hplusAte : ate Pplus = muUpper H g Prel hMass true -
      muLower H g Prel hMass false := by
    letI : IsProbabilityMeasure Pplus := hplus.probability
    rw [ate_eq_potentialOutcomeMeans_sub]
    have h1 := endpointFullLaw_armMean H g Prel hMass hOverlap false true true
    have h0 := endpointFullLaw_armMean H g Prel hMass hOverlap false true false
    simpa [Pplus] using congrArg₂ (· - ·) h1 h0
  refine ⟨⟨Pminus, hminus.probability, hminus⟩,
    Pminus, Pplus, hminus.probability, hplus.probability,
    hminus, hplus, hminusAte, hplusAte, ?_⟩
  rw [hminusAte, hplusAte]
  unfold sharpATELength
  ring

end
end CausalSmith.PartialID.UnlinkedPropensityAte
