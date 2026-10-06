module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelDefinitions
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelUpperCell
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.CompatibilityFullLawConstruction

/-!
# Universal upper bound for worst case all-label ambiguity

The cellwise reciprocal-score deviation bounds are aggregated over both arms
and then lifted through the supremum over randomized causal laws.
-/

public section

open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,P,hP), this result [establishes the stated mathematical conclusion](goal). -/
lemma randomizedCausalLaw_sharpATELength_le_sum_cellAbsoluteDeviation
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (hOverlap : Overlap ε) (P : Measure (FullRow ε J))
    (hP : RandomizedCausalLaw H g P) :
    sharpATELength H g (releasedLaw P)
        (compatibleCellMasses_of_randomizedCausalLaw H g P hP) ≤
      ∑ r : LabelSpace J,
        (cellAbsoluteDeviation H g true r +
          cellAbsoluteDeviation H g false r) := by
  let hMass := compatibleCellMasses_of_randomizedCausalLaw H g P hP
  have htrue := muUpper_sub_muLower_le_sum_cellAbsoluteDeviation
    H g (releasedLaw P) hMass hOverlap true
  have hfalse := muUpper_sub_muLower_le_sum_cellAbsoluteDeviation
    H g (releasedLaw P) hMass hOverlap false
  unfold sharpATELength
  rw [Finset.sum_add_distrib]
  linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma worstCaseAmbiguity_le_sum_cellAbsoluteDeviation {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g) :
    worstCaseAmbiguity H g ≤
      ∑ r : LabelSpace J,
        (cellAbsoluteDeviation H g true r +
          cellAbsoluteDeviation H g false r) := by
  unfold worstCaseAmbiguity
  apply csSup_le
  · let Prel := halfOutcomeReleasedLaw H g
    let hMass : CompatibleCellMasses H g Prel :=
      halfOutcomeReleasedLaw_cellMasses H g hOverlap hg
    letI : IsProbabilityMeasure Prel := hMass.2.1
    let P := reconstructedFullLaw H g Prel hg
    have hComp : CompatibleCausalLaw H g Prel P :=
      reconstructedFullLaw_compatibleCausalLaw H g Prel hg hMass hOverlap
    have hRandom : RandomizedCausalLaw H g P :=
      { probability := hComp.probability
        measurableRelease := hComp.measurableRelease
        scoreMarginal := hComp.scoreMarginal
        randomizedAssignment := hComp.randomizedAssignment
        consistency := hComp.consistency
        deterministicRelease := hComp.deterministicRelease }
    exact ⟨sharpATELength H g (releasedLaw P)
        (compatibleCellMasses_of_randomizedCausalLaw H g P hRandom),
      P, hRandom.probability, hRandom, rfl⟩
  · intro d hd
    rcases hd with ⟨P, hprob, hP, rfl⟩
    exact randomizedCausalLaw_sharpATELength_le_sum_cellAbsoluteDeviation
      H g hOverlap P hP

end
end CausalSmith.PartialID.UnlinkedPropensityAte
