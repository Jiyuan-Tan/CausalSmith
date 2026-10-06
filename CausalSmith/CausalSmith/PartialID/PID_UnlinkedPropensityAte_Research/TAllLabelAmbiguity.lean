module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelAmbiguityBridge
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelFairCell
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelSupremumUpper

/-! Exact worst-case ATE ambiguity for arbitrary measurable release cells. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma halfOutcome_endpoint_attainment {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g) :
    (∃ P : Measure (FullRow ε J), IsProbabilityMeasure P ∧
      CompatibleCausalLaw H g (halfOutcomeReleasedLaw H g) P) ∧
    (∃ Pminus Pplus : Measure (FullRow ε J),
      IsProbabilityMeasure Pminus ∧ IsProbabilityMeasure Pplus ∧
      CompatibleCausalLaw H g (halfOutcomeReleasedLaw H g) Pminus ∧
      CompatibleCausalLaw H g (halfOutcomeReleasedLaw H g) Pplus ∧
      ate Pminus =
        muLower H g (halfOutcomeReleasedLaw H g)
          (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) true -
          muUpper H g (halfOutcomeReleasedLaw H g)
            (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) false ∧
      ate Pplus =
        muUpper H g (halfOutcomeReleasedLaw H g)
          (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) true -
          muLower H g (halfOutcomeReleasedLaw H g)
            (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) false ∧
      ate Pplus - ate Pminus =
        sharpATELength H g (halfOutcomeReleasedLaw H g)
          (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg)) := by
  exact compatible_endpointGap_eq_sharpATELength H g
    (halfOutcomeReleasedLaw H g)
    (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) hOverlap

private lemma sharpATELength_congr_releasedMeasure {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel Prel' : Measure (Observation J))
    (hPrel : Prel = Prel')
    (hMass : CompatibleCellMasses H g Prel)
    (hMass' : CompatibleCellMasses H g Prel') :
    sharpATELength H g Prel hMass = sharpATELength H g Prel' hMass' := by
  subst Prel'
  rfl

-- @node: thm:all-label-ambiguity
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
theorem worstCaseAmbiguity_eq {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g) :
    worstCaseAmbiguity H g =
      ∑ r : LabelSpace J,
        (cellAbsoluteDeviation H g true r + cellAbsoluteDeviation H g false r) ∧
    (∃ P : Measure (FullRow ε J), IsProbabilityMeasure P ∧
      CompatibleCausalLaw H g (halfOutcomeReleasedLaw H g) P) ∧
    sharpATELength H g (halfOutcomeReleasedLaw H g)
      (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) =
      worstCaseAmbiguity H g ∧
    (∃ Pminus Pplus : Measure (FullRow ε J),
      IsProbabilityMeasure Pminus ∧ IsProbabilityMeasure Pplus ∧
      CompatibleCausalLaw H g (halfOutcomeReleasedLaw H g) Pminus ∧
      CompatibleCausalLaw H g (halfOutcomeReleasedLaw H g) Pplus ∧
      ate Pminus =
        muLower H g (halfOutcomeReleasedLaw H g)
          (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) true -
          muUpper H g (halfOutcomeReleasedLaw H g)
            (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) false ∧
      ate Pplus =
        muUpper H g (halfOutcomeReleasedLaw H g)
          (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) true -
          muLower H g (halfOutcomeReleasedLaw H g)
            (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) false ∧
      ate Pplus - ate Pminus = worstCaseAmbiguity H g) := by
  let S : ℝ := ∑ r : LabelSpace J,
    (cellAbsoluteDeviation H g true r + cellAbsoluteDeviation H g false r)
  have hupper : worstCaseAmbiguity H g ≤ S :=
    worstCaseAmbiguity_le_sum_cellAbsoluteDeviation H g hOverlap hg
  have hfair :
      sharpATELength H g (halfOutcomeReleasedLaw H g)
          (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) = S :=
    halfOutcome_sharpATELength_eq_sum_cellAbsoluteDeviation H g hOverlap hg
  rcases halfOutcome_endpoint_attainment H g hOverlap hg with
    ⟨hexists, hendpoint⟩
  rcases hexists with ⟨P, hPprob, hPcomp⟩
  have hPrandom : RandomizedCausalLaw H g P :=
    { probability := hPcomp.probability
      measurableRelease := hPcomp.measurableRelease
      scoreMarginal := hPcomp.scoreMarginal
      randomizedAssignment := hPcomp.randomizedAssignment
      consistency := hPcomp.consistency
      deterministicRelease := hPcomp.deterministicRelease }
  let A : Set ℝ := {d : ℝ | ∃ P : Measure (FullRow ε J),
    ∃ (_hprob : IsProbabilityMeasure P), ∃ hP : RandomizedCausalLaw H g P,
      d = sharpATELength H g (releasedLaw P)
        (compatibleCellMasses_of_randomizedCausalLaw H g P hP)}
  have hAbdd : BddAbove A := by
    refine ⟨S, ?_⟩
    rintro d ⟨Q, hQprob, hQ, rfl⟩
    exact randomizedCausalLaw_sharpATELength_le_sum_cellAbsoluteDeviation
      H g hOverlap Q hQ
  have hfairMem :
      sharpATELength H g (halfOutcomeReleasedLaw H g)
        (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) ∈ A := by
    refine ⟨P, hPprob, hPrandom, ?_⟩
    exact (sharpATELength_congr_releasedMeasure H g
      (releasedLaw P) (halfOutcomeReleasedLaw H g) hPcomp.releasedLaw
      (compatibleCellMasses_of_randomizedCausalLaw H g P hPrandom)
      (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg)).symm
  have hlower : S ≤ worstCaseAmbiguity H g := by
    rw [← hfair]
    unfold worstCaseAmbiguity
    exact le_csSup hAbdd hfairMem
  have heq : worstCaseAmbiguity H g = S := le_antisymm hupper hlower
  refine ⟨heq, ⟨P, hPprob, hPcomp⟩, hfair.trans heq.symm, ?_⟩
  rcases hendpoint with
    ⟨Pminus, Pplus, hminusProb, hplusProb, hminusComp, hplusComp,
      hminus, hplus, hgap⟩
  exact ⟨Pminus, Pplus, hminusProb, hplusProb, hminusComp, hplusComp,
    hminus, hplus, hgap.trans (hfair.trans heq.symm)⟩

end
end CausalSmith.PartialID.UnlinkedPropensityAte
