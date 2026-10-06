module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionSieveDensityBridge

/-! Arbitrarily close finite candidates inside strict projection balls. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: exists_sievedProjectionCandidate_close_of_slack
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,α,x,lam,σ,hfinite,hcompat,η,hη,hout,hscore), this result [establishes the stated mathematical conclusion](goal). -/
lemma exists_sievedProjectionCandidate_close_of_slack
    {ε : ℝ} {J n m : ℕ} (hOverlap : Overlap ε)
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m)
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hfinite : ∀ a r, (lam a r) Set.univ < ⊤ ∧ (σ a r) Set.univ < ⊤)
    (hcompat : ProjectionCompatible lam σ)
    (η : ℝ) (hη : 0 < η)
    (hout : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (lam a r) (empiricalTrialCells x.1 a r)) + η ≤
        4 * J / (α * Real.sqrt n))
    (hscore : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      scoreCDFDistance (σ a r) (empiricalScoreCells g x.2 a r)) + η ≤
        2 * J * (2 - 2 * ε) / (α * Real.sqrt m)) :
    ∃ b ∈ sievedProjectionCandidates g α x,
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        (outcomeCDFDistance (lam a r) (b.1 a r) +
          scoreCDFDistance (σ a r) (b.2 a r))) < η := by
  classical
  obtain ⟨code, hsieve, hcompatB, hdist⟩ :=
    exists_rationalSieveArray_close hOverlap lam σ hfinite hcompat η hη
  let b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε) :=
    ((fun a r => synchronizedRationalOutcomeMeasure (code a r)),
      (fun a r => synchronizedRationalScoreMeasure ε hOverlap (code a r)))
  have hbfinite : ∀ a r, (b.1 a r) Set.univ < ⊤ ∧ (b.2 a r) Set.univ < ⊤ := by
    intro a r
    exact ⟨synchronizedRationalOutcomeMeasure_finite (code a r),
      synchronizedRationalScoreMeasure_finite hOverlap (code a r)⟩
  have hnonnegOut : 0 ≤ ∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (lam a r) (b.1 a r) :=
    Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun r _ => outcomeCDFDistance_nonneg _ _))
  have hnonnegScore : 0 ≤ ∑ a : ArmSpace, ∑ r : LabelSpace J,
      scoreCDFDistance (σ a r) (b.2 a r) :=
    Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun r _ => scoreCDFDistance_nonneg hOverlap _ _))
  have houtClose :
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (b.1 a r) (lam a r)) +
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (lam a r) (empiricalTrialCells x.1 a r)) ≤
          4 * J / (α * Real.sqrt n) := by
    simp_rw [outcomeCDFDistance_symm (b.1 _ _) (lam _ _)]
    have hdist' :
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (lam a r) (b.1 a r)) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (σ a r) (b.2 a r)) < η := by
      simpa only [b, Finset.sum_add_distrib] using hdist
    linarith
  have hscoreClose :
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (b.2 a r) (σ a r)) +
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (σ a r) (empiricalScoreCells g x.2 a r)) ≤
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m) := by
    simp_rw [scoreCDFDistance_symm (b.2 _ _) (σ _ _)]
    have hdist' :
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (lam a r) (b.1 a r)) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (σ a r) (b.2 a r)) < η := by
      simpa only [b, Finset.sum_add_distrib] using hdist
    linarith
  refine ⟨b, ?_, ?_⟩
  · exact ⟨projectionCandidate_of_strict_population_slack hOverlap g α x lam σ b
      hbfinite hcompatB hfinite houtClose hscoreClose, hsieve⟩
  · exact hdist

end
end CausalSmith.PartialID.UnlinkedPropensityAte
