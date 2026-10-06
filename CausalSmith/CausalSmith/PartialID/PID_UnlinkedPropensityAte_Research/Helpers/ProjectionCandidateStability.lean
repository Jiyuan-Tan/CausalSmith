module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionCellStability
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionDistanceTriangle
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionScorePopulation

/-! Candidate-to-population endpoint stability for the external projection. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: projectionCandidate_armEndpoint_abs_le
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,x,b,lam,σ,hb,hfinLam,hfinσ,hcompat,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCandidate_armEndpoint_abs_le
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε)
    (x : ExternalSample ε J n m)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hb : b ∈ projectionCandidates g α x)
    (hfinLam : ∀ a r, IsFiniteMeasure (lam a r))
    (hfinσ : ∀ a r, IsFiniteMeasure (σ a r))
    (hcompat : ProjectionCompatible lam σ)
    (a : ArmSpace) (upper : Bool) :
    |projectedArmEndpoint b.1 b.2 a upper -
      projectedArmEndpoint lam σ a upper| ≤
      (ε⁻¹ + (ε ^ 2)⁻¹) *
        (4 * J / (α * Real.sqrt n) +
          (∑ a : ArmSpace, ∑ r : LabelSpace J,
            outcomeCDFDistance (empiricalTrialCells x.1 a r) (lam a r)) +
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
          (∑ a : ArmSpace, ∑ r : LabelSpace J,
            scoreCDFDistance (empiricalScoreCells g x.2 a r) (σ a r))) := by
  have hfinB₁ : ∀ a r, IsFiniteMeasure (b.1 a r) :=
    fun a r => ⟨(hb.1 a r).1⟩
  have hfinB₂ : ∀ a r, IsFiniteMeasure (b.2 a r) :=
    fun a r => ⟨(hb.1 a r).2⟩
  have hε : 0 < ε := hOverlap.1
  have hL : 0 ≤ ε⁻¹ + (ε ^ 2)⁻¹ := by positivity
  have hArm : ∀ a upper,
      |projectedArmEndpoint b.1 b.2 a upper -
        projectedArmEndpoint lam σ a upper| ≤
      (ε⁻¹ + (ε ^ 2)⁻¹) *
        ((∑ r : LabelSpace J,
          outcomeCDFDistance (b.1 a r) (lam a r)) +
          ∑ r : LabelSpace J,
            scoreCDFDistance (b.2 a r) (σ a r)) := by
    intro a upper
    exact projectedArmEndpoint_abs_le_of_compatible_cells hOverlap
      b.1 lam b.2 σ hfinB₁ hfinLam hfinB₂ hfinσ hb.2.1 hcompat a upper
  have hEndpoint := projectedArmEndpoint_abs_le_of_armBounds hOverlap
    b.1 lam b.2 σ (ε⁻¹ + (ε ^ 2)⁻¹) hL hArm a upper
  have hDistance := projectionCandidate_populationDistance_le_of_populationFinite
    g α hOverlap x b lam σ hb
    (fun a r => (hfinLam a r).measure_univ_lt_top)
    (fun a r => (hfinσ a r).measure_univ_lt_top)
  exact hEndpoint.trans (mul_le_mul_of_nonneg_left hDistance hL)

-- @node: projectionCandidate_populationArmEndpoint_abs_le
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,PH,hPH,x,b,hb,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCandidate_populationArmEndpoint_abs_le
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g)
    (x : ExternalSample ε J n m)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (hb : b ∈ projectionCandidates g α x)
    (a : ArmSpace) (upper : Bool) :
    |projectedArmEndpoint b.1 b.2 a upper -
      projectedArmEndpoint (trialPopulationCells (releasedLaw PH.1))
        (scorePopulationCells PH.2 g) a upper| ≤
      (ε⁻¹ + (ε ^ 2)⁻¹) *
        (4 * J / (α * Real.sqrt n) +
          (∑ a : ArmSpace, ∑ r : LabelSpace J,
            outcomeCDFDistance (empiricalTrialCells x.1 a r)
              (trialPopulationCells (releasedLaw PH.1) a r)) +
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
          (∑ a : ArmSpace, ∑ r : LabelSpace J,
            scoreCDFDistance (empiricalScoreCells g x.2 a r)
              (scorePopulationCells PH.2 g a r))) := by
  haveI : IsProbabilityMeasure PH.2 := hPH.2.1
  haveI : IsProbabilityMeasure (releasedLaw PH.1) := by
    unfold releasedLaw
    exact @Measure.isProbabilityMeasure_map _ _ _ _ PH.1 hPH.1 _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  have hfin := projectionPopulationCells_finite PH.2 g (releasedLaw PH.1)
    hPH.2.2.overlap hPH.2.2.measurableRelease
  exact projectionCandidate_armEndpoint_abs_le g α hPH.2.2.overlap x b
    (trialPopulationCells (releasedLaw PH.1)) (scorePopulationCells PH.2 g)
    hb hfin.1 hfin.2
    (projectionCompatible_populationCells PH.2 g (releasedLaw PH.1)
      (externalLawCellMasses g PH hPH) hPH.2.2.overlap) a upper

-- @node: projectionCandidate_populationATEInterval_subset
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,PH,hPH,x,b,hb), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCandidate_populationATEInterval_subset
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g)
    (x : ExternalSample ε J n m)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (hb : b ∈ projectionCandidates g α x) :
    let δ := (ε⁻¹ + (ε ^ 2)⁻¹) *
      (4 * J / (α * Real.sqrt n) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (empiricalTrialCells x.1 a r)
            (trialPopulationCells (releasedLaw PH.1) a r)) +
        2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (empiricalScoreCells g x.2 a r)
            (scorePopulationCells PH.2 g a r)))
    projectedATEInterval b.1 b.2 ⊆
      Set.Icc
        ((projectedArmEndpoint (trialPopulationCells (releasedLaw PH.1))
          (scorePopulationCells PH.2 g) true false -
          projectedArmEndpoint (trialPopulationCells (releasedLaw PH.1))
            (scorePopulationCells PH.2 g) false true) - 2 * δ)
        ((projectedArmEndpoint (trialPopulationCells (releasedLaw PH.1))
          (scorePopulationCells PH.2 g) true true -
          projectedArmEndpoint (trialPopulationCells (releasedLaw PH.1))
            (scorePopulationCells PH.2 g) false false) + 2 * δ) := by
  dsimp
  apply projectedATEInterval_subset_of_armEndpoint_bounds
  intro a upper
  exact projectionCandidate_populationArmEndpoint_abs_le g α PH hPH x b hb a upper

end CausalSmith.PartialID.UnlinkedPropensityAte
