module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionIntegrated
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionEndpointAlgebra
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionEmpiricalFinite

/-! Triangle bounds for the finite-measure CDF distances in the external projection. -/

public section

open MeasureTheory
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: projectionFiniteCDF_intervalIntegrable
/-- Given [the stated mathematical inputs and assumptions](hyp:X,ν,hν,v,a,b,hab), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionFiniteCDF_intervalIntegrable {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (hν : ν Set.univ < ⊤) (v : X → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => ν.real {x | v x ≤ t}) volume a b := by
  have hInt : IntegrableOn (fun t : ℝ => ν.real {x | v x ≤ t})
      (Set.Icc a b) volume := by
    apply Integrable.of_bound
      (measurable_projectionFiniteCDF ν hν v).aestronglyMeasurable
      (ν.real Set.univ)
    filter_upwards [] with t
    have hle : ν {x | v x ≤ t} ≤ ν Set.univ := measure_mono (Set.subset_univ _)
    have hreal : ν.real {x | v x ≤ t} ≤ ν.real Set.univ := by
      exact ENNReal.toReal_mono (ne_of_lt hν) hle
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hreal
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hInt

-- @node: projectionFiniteCDF_absDiff_intervalIntegrable
/-- Given [the stated mathematical inputs and assumptions](hyp:X,μ,ν,hμ,hν,v,a,b,hab), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionFiniteCDF_absDiff_intervalIntegrable {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (hμ : μ Set.univ < ⊤) (hν : ν Set.univ < ⊤)
    (v : X → ℝ) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ =>
      |(μ {x | v x ≤ t}).toReal - (ν {x | v x ≤ t}).toReal|)
      volume a b := by
  exact ((projectionFiniteCDF_intervalIntegrable μ hμ v hab).sub
    (projectionFiniteCDF_intervalIntegrable ν hν v hab)).abs

-- @node: projectionIntegratedAbs_triangle
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,F,G,H,hFG,hGH,hFH), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionIntegratedAbs_triangle {a b : ℝ} (hab : a ≤ b)
    (F G H : ℝ → ℝ)
    (hFG : IntervalIntegrable (fun t => |F t - G t|) volume a b)
    (hGH : IntervalIntegrable (fun t => |G t - H t|) volume a b)
    (hFH : IntervalIntegrable (fun t => |F t - H t|) volume a b) :
    (∫ t in a..b, |F t - H t|) ≤
      (∫ t in a..b, |F t - G t|) +
        (∫ t in a..b, |G t - H t|) := by
  rw [← intervalIntegral.integral_add hFG hGH]
  apply intervalIntegral.integral_mono_on hab hFH (hFG.add hGH)
  intro t _
  calc
    |F t - H t| = |(F t - G t) + (G t - H t)| := by congr 1; ring
    _ ≤ |F t - G t| + |G t - H t| := abs_add_le _ _

-- @node: outcomeCDFDistance_triangle
/-- Given [the stated mathematical inputs and assumptions](hyp:μ,ν,ξ,hμ,hν,hξ), this result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeCDFDistance_triangle
    (μ ν ξ : Measure OutcomeSpace)
    (hμ : μ Set.univ < ⊤) (hν : ν Set.univ < ⊤)
    (hξ : ξ Set.univ < ⊤) :
    outcomeCDFDistance μ ξ ≤
      outcomeCDFDistance μ ν + outcomeCDFDistance ν ξ := by
  have hmass := abs_sub_le (μ.real Set.univ) (ν.real Set.univ) (ξ.real Set.univ)
  have hcdf := projectionIntegratedAbs_triangle (by norm_num : (0 : ℝ) ≤ 1)
    (fun t => (μ {y | (y : ℝ) ≤ t}).toReal)
    (fun t => (ν {y | (y : ℝ) ≤ t}).toReal)
    (fun t => (ξ {y | (y : ℝ) ≤ t}).toReal)
    (projectionFiniteCDF_absDiff_intervalIntegrable μ ν hμ hν
      (fun y : OutcomeSpace => (y : ℝ)) (by norm_num))
    (projectionFiniteCDF_absDiff_intervalIntegrable ν ξ hν hξ
      (fun y : OutcomeSpace => (y : ℝ)) (by norm_num))
    (projectionFiniteCDF_absDiff_intervalIntegrable μ ξ hμ hξ
      (fun y : OutcomeSpace => (y : ℝ)) (by norm_num))
  dsimp [outcomeCDFDistance]
  linarith

-- @node: scoreCDFDistance_triangle
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,μ,ν,ξ,hμ,hν,hξ), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreCDFDistance_triangle {ε : ℝ} (hOverlap : Overlap ε)
    (μ ν ξ : Measure (ScoreSpace ε))
    (hμ : μ Set.univ < ⊤) (hν : ν Set.univ < ⊤)
    (hξ : ξ Set.univ < ⊤) :
    scoreCDFDistance μ ξ ≤
      scoreCDFDistance μ ν + scoreCDFDistance ν ξ := by
  have hab : ε ≤ 1 - ε := by dsimp [Overlap] at hOverlap; linarith [hOverlap.2]
  have hmass := abs_sub_le (μ.real Set.univ) (ν.real Set.univ) (ξ.real Set.univ)
  have hcdf := projectionIntegratedAbs_triangle hab
    (fun t => (μ {e | (e : ℝ) ≤ t}).toReal)
    (fun t => (ν {e | (e : ℝ) ≤ t}).toReal)
    (fun t => (ξ {e | (e : ℝ) ≤ t}).toReal)
    (projectionFiniteCDF_absDiff_intervalIntegrable μ ν hμ hν
      (fun e : ScoreSpace ε => (e : ℝ)) hab)
    (projectionFiniteCDF_absDiff_intervalIntegrable ν ξ hν hξ
      (fun e : ScoreSpace ε => (e : ℝ)) hab)
    (projectionFiniteCDF_absDiff_intervalIntegrable μ ξ hμ hξ
      (fun e : ScoreSpace ε => (e : ℝ)) hab)
  dsimp [scoreCDFDistance]
  linarith

-- @node: projectionCandidate_populationDistance_le_of_finite
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,x,b,lam,σ,hb,htrialEmp,hscoreEmp,htrialPop,hscorePop), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCandidate_populationDistance_le_of_finite
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε)
    (x : ExternalSample ε J n m)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hb : b ∈ projectionCandidates g α x)
    (htrialEmp : ∀ a r, (empiricalTrialCells x.1 a r) Set.univ < ⊤)
    (hscoreEmp : ∀ a r, (empiricalScoreCells g x.2 a r) Set.univ < ⊤)
    (htrialPop : ∀ a r, (lam a r) Set.univ < ⊤)
    (hscorePop : ∀ a r, (σ a r) Set.univ < ⊤) :
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (b.1 a r) (lam a r)) +
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (b.2 a r) (σ a r)) ≤
      4 * J / (α * Real.sqrt n) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (empiricalTrialCells x.1 a r) (lam a r)) +
      2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (empiricalScoreCells g x.2 a r) (σ a r)) := by
  apply projectionCandidate_populationDistance_le g α x b lam σ hb
  · intro a r
    exact outcomeCDFDistance_triangle _ _ _ (hb.1 a r).1
      (htrialEmp a r) (htrialPop a r)
  · intro a r
    exact scoreCDFDistance_triangle hOverlap _ _ _ (hb.1 a r).2
      (hscoreEmp a r) (hscorePop a r)

-- @node: projectionCandidate_populationDistance_le_of_populationFinite
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,x,b,lam,σ,hb,htrialPop,hscorePop), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCandidate_populationDistance_le_of_populationFinite
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε)
    (x : ExternalSample ε J n m)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hb : b ∈ projectionCandidates g α x)
    (htrialPop : ∀ a r, (lam a r) Set.univ < ⊤)
    (hscorePop : ∀ a r, (σ a r) Set.univ < ⊤) :
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (b.1 a r) (lam a r)) +
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (b.2 a r) (σ a r)) ≤
      4 * J / (α * Real.sqrt n) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (empiricalTrialCells x.1 a r) (lam a r)) +
      2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (empiricalScoreCells g x.2 a r) (σ a r)) := by
  exact projectionCandidate_populationDistance_le_of_finite g α hOverlap x b lam σ hb
    (empiricalTrialCells_finite x.1) (empiricalScoreCells_finite g x.2)
    htrialPop hscorePop

end CausalSmith.PartialID.UnlinkedPropensityAte
