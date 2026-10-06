module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.External
public import Causalean.Stat.Quantile.Quantile
public import Mathlib.Analysis.Convex.Hull

/-! Joint empirical-measure projection for external score-log inference. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section
/-- For [the specified mathematical inputs](hyp:J,α), [this definition](goal) introduces the corresponding object. -/
abbrev ArmCellArray (J : ℕ) (α : Type*) [MeasurableSpace α] :=
  ArmSpace → LabelSpace J → Measure α

/-- For [the specified mathematical inputs](hyp:J,n,x), [this definition](goal) introduces the corresponding object. -/
def empiricalTrialCells {J n : ℕ} (x : TrialSample n J) :
    ArmCellArray J OutcomeSpace :=
  fun a r => ((n : ENNReal)⁻¹) •
    ∑ i : Fin n, if (x i).1 = r ∧ (x i).2.1 = a then
      Measure.dirac (x i).2.2 else 0

/-- For [the specified mathematical inputs](hyp:ε,J,m,g,x), [this definition](goal) introduces the corresponding object. -/
def empiricalScoreCells {ε : ℝ} {J m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (x : Fin m → ScoreSpace ε) :
    ArmCellArray J (ScoreSpace ε) :=
  fun a r => ∑ j : Fin m,
    if g (x j) = r then
      ((ENNReal.ofReal (armProb a (x j))) / m) • Measure.dirac (x j)
    else 0

/-- For [the specified mathematical inputs](hyp:μ,ν), [this definition](goal) introduces the corresponding object. -/
def outcomeCDFDistance (μ ν : Measure OutcomeSpace) : ℝ :=
  |μ.real Set.univ - ν.real Set.univ| +
    ∫ t in (0 : ℝ)..1,
      |(μ {y | (y : ℝ) ≤ t}).toReal - (ν {y | (y : ℝ) ≤ t}).toReal|

/-- For [the specified mathematical inputs](hyp:ε,μ,ν), [this definition](goal) introduces the corresponding object. -/
def scoreCDFDistance {ε : ℝ}
    (μ ν : Measure (ScoreSpace ε)) : ℝ :=
  |μ.real Set.univ - ν.real Set.univ| +
    ∫ t in ε..(1 - ε),
      |(μ {e | (e : ℝ) ≤ t}).toReal - (ν {e | (e : ℝ) ≤ t}).toReal|

/-- For [the specified mathematical inputs](hyp:ε,J,lam,σ), [this definition](goal) introduces the corresponding object. -/
def ProjectionCompatible {ε : ℝ} {J : ℕ}
    (lam : ArmCellArray J OutcomeSpace) (σ : ArmCellArray J (ScoreSpace ε)) : Prop :=
  ∀ a r, (lam a r).real Set.univ = (σ a r).real Set.univ

/-- For [the specified mathematical inputs](hyp:ε,J,lam,σ,a,upper), [this definition](goal) introduces the corresponding object. -/
def projectedArmEndpoint {ε : ℝ} {J : ℕ}
    (lam : ArmCellArray J OutcomeSpace) (σ : ArmCellArray J (ScoreSpace ε))
    (a : ArmSpace) (upper : Bool) : ℝ :=
  ∑ r : LabelSpace J,
    let q := (lam a r).real Set.univ
    if 0 < q then
      q * ∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile
          (((lam a r Set.univ)⁻¹ • (lam a r)).map
            (fun y : OutcomeSpace => (y : ℝ))) u *
        Causalean.Stat.quantile
          (((σ a r Set.univ)⁻¹ • (σ a r)).map
            (fun e => (armProb a e)⁻¹)) (if upper then u else 1 - u)
    else 0

/-- For [the specified mathematical inputs](hyp:q), [this definition](goal) introduces the corresponding object. -/
def rationalOutcomePoint (q : ℚ) : OutcomeSpace :=
  ⟨max 0 (min 1 (q : ℝ)), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)⟩

/-- For [the specified mathematical inputs](hyp:ε,hOverlap,q), [this definition](goal) introduces the corresponding object. -/
def rationalScorePoint (ε : ℝ) (hOverlap : Overlap ε) (q : ℚ) :
    ScoreSpace ε :=
  ⟨ε + (1 - 2 * ε) * (rationalOutcomePoint q : ℝ), by
    have hwidth : 0 ≤ 1 - 2 * ε := by
      dsimp [Overlap] at hOverlap
      linarith [hOverlap.2]
    have hq := (rationalOutcomePoint q).property
    constructor
    · have hm := mul_nonneg hwidth hq.1
      linarith
    · have hm := mul_le_mul_of_nonneg_left hq.2 hwidth
      linarith⟩

/-- For [the specified mathematical inputs](hyp:l), [this definition](goal) introduces the corresponding object. -/
def rationalOutcomeMeasure (l : List (ℚ × ℚ)) : Measure OutcomeSpace :=
  (l.map (fun p => ENNReal.ofReal (p.2 : ℝ) •
    Measure.dirac (rationalOutcomePoint p.1))).sum
/-- For [the specified mathematical inputs](hyp:ε,hOverlap,l), [this definition](goal) introduces the corresponding object. -/
def rationalScoreMeasure (ε : ℝ) (hOverlap : Overlap ε)
    (l : List (ℚ × ℚ)) : Measure (ScoreSpace ε) :=
  (l.map (fun p => ENNReal.ofReal (p.2 : ℝ) •
    Measure.dirac (rationalScorePoint ε hOverlap p.1))).sum

/-- For [the specified mathematical inputs](hyp:ε,J), [this definition](goal) introduces the corresponding object. -/
def rationalArraySieve (ε : ℝ) (J : ℕ) :
    Set (ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε)) := by
  classical
  exact if hOverlap : Overlap ε then
    Set.range (fun code :
        (ArmSpace → LabelSpace J → List (ℚ × ℚ)) ×
          (ArmSpace → LabelSpace J → List (ℚ × ℚ)) =>
      (fun a r => rationalOutcomeMeasure (code.1 a r),
       fun a r => rationalScoreMeasure ε hOverlap (code.2 a r))) ∩
      {b | ProjectionCompatible b.1 b.2}
  else ∅

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,α,x), [this definition](goal) introduces the corresponding object. -/
def projectionCandidates {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) :
    Set (ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε)) :=
  {b | (∀ a r, (b.1 a r) Set.univ < ⊤ ∧ (b.2 a r) Set.univ < ⊤) ∧
    ProjectionCompatible b.1 b.2 ∧
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (b.1 a r) (empiricalTrialCells x.1 a r)) ≤
        4 * J / (α * Real.sqrt n) ∧
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      scoreCDFDistance (b.2 a r) (empiricalScoreCells g x.2 a r)) ≤
        2 * J * (2 - 2 * ε) / (α * Real.sqrt m)}

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,α,x), [this definition](goal) introduces the corresponding object. -/
def sievedProjectionCandidates {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) :
    Set (ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε)) :=
  projectionCandidates g α x ∩ rationalArraySieve ε J

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J), this result [establishes the stated mathematical conclusion](goal). -/
lemma countable_rationalArraySieve (ε : ℝ) (J : ℕ) :
    (rationalArraySieve ε J).Countable := by
  classical
  unfold rationalArraySieve
  split_ifs
  · exact (Set.countable_range _).mono Set.inter_subset_left
  · exact Set.countable_empty

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma countable_sievedProjectionCandidates {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) :
    (sievedProjectionCandidates g α x).Countable := by
  exact (countable_rationalArraySieve ε J).mono Set.inter_subset_right

/-- For [the specified mathematical inputs](hyp:ε,J,lam,σ), [this definition](goal) introduces the corresponding object. -/
def projectedATEInterval {ε : ℝ} {J : ℕ}
    (lam : ArmCellArray J OutcomeSpace) (σ : ArmCellArray J (ScoreSpace ε)) :
    Set ℝ :=
  Set.Icc
    (projectedArmEndpoint lam σ true false - projectedArmEndpoint lam σ false true)
    (projectedArmEndpoint lam σ true true - projectedArmEndpoint lam σ false false)

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,α,x), [this definition](goal) introduces the corresponding object. -/
def sievedTotalizedProjectionCI {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) : Set ℝ := by
  classical
  let B := sievedProjectionCandidates g α x
  let C := Set.Icc (-1 : ℝ) 1 ∩
    closure (convexHull ℝ (⋃ b ∈ B, projectedATEInterval b.1 b.2))
  exact if B.Nonempty ∧ C.Nonempty then C else {0}

-- @node: def:external-projection-handle
/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,α,x), [this definition](goal) introduces the corresponding object. -/
def externalProjectionCI {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) : Set ℝ :=
  sievedTotalizedProjectionCI g α x
  -- @realizes Hext(totalized rational-sieve projection)

end
end CausalSmith.PartialID.UnlinkedPropensityAte
