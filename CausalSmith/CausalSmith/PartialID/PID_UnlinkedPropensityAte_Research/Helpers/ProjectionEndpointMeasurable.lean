module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionGeometry
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionIntegrated
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
Measurability infrastructure for the endpoints of the external projection interval.

The rational sieve is countable.  This file first proves that admission of each
fixed sieve element is a measurable event of the external sample; these are the
coordinate facts needed to form measurable countable endpoint envelopes.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hμ,a,r), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_outcomeCDFDistance_empirical {J n : ℕ}
    (μ : Measure OutcomeSpace) (hμ : μ Set.univ < ⊤)
    (a : ArmSpace) (r : LabelSpace J) :
    Measurable (fun x : TrialSample n J =>
      outcomeCDFDistance μ (empiricalTrialCells x a r)) := by
  have hmass : Measurable (fun x : TrialSample n J =>
      |μ.real Set.univ - (empiricalTrialCells x a r).real Set.univ|) :=
    (measurable_const.sub
      (measurable_empiricalTrialCells_real_apply a r Set.univ MeasurableSet.univ)).abs
  have hjoint : Measurable (fun p : TrialSample n J × ℝ =>
      |μ.real {y | (y : ℝ) ≤ p.2} -
        (empiricalTrialCells p.1 a r).real {y | (y : ℝ) ≤ p.2}|) :=
    (((measurable_projectionFiniteCDF μ hμ
        (fun y : OutcomeSpace => (y : ℝ))).comp measurable_snd).sub
      (measurable_empiricalTrialCellCDF_joint a r)).abs
  have hint : Measurable (fun x : TrialSample n J =>
      ∫ t in (0 : ℝ)..1,
        |μ.real {y | (y : ℝ) ≤ t} -
          (empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t}|) := by
    rw [show (fun x : TrialSample n J =>
        ∫ t in (0 : ℝ)..1,
          |μ.real {y | (y : ℝ) ≤ t} -
            (empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t}|) =
        fun x => ∫ t,
          |μ.real {y | (y : ℝ) ≤ t} -
            (empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t}|
              ∂(volume.restrict (Set.Ioc 0 1)) by
      funext x
      rw [intervalIntegral.integral_of_le (by norm_num)]]
    exact (hjoint.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioc 0 1))).measurable
  exact hmass.add hint

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,g,hg,σ,hσ,a,r), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_scoreCDFDistance_empirical {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (σ : Measure (ScoreSpace ε))
    (hσ : σ Set.univ < ⊤) (a : ArmSpace) (r : LabelSpace J) :
    Measurable (fun x : Fin m → ScoreSpace ε =>
      scoreCDFDistance σ (empiricalScoreCells g x a r)) := by
  have hmassEval : Measurable (fun x : Fin m → ScoreSpace ε =>
      (empiricalScoreCells g x a r).real Set.univ) := by
    rw [show (fun x : Fin m → ScoreSpace ε =>
        (empiricalScoreCells g x a r).real Set.univ) =
        scoreCellFrequency g a r Set.univ by
      funext x
      exact empiricalScoreCells_real_eq_scoreCellFrequency hOverlap g a r
        Set.univ MeasurableSet.univ x]
    exact measurable_scoreCellFrequency g hg a r Set.univ MeasurableSet.univ
  have hmass : Measurable (fun x : Fin m → ScoreSpace ε =>
      |σ.real Set.univ - (empiricalScoreCells g x a r).real Set.univ|) :=
    (measurable_const.sub hmassEval).abs
  have hjoint : Measurable (fun p : (Fin m → ScoreSpace ε) × ℝ =>
      |σ.real {e | (e : ℝ) ≤ p.2} -
        (empiricalScoreCells g p.1 a r).real {e | (e : ℝ) ≤ p.2}|) :=
    (((measurable_projectionFiniteCDF σ hσ
        (fun e : ScoreSpace ε => (e : ℝ))).comp measurable_snd).sub
      (measurable_empiricalScoreCellCDF_joint hOverlap g hg a r)).abs
  have hε : ε ≤ 1 - ε := by
    dsimp [Overlap] at hOverlap
    linarith [hOverlap.2]
  have hint : Measurable (fun x : Fin m → ScoreSpace ε =>
      ∫ t in ε..(1 - ε),
        |σ.real {e | (e : ℝ) ≤ t} -
          (empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t}|) := by
    rw [show (fun x : Fin m → ScoreSpace ε =>
        ∫ t in ε..(1 - ε),
          |σ.real {e | (e : ℝ) ≤ t} -
            (empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t}|) =
        fun x => ∫ t,
          |σ.real {e | (e : ℝ) ≤ t} -
            (empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t}|
              ∂(volume.restrict (Set.Ioc ε (1 - ε))) by
      funext x
      rw [intervalIntegral.integral_of_le hε]]
    exact (hjoint.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioc ε (1 - ε)))).measurable
  exact hmass.add hint

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,b,x), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def projectionTrialDistance {ε : ℝ} {J n m : ℕ}
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (x : ExternalSample ε J n m) : ℝ :=
  ∑ a : ArmSpace, ∑ r : LabelSpace J,
    outcomeCDFDistance (b.1 a r) (empiricalTrialCells x.1 a r)

/-- For [the specified mathematical inputs](hyp:ε,J,n,m,g,b,x), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def projectionScoreDistance {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (x : ExternalSample ε J n m) : ℝ :=
  ∑ a : ArmSpace, ∑ r : LabelSpace J,
    scoreCDFDistance (b.2 a r) (empiricalScoreCells g x.2 a r)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,b,hfin), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_projectionTrialDistance {ε : ℝ} {J n m : ℕ}
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (hfin : ∀ a r, (b.1 a r) Set.univ < ⊤) :
    Measurable (projectionTrialDistance (n := n) (m := m) b) := by
  unfold projectionTrialDistance
  apply Finset.measurable_sum
  intro a _
  apply Finset.measurable_sum
  intro r _
  exact (measurable_outcomeCDFDistance_empirical (b.1 a r) (hfin a r) a r).comp
    measurable_fst

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,b,hfin), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_projectionScoreDistance {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (hfin : ∀ a r, (b.2 a r) Set.univ < ⊤) :
    Measurable (projectionScoreDistance (n := n) (m := m) g b) := by
  unfold projectionScoreDistance
  apply Finset.measurable_sum
  intro a _
  apply Finset.measurable_sum
  intro r _
  exact (measurable_scoreCDFDistance_empirical hOverlap g hg (b.2 a r)
    (hfin a r) a r).comp measurable_snd

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α,b), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurableSet_mem_projectionCandidates {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α : ℝ)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε)) :
    MeasurableSet {x : ExternalSample ε J n m | b ∈ projectionCandidates g α x} := by
  classical
  by_cases hfin : ∀ a r, (b.1 a r) Set.univ < ⊤ ∧ (b.2 a r) Set.univ < ⊤
  · by_cases hcompat : ProjectionCompatible b.1 b.2
    · have htrial : Measurable (projectionTrialDistance (n := n) (m := m) b) :=
        measurable_projectionTrialDistance b (fun a r => (hfin a r).1)
      have hscore : Measurable (projectionScoreDistance (n := n) (m := m) g b) :=
        measurable_projectionScoreDistance hOverlap g hg b (fun a r => (hfin a r).2)
      have heq : {x : ExternalSample ε J n m |
          b ∈ projectionCandidates g α x} =
          {x | projectionTrialDistance b x ≤ 4 * J / (α * Real.sqrt n)} ∩
          {x | projectionScoreDistance g b x ≤
            2 * J * (2 - 2 * ε) / (α * Real.sqrt m)} := by
        ext x
        simp only [projectionCandidates, Set.mem_ofPred_eq, Set.mem_inter_iff,
          projectionTrialDistance, projectionScoreDistance]
        constructor
        · intro hx
          exact hx.2.2
        · intro hx
          exact ⟨hfin, hcompat, hx⟩
      rw [heq]
      exact (measurableSet_le htrial measurable_const).inter
        (measurableSet_le hscore measurable_const)
    · have heq : {x : ExternalSample ε J n m |
          b ∈ projectionCandidates g α x} = ∅ := by
        ext x
        simp only [projectionCandidates, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        intro hx
        exact hcompat hx.2.1
      rw [heq]
      exact MeasurableSet.empty
  · have heq : {x : ExternalSample ε J n m |
        b ∈ projectionCandidates g α x} = ∅ := by
      ext x
      simp only [projectionCandidates, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]
      intro hx
      exact hfin hx.1
    rw [heq]
    exact MeasurableSet.empty

/-- For [the specified mathematical inputs](hyp:ε,J,b), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def projectedATEIntervalLower {ε : ℝ} {J : ℕ}
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε)) : ℝ :=
  projectedArmEndpoint b.1 b.2 true false -
    projectedArmEndpoint b.1 b.2 false true

/-- For [the specified mathematical inputs](hyp:ε,J,b), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def projectedATEIntervalUpper {ε : ℝ} {J : ℕ}
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε)) : ℝ :=
  projectedArmEndpoint b.1 b.2 true true -
    projectedArmEndpoint b.1 b.2 false false

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,b), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedATEInterval_eq_Icc_endpoints {ε : ℝ} {J : ℕ}
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε)) :
    projectedATEInterval b.1 b.2 =
      Set.Icc (projectedATEIntervalLower b) (projectedATEIntervalUpper b) := by
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α,q), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurableSet_exists_sievedCandidate_lower_lt {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α q : ℝ) :
    MeasurableSet {x : ExternalSample ε J n m |
      ∃ b ∈ sievedProjectionCandidates g α x,
        projectedATEIntervalLower b ≤ projectedATEIntervalUpper b ∧
          projectedATEIntervalLower b < q} := by
  let S := {b ∈ rationalArraySieve ε J |
    projectedATEIntervalLower b ≤ projectedATEIntervalUpper b ∧
      projectedATEIntervalLower b < q}
  have hS : S.Countable :=
    (countable_rationalArraySieve ε J).mono (Set.sep_subset _ _)
  have hmeas : MeasurableSet
      (⋃ b ∈ S, {x : ExternalSample ε J n m |
        b ∈ projectionCandidates g α x}) := by
    exact MeasurableSet.biUnion hS fun b _ =>
      measurableSet_mem_projectionCandidates hOverlap g hg α b
  have heq : {x : ExternalSample ε J n m |
      ∃ b ∈ sievedProjectionCandidates g α x,
        projectedATEIntervalLower b ≤ projectedATEIntervalUpper b ∧
          projectedATEIntervalLower b < q} =
      ⋃ b ∈ S, {x | b ∈ projectionCandidates g α x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sievedProjectionCandidates,
      Set.mem_inter_iff, S]
    aesop
  rw [heq]
  exact hmeas

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,hOverlap,g,hg,α,q), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurableSet_exists_sievedCandidate_lt_upper {ε : ℝ} {J n m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (α q : ℝ) :
    MeasurableSet {x : ExternalSample ε J n m |
      ∃ b ∈ sievedProjectionCandidates g α x,
        projectedATEIntervalLower b ≤ projectedATEIntervalUpper b ∧
          q < projectedATEIntervalUpper b} := by
  let S := {b ∈ rationalArraySieve ε J |
    projectedATEIntervalLower b ≤ projectedATEIntervalUpper b ∧
      q < projectedATEIntervalUpper b}
  have hS : S.Countable :=
    (countable_rationalArraySieve ε J).mono (Set.sep_subset _ _)
  have hmeas : MeasurableSet
      (⋃ b ∈ S, {x : ExternalSample ε J n m |
        b ∈ projectionCandidates g α x}) := by
    exact MeasurableSet.biUnion hS fun b _ =>
      measurableSet_mem_projectionCandidates hOverlap g hg α b
  have heq : {x : ExternalSample ε J n m |
      ∃ b ∈ sievedProjectionCandidates g α x,
        projectedATEIntervalLower b ≤ projectedATEIntervalUpper b ∧
          q < projectedATEIntervalUpper b} =
      ⋃ b ∈ S, {x | b ∈ projectionCandidates g α x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sievedProjectionCandidates,
      Set.mem_inter_iff, S]
    aesop
  rw [heq]
  exact hmeas

end
end CausalSmith.PartialID.UnlinkedPropensityAte
