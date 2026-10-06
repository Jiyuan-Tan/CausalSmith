module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionEmpirical

/-! Expected absolute coordinate errors for the empirical projection. -/

public section

open MeasureTheory Set
open scoped BigOperators

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: meanAbs_scoreCellFrequency_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma meanAbs_scoreCellFrequency_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B) :
    ∫ x, |scoreCellFrequency g a r B x -
      ∫ e, {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a) e ∂H|
      ∂Measure.pi (fun _ : Fin m => H) ≤ 1 / (2 * Real.sqrt m) := by
  let C : Set (ScoreSpace ε) := {e | g e = r ∧ e ∈ B}
  let F : ScoreSpace ε → ℝ := C.indicator (armProb a)
  have hC : MeasurableSet C :=
    (measurableSet_eq_fun hg measurable_const).inter hB
  have hp : Measurable (armProb a : ScoreSpace ε → ℝ) := by
    unfold armProb
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hF : Measurable F := hp.indicator hC
  have hbound : ∀ e, F e ∈ Set.Icc (0 : ℝ) 1 := by
    intro e
    by_cases he : e ∈ C
    · simpa [F, Set.indicator, he] using
        (show armProb a e ∈ Set.Icc (0 : ℝ) 1 from
          ⟨le_trans (le_of_lt hOverlap.1) (projectionArmProb_bounds hOverlap a e).1,
            (projectionArmProb_bounds hOverlap a e).2⟩)
    · simp [F, he]
  have hlp : MemLp F 2 H :=
    memLp_of_bounded (Filter.Eventually.of_forall hbound) hF.aestronglyMeasurable 2
  have hcoord (j : Fin m) :
      MemLp (fun x : Fin m → ScoreSpace ε => F (x j)) 2
        (Measure.pi fun _ : Fin m => H) := by
    exact hlp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => H) j)
  have hX : MemLp (scoreCellFrequency g a r B) 2
      (Measure.pi fun _ : Fin m => H) := by
    have hs := memLp_finsetSum Finset.univ (fun j _ => hcoord j)
    have hs' := hs.const_mul (m : ℝ)⁻¹
    unfold scoreCellFrequency
    simpa only [F, C] using hs'
  rw [← integral_scoreCellFrequency_pi hOverlap H g hg hm a r B hB]
  exact projectionMeanAbs_le_inv_two_sqrt
    (Measure.pi fun _ : Fin m => H) (scoreCellFrequency g a r B) m hm hX
    (variance_scoreCellFrequency_pi hOverlap H g hg hm a r B hB)

-- @node: meanAbs_empiricalScoreCells_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma meanAbs_empiricalScoreCells_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B) :
    ∫ x, |(empiricalScoreCells g x a r).real B -
      ∫ e, {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a) e ∂H|
      ∂Measure.pi (fun _ : Fin m => H) ≤ 1 / (2 * Real.sqrt m) := by
  simpa only [empiricalScoreCells_real_eq_scoreCellFrequency hOverlap g a r B hB] using
    meanAbs_scoreCellFrequency_pi hOverlap H g hg hm a r B hB

-- @node: sum_meanAbs_trialCellFrequency_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_meanAbs_trialCellFrequency_pi {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ] (hn : 0 < n)
    (B : ArmSpace → LabelSpace J → Set OutcomeSpace)
    (hB : ∀ a r, MeasurableSet (B a r)) :
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ∫ x, |trialCellFrequency a r (B a r) x -
        μ.real {z | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B a r}|
        ∂Measure.pi (fun _ : Fin n => μ)) ≤ J / Real.sqrt n := by
  calc
    _ ≤ ∑ a : ArmSpace, ∑ _r : LabelSpace J,
        (1 / (2 * Real.sqrt n) : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro r _
      exact meanAbs_trialCellFrequency_pi μ hn a r (B a r) (hB a r)
    _ = J / Real.sqrt n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Fintype.card_bool, nsmul_eq_mul]
      field_simp
      ring

-- @node: sum_meanAbs_empiricalScoreCells_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_meanAbs_empiricalScoreCells_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m)
    (B : ArmSpace → LabelSpace J → Set (ScoreSpace ε))
    (hB : ∀ a r, MeasurableSet (B a r)) :
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ∫ x, |(empiricalScoreCells g x a r).real (B a r) -
        ∫ e, {e : ScoreSpace ε | g e = r ∧ e ∈ B a r}.indicator
          (armProb a) e ∂H|
        ∂Measure.pi (fun _ : Fin m => H)) ≤ J / Real.sqrt m := by
  calc
    _ ≤ ∑ a : ArmSpace, ∑ _r : LabelSpace J,
        (1 / (2 * Real.sqrt m) : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro r _
      exact meanAbs_empiricalScoreCells_pi hOverlap H g hg hm a r (B a r) (hB a r)
    _ = J / Real.sqrt m := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Fintype.card_bool, nsmul_eq_mul]
      field_simp
      ring

end
end CausalSmith.PartialID.UnlinkedPropensityAte
