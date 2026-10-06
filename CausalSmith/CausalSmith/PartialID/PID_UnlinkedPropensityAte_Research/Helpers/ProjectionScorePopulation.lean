module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionPopulation

/-! Population weighted score-cell submeasures for the external projection. -/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: scorePopulationCells
/-- For [the specified mathematical inputs](hyp:ε,J,H,g,a,r), [this definition](goal) introduces the corresponding object. -/
def scorePopulationCells {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (a : ArmSpace) (r : LabelSpace J) : Measure (ScoreSpace ε) :=
  H.withDensity (fun e => ENNReal.ofReal (if g e = r then armProb a e else 0))

-- @node: scorePopulationCells_real_apply
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,hOverlap,H,g,hg,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma scorePopulationCells_real_apply {ε : ℝ} {J : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B) :
    (scorePopulationCells H g a r).real B =
      ∫ e, {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a) e ∂H := by
  let F : ScoreSpace ε → ℝ :=
    {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a)
  have hp : Measurable (armProb a : ScoreSpace ε → ℝ) := by
    unfold armProb
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hC : MeasurableSet {e : ScoreSpace ε | g e = r ∧ e ∈ B} :=
    (measurableSet_eq_fun hg measurable_const).inter hB
  have hF : Measurable F := hp.indicator hC
  have hbound : ∀ e, F e ∈ Set.Icc (0 : ℝ) 1 := by
    intro e
    by_cases he : g e = r ∧ e ∈ B
    · simpa [F, Set.indicator, he] using
        (show armProb a e ∈ Set.Icc (0 : ℝ) 1 from
          ⟨le_trans (le_of_lt hOverlap.1) (projectionArmProb_bounds hOverlap a e).1,
            (projectionArmProb_bounds hOverlap a e).2⟩)
    · simp [F, he]
  have hInt : Integrable F H := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro e
    simpa [Real.norm_eq_abs, abs_of_nonneg (hbound e).1] using (hbound e).2
  unfold scorePopulationCells Measure.real
  rw [withDensity_apply _ hB]
  have hlin : (∫⁻ e in B, ENNReal.ofReal (if g e = r then armProb a e else 0) ∂H) =
      ∫⁻ e, ENNReal.ofReal (F e) ∂H := by
    rw [← lintegral_indicator hB]
    apply lintegral_congr
    intro e
    by_cases he : g e = r <;> by_cases heB : e ∈ B <;>
      simp [F, Set.indicator, he, heB]
  rw [hlin, ← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall (fun e => (hbound e).1))]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun e => (hbound e).1))]

-- @node: scoreCDFDistance_scorePopulationCells
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,x,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreCDFDistance_scorePopulationCells {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (x : Fin m → ScoreSpace ε)
    (a : ArmSpace) (r : LabelSpace J) :
    scoreCDFDistance (empiricalScoreCells g x a r) (scorePopulationCells H g a r) =
      |(empiricalScoreCells g x a r).real Set.univ -
        ∫ e, {e : ScoreSpace ε | g e = r}.indicator (armProb a) e ∂H| +
      ∫ t in ε..(1 - ε),
        |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
          ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
            (armProb a) e ∂H| := by
  unfold scoreCDFDistance
  rw [scorePopulationCells_real_apply hOverlap H g hg a r Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, and_true]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  change |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
      (scorePopulationCells H g a r).real {e | (e : ℝ) ≤ t}| = _
  rw [show (scorePopulationCells H g a r).real {e | (e : ℝ) ≤ t} =
      ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
        (armProb a) e ∂H from
    scorePopulationCells_real_apply hOverlap H g hg a r _
      (measurableSet_le (by fun_prop) measurable_const)]

-- @node: meanScoreCDFDistance_scorePopulationCells_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma meanScoreCDFDistance_scorePopulationCells_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J) :
    ∫ x : Fin m → ScoreSpace ε,
      scoreCDFDistance (empiricalScoreCells g x a r) (scorePopulationCells H g a r)
        ∂Measure.pi (fun _ : Fin m => H) ≤
      (1 - ε) / Real.sqrt m := by
  have hmass : Integrable (fun x : Fin m → ScoreSpace ε =>
      |(empiricalScoreCells g x a r).real Set.univ -
        ∫ e, {e : ScoreSpace ε | g e = r}.indicator (armProb a) e ∂H|)
      (Measure.pi fun _ : Fin m => H) := by
    let F : ScoreSpace ε → ℝ :=
      {e : ScoreSpace ε | g e = r}.indicator (armProb a)
    have hC : MeasurableSet {e : ScoreSpace ε | g e = r} :=
      measurableSet_eq_fun hg measurable_const
    have hp : Measurable (armProb a : ScoreSpace ε → ℝ) := by
      unfold armProb
      cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    have hF : Measurable F := hp.indicator hC
    have hbound : ∀ e, F e ∈ Set.Icc (0 : ℝ) 1 := by
      intro e
      by_cases he : g e = r
      · simpa [F, Set.indicator, he] using
          (show armProb a e ∈ Set.Icc (0 : ℝ) 1 from
            ⟨le_trans (le_of_lt hOverlap.1) (projectionArmProb_bounds hOverlap a e).1,
              (projectionArmProb_bounds hOverlap a e).2⟩)
      · simp [F, he]
    have hlp : MemLp F 2 H :=
      memLp_of_bounded (Filter.Eventually.of_forall hbound) hF.aestronglyMeasurable 2
    have hcoord (j : Fin m) :
        MemLp (fun x : Fin m → ScoreSpace ε => F (x j)) 2
          (Measure.pi fun _ : Fin m => H) :=
      hlp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => H) j)
    have hX : MemLp (scoreCellFrequency g a r Set.univ) 2
        (Measure.pi fun _ : Fin m => H) := by
      have hs := memLp_finsetSum Finset.univ (fun j _ => hcoord j)
      have hs' := hs.const_mul (m : ℝ)⁻¹
      unfold scoreCellFrequency
      simpa only [F, Set.mem_univ, and_true] using hs'
    have hXi : Integrable (scoreCellFrequency g a r Set.univ)
        (Measure.pi fun _ : Fin m => H) :=
      memLp_one_iff_integrable.mp (hX.mono_exponent (by norm_num))
    have hconst : Integrable (fun _ : Fin m → ScoreSpace ε =>
        ∫ e, {e : ScoreSpace ε | g e = r}.indicator (armProb a) e ∂H)
        (Measure.pi fun _ : Fin m => H) := integrable_const _
    convert (hXi.sub hconst).abs using 1
    funext x
    rw [empiricalScoreCells_real_eq_scoreCellFrequency hOverlap g a r
      Set.univ MeasurableSet.univ]
    rfl
  have hcdf : Integrable (fun x : Fin m → ScoreSpace ε =>
      ∫ t in ε..(1 - ε),
        |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
          ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
            (armProb a) e ∂H|)
      (Measure.pi fun _ : Fin m => H) := by
    convert (integrable_empiricalScoreCellCDF_joint
      hOverlap H g hg hm a r).integral_prod_left using 1
    funext x
    rw [intervalIntegral.integral_of_le (by linarith [hOverlap.2])]
    rfl
  simp_rw [scoreCDFDistance_scorePopulationCells hOverlap H g hg]
  rw [integral_add hmass hcdf]
  have h₁ := meanAbs_empiricalScoreCells_pi hOverlap H g hg hm a r
    Set.univ MeasurableSet.univ
  have h₂ := meanIntegratedAbs_empiricalScoreCellCDF_pi hOverlap H g hg hm a r
  have h₁' : (∫ x : Fin m → ScoreSpace ε,
      |(empiricalScoreCells g x a r).real Set.univ -
        ∫ e, {e : ScoreSpace ε | g e = r}.indicator (armProb a) e ∂H|
        ∂Measure.pi (fun _ : Fin m => H)) ≤
      1 / (2 * Real.sqrt m) := by
    simpa only [Set.mem_univ, and_true] using h₁
  calc
    _ ≤ 1 / (2 * Real.sqrt m) + (1 - 2 * ε) / (2 * Real.sqrt m) :=
      add_le_add h₁' h₂
    _ = (1 - ε) / Real.sqrt m := by ring

-- @node: sum_meanScoreCDFDistance_scorePopulationCells_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_meanScoreCDFDistance_scorePopulationCells_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) :
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ∫ x : Fin m → ScoreSpace ε,
        scoreCDFDistance (empiricalScoreCells g x a r) (scorePopulationCells H g a r)
          ∂Measure.pi (fun _ : Fin m => H)) ≤
      J * (2 - 2 * ε) / Real.sqrt m := by
  calc
    _ ≤ ∑ a : ArmSpace, ∑ _r : LabelSpace J,
        ((1 - ε) / Real.sqrt m : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro r _
      exact meanScoreCDFDistance_scorePopulationCells_pi hOverlap H g hg hm a r
    _ = J * (2 - 2 * ε) / Real.sqrt m := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Fintype.card_bool, nsmul_eq_mul]
      ring

-- @node: projectionCompatible_populationCells
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,μ,h,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCompatible_populationCells {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (μ : Measure (Observation J)) (h : CompatibleCellMasses H g μ)
    (hOverlap : Overlap ε) :
    ProjectionCompatible (trialPopulationCells μ) (scorePopulationCells H g) := by
  haveI : IsProbabilityMeasure H := h.1
  intro a r
  rw [trialPopulationCells_real_apply μ a r Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, and_true]
  rw [scorePopulationCells_real_apply hOverlap H g h.2.2.1 a r Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, and_true]
  rw [h.2.2.2 a r]
  simp only [armCellMass, cell]
  rw [← integral_indicator (measurableSet_eq_fun h.2.2.1 measurable_const)]

-- @node: projectionPopulationCells_finite
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,μ,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionPopulationCells_finite {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (μ : Measure (Observation J)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure μ] (hOverlap : Overlap ε) (hg : Measurable g) :
    (∀ a r, IsFiniteMeasure (trialPopulationCells μ a r)) ∧
      ∀ a r, IsFiniteMeasure (scorePopulationCells H g a r) := by
  constructor
  · intro a r
    unfold trialPopulationCells
    infer_instance
  · intro a r
    let F : ScoreSpace ε → ℝ := fun e => if g e = r then armProb a e else 0
    have hF : Measurable F := by
      have hcell : MeasurableSet {e : ScoreSpace ε | g e = r} :=
        measurableSet_eq_fun hg measurable_const
      dsimp [F, armProb]
      cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        exact Measurable.ite hcell (by fun_prop) measurable_const
    have hbound : ∀ e, |F e| ≤ 1 := by
      intro e
      by_cases he : g e = r
      · have hp := projectionArmProb_bounds hOverlap a e
        simpa [F, he, abs_of_nonneg (le_trans hOverlap.1.le hp.1)] using hp.2
      · simp [F, he]
    have hInt : Integrable F H := by
      apply Integrable.of_bound hF.aestronglyMeasurable 1
      exact Filter.Eventually.of_forall (fun e => by simpa [Real.norm_eq_abs] using hbound e)
    unfold scorePopulationCells
    exact isFiniteMeasure_withDensity_ofReal hInt.hasFiniteIntegral

end
end CausalSmith.PartialID.UnlinkedPropensityAte
