module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionInference
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionRiskEnvelope
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionSharpLength

/-!
Expected excess-length bounds obtained by integrating the deterministic
projection-risk envelope.
-/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: integrable_outcomeCDFDistance_population_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma integrable_outcomeCDFDistance_population_pi {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ] (hn : 0 < n)
    (a : ArmSpace) (r : LabelSpace J) :
    Integrable (fun x : TrialSample n J =>
      outcomeCDFDistance (empiricalTrialCells x a r) (trialPopulationCells μ a r))
      (Measure.pi fun _ : Fin n => μ) := by
  have hmass : Integrable (fun x : TrialSample n J =>
      |(empiricalTrialCells x a r).real Set.univ -
        μ.real {z | z.1 = r ∧ z.2.1 = a}|)
      (Measure.pi fun _ : Fin n => μ) := by
    have hmeas : Measurable (fun x : TrialSample n J =>
        |(empiricalTrialCells x a r).real Set.univ -
          μ.real {z | z.1 = r ∧ z.2.1 = a}|) := by
      exact ((measurable_empiricalTrialCells_real_apply a r Set.univ
        MeasurableSet.univ).sub measurable_const).abs
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    have hset : {y : OutcomeSpace | (y : ℝ) ≤ 1} = Set.univ := by
      ext y
      simp [y.property.2]
    have hx := empiricalTrialCellCDF_mem_Icc hn a r x 1
    have hp := trialPopulationCellCDF_mem_Icc μ a r 1
    rw [hset] at hx
    have hpop : {z : Observation J | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ 1} =
        {z | z.1 = r ∧ z.2.1 = a} := by
      ext z
      simp [z.2.2.property.2]
    rw [hpop] at hp
    dsimp
    rw [abs_abs]
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hp.1, hp.2]
  have hcdf : Integrable (fun x : TrialSample n J =>
      ∫ t in (0 : ℝ)..1,
        |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
          μ.real {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}|)
      (Measure.pi fun _ : Fin n => μ) := by
    convert (integrable_empiricalTrialCellCDF_joint μ hn a r).integral_prod_left using 1
    funext x
    rw [intervalIntegral.integral_of_le (by norm_num)]
    rfl
  rw [show (fun x : TrialSample n J =>
      outcomeCDFDistance (empiricalTrialCells x a r) (trialPopulationCells μ a r)) =
    fun x =>
      |(empiricalTrialCells x a r).real Set.univ -
        μ.real {z | z.1 = r ∧ z.2.1 = a}| +
      ∫ t in (0 : ℝ)..1,
        |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
          μ.real {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}| by
    funext x
    exact outcomeCDFDistance_trialPopulationCells μ x a r]
  exact hmass.add hcdf

-- @node: integrable_scoreCDFDistance_population_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma integrable_scoreCDFDistance_population_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J) :
    Integrable (fun x : Fin m → ScoreSpace ε =>
      scoreCDFDistance (empiricalScoreCells g x a r) (scorePopulationCells H g a r))
      (Measure.pi fun _ : Fin m => H) := by
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
  rw [show (fun x : Fin m → ScoreSpace ε =>
      scoreCDFDistance (empiricalScoreCells g x a r) (scorePopulationCells H g a r)) =
    fun x =>
      |(empiricalScoreCells g x a r).real Set.univ -
        ∫ e, {e : ScoreSpace ε | g e = r}.indicator (armProb a) e ∂H| +
      ∫ t in ε..(1 - ε),
        |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
          ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
            (armProb a) e ∂H| by
    funext x
    exact scoreCDFDistance_scorePopulationCells hOverlap H g hg x a r]
  exact hmass.add hcdf

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hTrial,hLog,hInd,PH,hPH,hn,hm,α,hα,hSharp), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionIntervalProcedure_population_meanExcessLength_le_of_sharp_nonneg
    {ε : ℝ} {J n m : ℕ} (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) (hn : 0 < n) (hm : 0 < m)
    (α : ℝ) (hα : 0 < α)
    (hSharp : 0 ≤ sharpATELength PH.2 g (releasedLaw PH.1)
      (externalLawCellMasses g PH hPH)) :
    ∫ x, max 0
        ((externalProjectionIntervalProcedure g α hPH.2.2.overlap
          hPH.2.2.measurableRelease).length x -
        sharpATELength PH.2 g (releasedLaw PH.1)
          (externalLawCellMasses g PH hPH)) ∂Qj PH.1 PH.2 ≤
      4 * (ε⁻¹ + (ε ^ 2)⁻¹) *
        (4 * J / (α * Real.sqrt n) + 2 * J / Real.sqrt n +
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
          J * (2 - 2 * ε) / Real.sqrt m) := by
  let μ := releasedLaw PH.1
  let H := PH.2
  let F : ExternalSample ε J n m → ℝ := fun x =>
    ∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (empiricalTrialCells x.1 a r)
        (trialPopulationCells μ a r)
  let G : ExternalSample ε J n m → ℝ := fun x =>
    ∑ a : ArmSpace, ∑ r : LabelSpace J,
      scoreCDFDistance (empiricalScoreCells g x.2 a r)
        (scorePopulationCells H g a r)
  haveI : IsProbabilityMeasure PH.1 := hPH.1
  haveI : IsProbabilityMeasure H := hPH.2.1
  haveI : IsProbabilityMeasure μ := by
    unfold μ releasedLaw
    exact @Measure.isProbabilityMeasure_map _ _ _ _ PH.1 hPH.1 _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  haveI : IsProbabilityMeasure (Qj PH.1 PH.2) := by
    rw [externalJointLaw_eq_experiment g Qj hTrial hLog hInd PH hPH]
    dsimp [externalExperiment]
    infer_instance
  have hfin := projectionPopulationCells_finite H g μ hPH.2.2.overlap
    hPH.2.2.measurableRelease
  have hFTmeas : Measurable (fun x : TrialSample n J =>
      ∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (empiricalTrialCells x a r)
          (trialPopulationCells μ a r)) := by
    apply Finset.measurable_sum
    intro a _
    apply Finset.measurable_sum
    intro r _
    letI : IsFiniteMeasure (trialPopulationCells μ a r) := hfin.1 a r
    simpa only [outcomeCDFDistance, abs_sub_comm] using
      measurable_outcomeCDFDistance_empirical (trialPopulationCells μ a r)
        (measure_lt_top _ _) a r
  have hGTmeas : Measurable (fun x : Fin m → ScoreSpace ε =>
      ∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (empiricalScoreCells g x a r)
          (scorePopulationCells H g a r)) := by
    apply Finset.measurable_sum
    intro a _
    apply Finset.measurable_sum
    intro r _
    letI : IsFiniteMeasure (scorePopulationCells H g a r) := hfin.2 a r
    simpa only [scoreCDFDistance, abs_sub_comm] using
      measurable_scoreCDFDistance_empirical hPH.2.2.overlap g
        hPH.2.2.measurableRelease (scorePopulationCells H g a r)
        (measure_lt_top _ _) a r
  have hFmeas : Measurable F := by
    exact hFTmeas.comp measurable_fst
  have hGmeas : Measurable G := by
    exact hGTmeas.comp measurable_snd
  have hFpi : Integrable (fun x : TrialSample n J =>
      ∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (empiricalTrialCells x a r)
          (trialPopulationCells μ a r))
      (Measure.pi fun _ : Fin n => μ) := by
    exact integrable_finsetSum _ (fun a _ =>
      integrable_finsetSum _ (fun r _ =>
        integrable_outcomeCDFDistance_population_pi μ hn a r))
  have hGpi : Integrable (fun x : Fin m → ScoreSpace ε =>
      ∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (empiricalScoreCells g x a r)
          (scorePopulationCells H g a r))
      (Measure.pi fun _ : Fin m => H) := by
    exact integrable_finsetSum _ (fun a _ =>
      integrable_finsetSum _ (fun r _ =>
        integrable_scoreCDFDistance_population_pi hPH.2.2.overlap H g
          hPH.2.2.measurableRelease hm a r))
  have hFint : Integrable F (Qj PH.1 PH.2) := by
    have hmap : Measure.map Prod.fst (Qj PH.1 PH.2) =
        Measure.pi (fun _ : Fin n => μ) := by
      simpa [μ] using hTrial PH hPH
    rw [← hmap] at hFpi
    simpa [F, Function.comp_def] using
      hFpi.comp_aemeasurable measurable_fst.aemeasurable
  have hGint : Integrable G (Qj PH.1 PH.2) := by
    have hmap : Measure.map Prod.snd (Qj PH.1 PH.2) =
        Measure.pi (fun _ : Fin m => H) := by
      simpa [H] using hLog PH hPH
    rw [← hmap] at hGpi
    simpa [G, Function.comp_def] using
      hGpi.comp_aemeasurable measurable_snd.aemeasurable
  have hFmean : ∫ x, F x ∂Qj PH.1 PH.2 ≤ 2 * J / Real.sqrt n := by
    exact externalJointTrial_meanDistance_le g Qj hTrial PH hPH hn
      (by simpa [μ] using hFTmeas)
      (fun a r => integrable_outcomeCDFDistance_population_pi μ hn a r)
  have hGmean : ∫ x, G x ∂Qj PH.1 PH.2 ≤
      J * (2 - 2 * ε) / Real.sqrt m := by
    exact externalJointLog_meanDistance_le g Qj hLog PH hPH hm
      (by simpa [H] using hGTmeas)
      (fun a r => integrable_scoreCDFDistance_population_pi hPH.2.2.overlap H g
        hPH.2.2.measurableRelease hm a r)
  let C : ExternalIntervalProcedure ε J n m :=
    externalProjectionIntervalProcedure g α hPH.2.2.overlap
      hPH.2.2.measurableRelease
  let S := sharpATELength H g μ (externalLawCellMasses g PH hPH)
  have hleftMeas : Measurable (fun x => max 0 (C.length x - S)) := by
    exact measurable_const.max
      ((C.measurable_hi.sub C.measurable_lo).sub measurable_const)
  have hleftInt : Integrable (fun x => max 0 (C.length x - S))
      (Qj PH.1 PH.2) := by
    apply Integrable.of_bound hleftMeas.aestronglyMeasurable 2
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    apply max_le (by norm_num)
    dsimp [C, ExternalIntervalProcedure.length, S]
    linarith [C.lower_bound x, C.upper_bound x, hSharp]
  have hL : 0 ≤ ε⁻¹ + (ε ^ 2)⁻¹ :=
    add_nonneg (inv_nonneg.mpr hPH.2.2.overlap.1.le)
      (inv_nonneg.mpr (sq_nonneg ε))
  let R : ExternalSample ε J n m → ℝ := fun x =>
    4 * (ε⁻¹ + (ε ^ 2)⁻¹) *
      (4 * J / (α * Real.sqrt n) + F x +
        2 * J * (2 - 2 * ε) / (α * Real.sqrt m) + G x)
  have hRint : Integrable R (Qj PH.1 PH.2) := by
    dsimp [R]
    fun_prop
  have hpoint : ∀ x, max 0 (C.length x - S) ≤ R x := by
    intro x
    simpa [C, S, R, F, G, μ, H, mul_assoc] using
      externalProjectionIntervalProcedure_population_excessLength_le
        g α PH hPH x hα hn hm hSharp
  calc
    ∫ x, max 0 (C.length x - S) ∂Qj PH.1 PH.2 ≤
        ∫ x, R x ∂Qj PH.1 PH.2 := integral_mono hleftInt hRint hpoint
    _ = 4 * (ε⁻¹ + (ε ^ 2)⁻¹) *
        (4 * J / (α * Real.sqrt n) + (∫ x, F x ∂Qj PH.1 PH.2) +
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
          (∫ x, G x ∂Qj PH.1 PH.2)) := by
      dsimp [R]
      rw [integral_const_mul]
      congr 1
      rw [integral_add
        (f := fun a => 4 * J / (α * Real.sqrt n) + F a +
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m))
        (g := G) (((integrable_const _).add hFint).add (integrable_const _)) hGint,
        integral_add
          (f := fun a => 4 * J / (α * Real.sqrt n) + F a)
          (g := fun _ => 2 * J * (2 - 2 * ε) / (α * Real.sqrt m))
          ((integrable_const _).add hFint) (integrable_const _),
        integral_add
          (f := fun _ => 4 * J / (α * Real.sqrt n)) (g := F)
          (integrable_const _) hFint]
      simp
    _ ≤ 4 * (ε⁻¹ + (ε ^ 2)⁻¹) *
        (4 * J / (α * Real.sqrt n) + 2 * J / Real.sqrt n +
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
          J * (2 - 2 * ε) / Real.sqrt m) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) hL)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hTrial,hLog,hInd,PH,hPH,hn,hm,α,hα), this result [establishes the stated mathematical conclusion](goal). -/
theorem externalProjectionIntervalProcedure_population_meanExcessLength_le
    {ε : ℝ} {J n m : ℕ} (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) (hn : 0 < n) (hm : 0 < m)
    (α : ℝ) (hα : 0 < α) :
    ∫ x, max 0
        ((externalProjectionIntervalProcedure g α hPH.2.2.overlap
          hPH.2.2.measurableRelease).length x -
        sharpATELength PH.2 g (releasedLaw PH.1)
          (externalLawCellMasses g PH hPH)) ∂Qj PH.1 PH.2 ≤
      4 * (ε⁻¹ + (ε ^ 2)⁻¹) *
        (4 * J / (α * Real.sqrt n) + 2 * J / Real.sqrt n +
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
          J * (2 - 2 * ε) / Real.sqrt m) := by
  apply externalProjectionIntervalProcedure_population_meanExcessLength_le_of_sharp_nonneg
    g Qj hTrial hLog hInd PH hPH hn hm α hα
  exact sharpATELength_nonneg_of_overlap PH.2 g (releasedLaw PH.1)
    (externalLawCellMasses g PH hPH) hPH.2.2.overlap

end
end CausalSmith.PartialID.UnlinkedPropensityAte
