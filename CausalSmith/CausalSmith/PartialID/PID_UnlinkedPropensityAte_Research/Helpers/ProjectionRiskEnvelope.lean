module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionCandidateStability
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionEndpointBounds

/-!
Population identification and deterministic excess-length bounds for the
external projection interval.
-/

public section

open MeasureTheory Set
open scoped ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

private lemma scorePopulationCells_eq_restrict {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (a : ArmSpace) (r : LabelSpace J) :
    scorePopulationCells H g a r =
      (H.withDensity (fun e => ENNReal.ofReal (armProb a e))).restrict (cell g r) := by
  ext B hB
  have hcell : MeasurableSet (cell g r) :=
    measurableSet_eq_fun hg measurable_const
  rw [scorePopulationCells, withDensity_apply _ hB,
    Measure.restrict_apply hB,
    withDensity_apply _ (hB.inter hcell)]
  rw [← MeasureTheory.lintegral_indicator hB,
    ← MeasureTheory.lintegral_indicator (hB.inter hcell)]
  apply lintegral_congr
  intro e
  by_cases heB : e ∈ B <;> by_cases he : g e = r <;>
    simp [cell, Set.indicator, heB, he]

private lemma normalized_trialPopulationCell_eq_armCellOutcomeLaw
    {ε : ℝ} {J : ℕ} (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) (Prel : Measure (Observation J))
    (hMass : CompatibleCellMasses H g Prel) (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    (((trialPopulationCells Prel a r Set.univ)⁻¹ •
        trialPopulationCells Prel a r).map
      (fun y : OutcomeSpace => (y : ℝ))) =
      armCellOutcomeLaw Prel hMass.2.1 a r
        (by rw [hMass.2.2.2 a r]; exact hq) := by
  have hmass : trialPopulationCells Prel a r Set.univ =
      Prel {z | z.1 = r ∧ z.2.1 = a} := by
    rw [trialPopulationCells_apply Prel a r Set.univ MeasurableSet.univ]
    simp only [Set.mem_univ, and_true]
  unfold armCellOutcomeLaw
  rw [Measure.map_smul, hmass]
  unfold trialPopulationCells
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

private lemma normalized_scorePopulationCell_eq_armCellWeightLaw
    {ε : ℝ} {J : ℕ} (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace J) (Prel : Measure (Observation J))
    (hMass : CompatibleCellMasses H g Prel) (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    (((scorePopulationCells H g a r Set.univ)⁻¹ •
        scorePopulationCells H g a r).map
      (fun e => (armProb a e)⁻¹)) =
      armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq := by
  letI : IsProbabilityMeasure H := hMass.1
  have hmassReal : (scorePopulationCells H g a r).real Set.univ =
      armCellMass H g a r := by
    rw [scorePopulationCells_real_apply hOverlap H g hMass.2.2.1 a r
      Set.univ MeasurableSet.univ]
    simpa [armCellMass, cell] using
      (integral_indicator
        (measurableSet_eq_fun hMass.2.2.1 measurable_const)
        (f := armProb a) (μ := H))
  letI : IsProbabilityMeasure Prel := hMass.2.1
  have hfin := projectionPopulationCells_finite H g Prel hOverlap hMass.2.2.1
  letI : IsFiniteMeasure (scorePopulationCells H g a r) := hfin.2 a r
  have hmass : scorePopulationCells H g a r Set.univ =
      ENNReal.ofReal (armCellMass H g a r) := by
    calc
      _ = ENNReal.ofReal ((scorePopulationCells H g a r Set.univ).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = _ := by simpa [Measure.real] using congrArg ENNReal.ofReal hmassReal
  unfold armCellWeightLaw armCellScoreLaw
  rw [Measure.map_smul, hmass,
    scorePopulationCells_eq_restrict H g hMass.2.2.1 a r,
    Measure.map_smul]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedArmEndpoint_population_eq {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) (upper : Bool) :
    projectedArmEndpoint (trialPopulationCells Prel) (scorePopulationCells H g)
        a upper =
      if upper then muUpper H g Prel hMass a else muLower H g Prel hMass a := by
  unfold projectedArmEndpoint
  cases upper with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold muLower
    apply Finset.sum_congr rfl
    intro r _
    have hmass : (trialPopulationCells Prel a r).real Set.univ =
        armCellMass H g a r := by
      rw [trialPopulationCells_real_apply Prel a r Set.univ MeasurableSet.univ]
      simpa only [Set.mem_univ, and_true] using hMass.2.2.2 a r
    rw [hmass]
    by_cases hq : 0 < armCellMass H g a r
    · simp only [hq, dif_pos, if_pos]
      rw [normalized_trialPopulationCell_eq_armCellOutcomeLaw H g Prel hMass a r hq,
        normalized_scorePopulationCell_eq_armCellWeightLaw H g Prel hMass
          hOverlap a r hq]
    · simp [hq]
  | true =>
    simp only [↓reduceIte]
    unfold muUpper
    apply Finset.sum_congr rfl
    intro r _
    have hmass : (trialPopulationCells Prel a r).real Set.univ =
        armCellMass H g a r := by
      rw [trialPopulationCells_real_apply Prel a r Set.univ MeasurableSet.univ]
      simpa only [Set.mem_univ, and_true] using hMass.2.2.2 a r
    rw [hmass]
    by_cases hq : 0 < armCellMass H g a r
    · simp only [hq, dif_pos, if_pos]
      rw [normalized_trialPopulationCell_eq_armCellOutcomeLaw H g Prel hMass a r hq,
        normalized_scorePopulationCell_eq_armCellWeightLaw H g Prel hMass
          hOverlap a r hq]
    · simp [hq]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedPopulationATESpan_eq_sharpATELength {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) :
    (projectedArmEndpoint (trialPopulationCells Prel) (scorePopulationCells H g)
          true true -
        projectedArmEndpoint (trialPopulationCells Prel) (scorePopulationCells H g)
          false false) -
      (projectedArmEndpoint (trialPopulationCells Prel) (scorePopulationCells H g)
          true false -
        projectedArmEndpoint (trialPopulationCells Prel) (scorePopulationCells H g)
          false true) =
      sharpATELength H g Prel hMass := by
  rw [projectedArmEndpoint_population_eq H g Prel hMass hOverlap true true,
    projectedArmEndpoint_population_eq H g Prel hMass hOverlap false false,
    projectedArmEndpoint_population_eq H g Prel hMass hOverlap true false,
    projectedArmEndpoint_population_eq H g Prel hMass hOverlap false true]
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,H,g,Prel,hMass,α,hOverlap,hg,x,δ,hδ,hSharp,hendpoint), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionIntervalProcedure_excessLength_le_of_endpoint_bounds
    {ε : ℝ} {J n m : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (α : ℝ) (hOverlap : Overlap ε) (hg : Measurable g)
    (x : ExternalSample ε J n m) {δ : ℝ}
    (hδ : 0 ≤ δ) (hSharp : 0 ≤ sharpATELength H g Prel hMass)
    (hendpoint : ∀ b ∈ sievedProjectionCandidates g α x, ∀ a upper,
      |projectedArmEndpoint b.1 b.2 a upper -
        projectedArmEndpoint (trialPopulationCells Prel)
          (scorePopulationCells H g) a upper| ≤ δ) :
    max 0 ((externalProjectionIntervalProcedure g α hOverlap hg).length x -
      sharpATELength H g Prel hMass) ≤ 4 * δ := by
  classical
  let C := Set.Icc (-1 : ℝ) 1 ∩
    closure (convexHull ℝ
      (⋃ b ∈ sievedProjectionCandidates g α x,
        projectedATEInterval b.1 b.2))
  by_cases hC : C.Nonempty
  · have hLU :
        projectedArmEndpoint (trialPopulationCells Prel) (scorePopulationCells H g)
            true false -
          projectedArmEndpoint (trialPopulationCells Prel) (scorePopulationCells H g)
            false true ≤
        projectedArmEndpoint (trialPopulationCells Prel) (scorePopulationCells H g)
            true true -
          projectedArmEndpoint (trialPopulationCells Prel) (scorePopulationCells H g)
            false false := by
      have hspan := projectedPopulationATESpan_eq_sharpATELength
        H g Prel hMass hOverlap
      linarith
    have hbound := externalProjectionCI_excessLength_le_of_armEndpoint_bounds
      g α x (trialPopulationCells Prel) (scorePopulationCells H g)
      hδ hLU (fun _ => hC) hendpoint
    obtain ⟨lo, hi, heq, hb⟩ := hbound
    have hne := externalProjectionCI_nonempty g α x
    have hlohi : lo ≤ hi := by
      obtain ⟨z, hz⟩ := hne
      rw [heq] at hz
      exact hz.1.trans hz.2
    let CI : ExternalIntervalProcedure ε J n m :=
      externalProjectionIntervalProcedure g α hOverlap hg
    have hproc : Set.Icc (CI.lo x) (CI.hi x) = sievedTotalizedProjectionCI g α x :=
      externalProjectionIntervalProcedure_Icc g α hOverlap hg x
    have hprocord : CI.lo x ≤ CI.hi x := CI.ordered x
    have hlo : CI.lo x = lo := by
      apply le_antisymm
      · have hz : lo ∈ Set.Icc (CI.lo x) (CI.hi x) := by
          rw [hproc, heq]
          exact Set.left_mem_Icc.mpr hlohi
        exact hz.1
      · have hz : CI.lo x ∈ Set.Icc lo hi := by
          rw [← heq, ← hproc]
          exact Set.left_mem_Icc.mpr hprocord
        exact hz.1
    have hhi : CI.hi x = hi := by
      apply le_antisymm
      · have hz : CI.hi x ∈ Set.Icc lo hi := by
          rw [← heq, ← hproc]
          exact Set.right_mem_Icc.mpr hprocord
        exact hz.2
      · have hz : hi ∈ Set.Icc (CI.lo x) (CI.hi x) := by
          rw [hproc, heq]
          exact Set.right_mem_Icc.mpr hlohi
        exact hz.2
    simpa [ExternalIntervalProcedure.length, CI, hlo, hhi,
      projectedPopulationATESpan_eq_sharpATELength H g Prel hMass hOverlap] using hb
  · have hfallback : sievedTotalizedProjectionCI g α x = {0} := by
      rw [sievedTotalizedProjectionCI]
      change (if (sievedProjectionCandidates g α x).Nonempty ∧ C.Nonempty
        then C else {0}) = {0}
      simp [hC]
    let CI : ExternalIntervalProcedure ε J n m :=
      externalProjectionIntervalProcedure g α hOverlap hg
    have hproc : Set.Icc (CI.lo x) (CI.hi x) = sievedTotalizedProjectionCI g α x :=
      externalProjectionIntervalProcedure_Icc g α hOverlap hg x
    have hlo : CI.lo x = 0 := by
      have hz : CI.lo x ∈ sievedTotalizedProjectionCI g α x := by
        rw [← hproc]
        exact Set.left_mem_Icc.mpr (CI.ordered x)
      simpa [hfallback] using hz
    have hhi : CI.hi x = 0 := by
      have hz : CI.hi x ∈ sievedTotalizedProjectionCI g α x := by
        rw [← hproc]
        exact Set.right_mem_Icc.mpr (CI.ordered x)
      simpa [hfallback] using hz
    simp only [ExternalIntervalProcedure.length, CI, hlo, hhi, sub_self]
    rw [max_eq_left]
    · exact mul_nonneg (by norm_num) hδ
    · linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,PH,hPH,x,hα,hn,hm,hSharp), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionIntervalProcedure_population_excessLength_le
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) (x : ExternalSample ε J n m)
    (hα : 0 < α) (hn : 0 < n) (hm : 0 < m)
    (hSharp : 0 ≤ sharpATELength PH.2 g (releasedLaw PH.1)
      (externalLawCellMasses g PH hPH)) :
    let δ := (ε⁻¹ + (ε ^ 2)⁻¹) *
      (4 * J / (α * Real.sqrt n) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (empiricalTrialCells x.1 a r)
            (trialPopulationCells (releasedLaw PH.1) a r)) +
        2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (empiricalScoreCells g x.2 a r)
            (scorePopulationCells PH.2 g a r)))
    max 0 ((externalProjectionIntervalProcedure g α hPH.2.2.overlap
        hPH.2.2.measurableRelease).length x -
      sharpATELength PH.2 g (releasedLaw PH.1)
        (externalLawCellMasses g PH hPH)) ≤ 4 * δ := by
  dsimp only
  have hOverlap := hPH.2.2.overlap
  have hout : 0 ≤ ∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (empiricalTrialCells x.1 a r)
        (trialPopulationCells (releasedLaw PH.1) a r) :=
    Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun r _ => outcomeCDFDistance_nonneg _ _))
  have hscore : 0 ≤ ∑ a : ArmSpace, ∑ r : LabelSpace J,
      scoreCDFDistance (empiricalScoreCells g x.2 a r)
        (scorePopulationCells PH.2 g a r) :=
    Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun r _ => scoreCDFDistance_nonneg hOverlap _ _))
  have htrialRadius : 0 ≤ 4 * J / (α * Real.sqrt n) := by positivity
  have hwidth : 0 ≤ 2 - 2 * ε := by linarith [hOverlap.2]
  have hsqrtm : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hlogRadius : 0 ≤ 2 * J * (2 - 2 * ε) / (α * Real.sqrt m) := by
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hwidth)
      (mul_nonneg hα.le hsqrtm.le)
  have hL : 0 ≤ ε⁻¹ + (ε ^ 2)⁻¹ :=
    add_nonneg (inv_nonneg.mpr hOverlap.1.le) (inv_nonneg.mpr (sq_nonneg ε))
  apply externalProjectionIntervalProcedure_excessLength_le_of_endpoint_bounds
    PH.2 g (releasedLaw PH.1) (externalLawCellMasses g PH hPH) α
    hOverlap hPH.2.2.measurableRelease x
  · exact mul_nonneg hL (by linarith)
  · exact hSharp
  · intro b hb a upper
    exact projectionCandidate_populationArmEndpoint_abs_le
      g α PH hPH x b hb.1 a upper

end
end CausalSmith.PartialID.UnlinkedPropensityAte
