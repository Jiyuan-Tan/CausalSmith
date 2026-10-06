module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerBasic
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionRiskExpectation
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionSieveApproximation
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionSharpLength
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawCoverage

/-! Coverage of the atom-valid external projection interval. -/

public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: projectedArmEndpoint_lower_le_upper
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,hOverlap,lam,σ,hfinite,hcompat,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedArmEndpoint_lower_le_upper {ε : ℝ} {J : ℕ}
    (hOverlap : Overlap ε)
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hfinite : ∀ a r, (lam a r) Set.univ < ⊤ ∧ (σ a r) Set.univ < ⊤)
    (hcompat : ProjectionCompatible lam σ) (a : ArmSpace) :
    projectedArmEndpoint lam σ a false ≤ projectedArmEndpoint lam σ a true := by
  unfold projectedArmEndpoint
  apply Finset.sum_le_sum
  intro r _
  letI : IsFiniteMeasure (lam a r) := ⟨(hfinite a r).1⟩
  letI : IsFiniteMeasure (σ a r) := ⟨(hfinite a r).2⟩
  let q := (lam a r).real Set.univ
  by_cases hq : 0 < q
  · dsimp [q] at hq
    simp only [hq, if_pos, Bool.false_eq_true, if_false, if_true]
    exact mul_le_mul_of_nonneg_left
      (cell_lower_le_upper_of_overlap hOverlap a (lam a r) (σ a r) hq
        (hcompat a r)) hq.le
  · dsimp [q] at hq
    simp [hq]

-- @node: projectedATEInterval_mem_closure_of_sieve_approx
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x,lam,σ,hOverlap,happrox,t,ht), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedATEInterval_mem_closure_of_sieve_approx {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m)
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hOverlap : Overlap ε)
    (happrox : ∀ η : ℝ, 0 < η →
      ∃ b ∈ sievedProjectionCandidates g α x,
        ∀ a upper,
          |projectedArmEndpoint b.1 b.2 a upper -
            projectedArmEndpoint lam σ a upper| < η)
    {t : ℝ} (ht : t ∈ projectedATEInterval lam σ) :
    t ∈ closure (⋃ b ∈ sievedProjectionCandidates g α x,
      projectedATEInterval b.1 b.2) := by
  classical
  let L := projectedArmEndpoint lam σ true false -
    projectedArmEndpoint lam σ false true
  let U := projectedArmEndpoint lam σ true true -
    projectedArmEndpoint lam σ false false
  have ht' : L ≤ t ∧ t ≤ U := ht
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨b, hb, hnear⟩ := happrox (δ / 4) (by positivity)
  let B := projectedArmEndpoint b.1 b.2 true false -
    projectedArmEndpoint b.1 b.2 false true
  let V := projectedArmEndpoint b.1 b.2 true true -
    projectedArmEndpoint b.1 b.2 false false
  have hfinite : ∀ a r, (b.1 a r) Set.univ < ⊤ ∧
      (b.2 a r) Set.univ < ⊤ := hb.1.1
  have hcompat : ProjectionCompatible b.1 b.2 := hb.1.2.1
  have horder : B ≤ V := by
    have h₁ := projectedArmEndpoint_lower_le_upper hOverlap b.1 b.2
      hfinite hcompat true
    have h₀ := projectedArmEndpoint_lower_le_upper hOverlap b.1 b.2
      hfinite hcompat false
    dsimp [B, V]
    linarith
  have hB : |B - L| < δ / 2 := by
    have h₁ := hnear true false
    have h₀ := hnear false true
    dsimp [B, L]
    rw [abs_lt] at h₁ h₀ ⊢
    constructor <;> linarith
  have hV : |V - U| < δ / 2 := by
    have h₁ := hnear true true
    have h₀ := hnear false false
    dsimp [V, U]
    rw [abs_lt] at h₁ h₀ ⊢
    constructor <;> linarith
  let z := min (max t B) V
  have hz : z ∈ projectedATEInterval b.1 b.2 := by
    change B ≤ z ∧ z ≤ V
    dsimp [z]
    exact ⟨le_min (le_max_right _ _) horder, min_le_right _ _⟩
  have hdist : dist t z < δ := by
    rw [Real.dist_eq]
    by_cases hlow : t < B
    · have hzeq : z = B := by
        simp [z, max_eq_right hlow.le, min_eq_left horder]
      rw [hzeq, abs_lt] at *
      constructor <;> linarith [hB.1, hB.2, ht'.1]
    · by_cases hhigh : V < t
      · have hzeq : z = V := by
          have hmax : max t B = t := max_eq_left (le_of_not_gt hlow)
          simp [z, hmax, min_eq_right hhigh.le]
        rw [hzeq, abs_lt] at *
        constructor <;> linarith [hV.1, hV.2, ht'.2]
      · have hzeq : z = t := by
          have hmax : max t B = t := max_eq_left (le_of_not_gt hlow)
          simp [z, hmax, min_eq_left (le_of_not_gt hhigh)]
        rw [hzeq]
        simpa using hδ
  exact ⟨z, Set.mem_iUnion.mpr ⟨b,
    Set.mem_iUnion.mpr ⟨hb, hz⟩⟩, hdist⟩

-- @node: projection_strict_population_approximants
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,x,lam,σ,hfinite,hcompat,hout,hscore), this result [establishes the stated mathematical conclusion](goal). -/
lemma projection_strict_population_approximants {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (x : ExternalSample ε J n m)
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hfinite : ∀ a r, (lam a r) Set.univ < ⊤ ∧ (σ a r) Set.univ < ⊤)
    (hcompat : ProjectionCompatible lam σ)
    (hout : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (lam a r) (empiricalTrialCells x.1 a r)) <
        4 * J / (α * Real.sqrt n))
    (hscore : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      scoreCDFDistance (σ a r) (empiricalScoreCells g x.2 a r)) <
        2 * J * (2 - 2 * ε) / (α * Real.sqrt m)) :
    ∀ η : ℝ, 0 < η →
      ∃ b ∈ sievedProjectionCandidates g α x,
        ∀ a upper,
          |projectedArmEndpoint b.1 b.2 a upper -
            projectedArmEndpoint lam σ a upper| < η := by
  classical
  intro η hη
  let L : ℝ := ε⁻¹ + (ε ^ 2)⁻¹
  have hLpos : 0 < L := by
    dsimp [L]
    have hε := hOverlap.1
    positivity
  have hL : 0 ≤ L := hLpos.le
  let rout : ℝ := 4 * J / (α * Real.sqrt n)
  let rscore : ℝ := 2 * J * (2 - 2 * ε) / (α * Real.sqrt m)
  let sout : ℝ := ∑ a : ArmSpace, ∑ r : LabelSpace J,
    outcomeCDFDistance (lam a r) (empiricalTrialCells x.1 a r)
  let sscore : ℝ := ∑ a : ArmSpace, ∑ r : LabelSpace J,
    scoreCDFDistance (σ a r) (empiricalScoreCells g x.2 a r)
  let δ := min (rout - sout) (min (rscore - sscore) (η / (L + 1))) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    have h₁ : 0 < rout - sout := sub_pos.mpr hout
    have h₂ : 0 < rscore - sscore := sub_pos.mpr hscore
    exact div_pos (lt_min h₁ (lt_min h₂ (div_pos hη (by linarith))))
      (by norm_num)
  have houtδ : sout + δ ≤ rout := by
    have hm := min_le_left (rout - sout) (min (rscore - sscore) (η / (L + 1)))
    dsimp [δ]
    linarith
  have hscoreδ : sscore + δ ≤ rscore := by
    have hm := min_le_left (rscore - sscore) (η / (L + 1))
    have hm' := min_le_right (rout - sout) (min (rscore - sscore) (η / (L + 1)))
    dsimp [δ]
    linarith
  obtain ⟨b, hb, hdist⟩ := exists_sievedProjectionCandidate_close_of_slack
    hOverlap g α x lam σ hfinite hcompat δ hδ houtδ hscoreδ
  refine ⟨b, hb, ?_⟩
  have hLδ : L * δ < η := by
    have hm := min_le_right (rscore - sscore) (η / (L + 1))
    have hm' := min_le_right (rout - sout) (min (rscore - sscore) (η / (L + 1)))
    have hδbound : δ ≤ η / (L + 1) := by
      have hmin : 0 ≤ min (rout - sout)
          (min (rscore - sscore) (η / (L + 1))) := by
        dsimp [δ] at hδ
        linarith
      dsimp [δ]
      linarith
    have hden : 0 < L + 1 := by linarith
    have hratio : L * (η / (L + 1)) < η := by
      have hcancel : (L + 1) * (η / (L + 1)) = η := by field_simp
      nlinarith [div_pos hη hden]
    exact (mul_le_mul_of_nonneg_left hδbound hL).trans_lt hratio
  have hfiniteB : ∀ a r, (b.1 a r) Set.univ < ⊤ ∧
      (b.2 a r) Set.univ < ⊤ := hb.1.1
  have hcompatB : ProjectionCompatible b.1 b.2 := hb.1.2.1
  intro a upper
  have hendpoint := projectedArmEndpoint_abs_le_of_compatible_cells hOverlap
    lam b.1 σ b.2 (fun a r => ⟨(hfinite a r).1⟩)
    (fun a r => ⟨(hfiniteB a r).1⟩)
    (fun a r => ⟨(hfinite a r).2⟩)
    (fun a r => ⟨(hfiniteB a r).2⟩)
    hcompat hcompatB a upper
  have hpair :
      (∑ r : LabelSpace J, outcomeCDFDistance (lam a r) (b.1 a r)) +
      (∑ r : LabelSpace J, scoreCDFDistance (σ a r) (b.2 a r)) < δ := by
    have hnonneg (a : ArmSpace) :
        0 ≤ (∑ r : LabelSpace J, outcomeCDFDistance (lam a r) (b.1 a r)) +
          (∑ r : LabelSpace J, scoreCDFDistance (σ a r) (b.2 a r)) := by
      apply add_nonneg
      · exact Finset.sum_nonneg (fun r _ => outcomeCDFDistance_nonneg _ _)
      · exact Finset.sum_nonneg (fun r _ => scoreCDFDistance_nonneg hOverlap _ _)
    simp only [Finset.sum_add_distrib, Fintype.sum_bool] at hdist
    cases a <;> linarith [hnonneg false, hnonneg true]
  rw [abs_sub_comm]
  exact hendpoint.trans_lt ((mul_lt_mul_of_pos_left hpair hLpos).trans hLδ)
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,PH,hPH,x,hout,hscore), this result [establishes the stated mathematical conclusion](goal). -/
lemma projection_strictBall_ate_mem_CI {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g)
    (x : ExternalSample ε J n m)
    (hout : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance
        (trialPopulationCells (releasedLaw PH.1) a r)
        (empiricalTrialCells x.1 a r)) <
          4 * J / (α * Real.sqrt n))
    (hscore : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      scoreCDFDistance (scorePopulationCells PH.2 g a r)
        (empiricalScoreCells g x.2 a r)) <
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m)) :
    ate PH.1 ∈ sievedTotalizedProjectionCI g α x := by
  classical
  let lam := trialPopulationCells (releasedLaw PH.1)
  let σ := scorePopulationCells PH.2 g
  let hMass := externalLawCellMasses g PH hPH
  haveI : IsProbabilityMeasure PH.2 := hPH.2.1
  haveI : IsProbabilityMeasure (releasedLaw PH.1) := by
    unfold releasedLaw
    exact @Measure.isProbabilityMeasure_map _ _ _ _ PH.1 hPH.1 _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  have hfin := projectionPopulationCells_finite PH.2 g (releasedLaw PH.1)
    hPH.2.2.overlap hPH.2.2.measurableRelease
  have hfinite : ∀ a r, (lam a r) Set.univ < ⊤ ∧ (σ a r) Set.univ < ⊤ := by
    intro a r
    exact ⟨(hfin.1 a r).measure_univ_lt_top,
      (hfin.2 a r).measure_univ_lt_top⟩
  have hcompat : ProjectionCompatible lam σ :=
    projectionCompatible_populationCells PH.2 g (releasedLaw PH.1)
      hMass hPH.2.2.overlap
  have happrox := projection_strict_population_approximants g α
    hPH.2.2.overlap x lam σ hfinite hcompat hout hscore
  have hC : ate PH.1 ∈ closure
      (⋃ b ∈ sievedProjectionCandidates g α x,
        projectedATEInterval b.1 b.2) := by
    apply projectedATEInterval_mem_closure_of_sieve_approx g α x lam σ
      hPH.2.2.overlap happrox
    have hLaw : CompatibleCausalLaw PH.2 g (releasedLaw PH.1) PH.1 :=
      ⟨hPH.1, hPH.2.2.measurableRelease, hPH.2.2.scoreMarginal,
        hPH.2.2.randomizedAssignment, hPH.2.2.consistency,
        hPH.2.2.deterministicRelease, rfl⟩
    have hθ := compatible_ate_mem_sharpATESet PH.2 g
      (releasedLaw PH.1) PH.1 hLaw hPH.2.2.overlap
    change ate PH.1 ∈ Set.Icc
      (muLower PH.2 g (releasedLaw PH.1) hMass true -
        muUpper PH.2 g (releasedLaw PH.1) hMass false)
      (muUpper PH.2 g (releasedLaw PH.1) hMass true -
        muLower PH.2 g (releasedLaw PH.1) hMass false) at hθ
    dsimp [projectedATEInterval, lam, σ]
    rw [projectedArmEndpoint_population_eq PH.2 g (releasedLaw PH.1)
        hMass hPH.2.2.overlap true false,
      projectedArmEndpoint_population_eq PH.2 g (releasedLaw PH.1)
        hMass hPH.2.2.overlap false true,
      projectedArmEndpoint_population_eq PH.2 g (releasedLaw PH.1)
        hMass hPH.2.2.overlap true true,
      projectedArmEndpoint_population_eq PH.2 g (releasedLaw PH.1)
        hMass hPH.2.2.overlap false false]
    simpa using hθ
  have hB : (sievedProjectionCandidates g α x).Nonempty := by
    obtain ⟨b, hb, _⟩ := happrox 1 (by norm_num)
    exact ⟨b, hb⟩
  have hclip : ate PH.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    letI : IsProbabilityMeasure PH.1 := hPH.1
    exact externalATE_mem_Icc PH.1
  have hCHull : ate PH.1 ∈
      closure (convexHull ℝ
        (⋃ b ∈ sievedProjectionCandidates g α x,
          projectedATEInterval b.1 b.2)) :=
    closure_mono (subset_convexHull ℝ _) hC
  have hne : (Set.Icc (-1 : ℝ) 1 ∩
      closure (convexHull ℝ
        (⋃ b ∈ sievedProjectionCandidates g α x,
          projectedATEInterval b.1 b.2))).Nonempty :=
    ⟨ate PH.1, hclip, hCHull⟩
  unfold sievedTotalizedProjectionCI
  simpa [hB, hne] using (show ate PH.1 ∈ Set.Icc (-1 : ℝ) 1 ∩
      closure (convexHull ℝ
        (⋃ b ∈ sievedProjectionCandidates g α x,
          projectedATEInterval b.1 b.2)) from ⟨hclip, hCHull⟩)

-- @node: externalProjectionIntervalProcedure_honest
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,hg,hn,hm,hα,Qj,hTrial,hLog,hInd), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionIntervalProcedure_honest {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (hg : Measurable g)
    (hn : 0 < n) (hm : 0 < m) (hα : 0 < α)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj) :
    externalProjectionIntervalProcedure g α hOverlap hg ∈
      externalHonestProcedures g Qj α := by
  intro PH hPH
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
  letI : IsProbabilityMeasure PH.1 := hPH.1
  letI : IsProbabilityMeasure H := hPH.2.1
  letI : IsProbabilityMeasure μ := by
    unfold μ releasedLaw
    exact @Measure.isProbabilityMeasure_map _ _ _ _ PH.1 hPH.1 _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  letI : IsProbabilityMeasure (Qj PH.1 PH.2) :=
    externalLaw_jointExperiment_probability g Qj hTrial hLog hInd PH hPH
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
  have hFm : Measurable F := hFTmeas.comp measurable_fst
  have hGm : Measurable G := hGTmeas.comp measurable_snd
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
  have hF : Integrable F (Qj PH.1 PH.2) := by
    have hmap : Measure.map Prod.fst (Qj PH.1 PH.2) =
        Measure.pi (fun _ : Fin n => μ) := by
      simpa [μ] using hTrial PH hPH
    rw [← hmap] at hFpi
    simpa [F, Function.comp_def] using
      hFpi.comp_aemeasurable measurable_fst.aemeasurable
  have hG : Integrable G (Qj PH.1 PH.2) := by
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
      (fun a r => integrable_scoreCDFDistance_population_pi
        hPH.2.2.overlap H g hPH.2.2.measurableRelease hm a r)
  have hJ : 0 < J := by
    letI : Nonempty (FullRow ε J) := nonempty_of_isProbabilityMeasure PH.1
    obtain ⟨ω⟩ := ‹Nonempty (FullRow ε J)›
    exact lt_of_le_of_lt (Nat.zero_le _) (label ω).isLt
  have hprob := projection_strictBall_probability_at_paper_radii
    (Qj PH.1 PH.2) F G hFm hGm hF hG
    (Filter.Eventually.of_forall (fun x => Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun r _ => outcomeCDFDistance_nonneg _ _))))
    (Filter.Eventually.of_forall (fun x => Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun r _ => scoreCDFDistance_nonneg hOverlap _ _))))
    J n m hJ hn hm α ε hα hOverlap.2 hFmean hGmean
  have hsubset : {x | F x < 4 * J / (α * Real.sqrt n) ∧
      G x < 2 * J * (2 - 2 * ε) / (α * Real.sqrt m)} ⊆
      {x | (externalProjectionIntervalProcedure g α hOverlap hg).contains x
        (ate PH.1)} := by
    intro x hx
    change F x < _ ∧ G x < _ at hx
    have hout : (∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (trialPopulationCells μ a r)
          (empiricalTrialCells x.1 a r)) <
            4 * J / (α * Real.sqrt n) := by
      convert hx.1 using 1
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro r _
      exact outcomeCDFDistance_symm _ _
    have hscore : (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (scorePopulationCells H g a r)
          (empiricalScoreCells g x.2 a r)) <
            2 * J * (2 - 2 * ε) / (α * Real.sqrt m) := by
      convert hx.2 using 1
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro r _
      exact scoreCDFDistance_symm _ _
    have hmem := projection_strictBall_ate_mem_CI g α PH hPH x hout hscore
    rw [← externalProjectionIntervalProcedure_Icc g α hOverlap hg x] at hmem
    exact hmem
  rw [← jointTrialLog_eq_externalExperiment g Qj hTrial hLog hInd PH hPH]
  exact hprob.trans (measureReal_mono hsubset)

-- @node: externalExcessRisk_le_of_honest_uniform_bound
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hOverlap,hg,Qj,hTrial,hLog,hInd,C,hC,R,hR,hbound), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalExcessRisk_le_of_honest_uniform_bound {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (hg : Measurable g)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (C : ExternalIntervalProcedure ε J n m)
    (hC : C ∈ externalHonestProcedures g Qj α)
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ PH, ∀ hPH : PH ∈ ExternalLaws g,
      (∫ x, max 0 (C.length x -
        sharpATELength PH.2 g (releasedLaw PH.1)
          (externalLawCellMasses g PH hPH)) ∂(Qj PH.1 PH.2)) ≤ R) :
    externalExcessRisk g Qj α ≤ R := by
  let P : Measure (FullRow ε J) := trialCenterFullLaw g hOverlap (1 / 2)
  let H : Measure (ScoreSpace ε) := Measure.dirac (trialCenterScore hOverlap)
  have hPH : (P, H) ∈ ExternalLaws g :=
    ⟨trialCenterFullLaw_isProbabilityMeasure g hOverlap _ (by norm_num) (by norm_num),
      inferInstance,
      trialCenterFullLaw_externalScoreLaw g hOverlap hg _ (by norm_num) (by norm_num)⟩
  let U (C : ExternalIntervalProcedure ε J n m) : Set ℝ :=
    {u | ∃ PH, ∃ hPH : PH ∈ ExternalLaws g,
      u = ∫ x, max 0 (C.length x -
        sharpATELength PH.2 g (releasedLaw PH.1)
          (externalLawCellMasses g PH hPH))
          ∂(externalExperiment n m PH.1 PH.2)}
  have hUbd (C : ExternalIntervalProcedure ε J n m) : BddAbove (U C) := by
    refine ⟨2, ?_⟩
    rintro u ⟨PH, hPH', rfl⟩
    simpa only [jointTrialLog_eq_externalExperiment g Qj hTrial hLog hInd PH hPH']
      using externalExcessIntegral_le_two g Qj hTrial hLog hInd C PH hPH'
  have hUne (C : ExternalIntervalProcedure ε J n m) : (U C).Nonempty := by
    exact ⟨_, ⟨(P, H), hPH, rfl⟩⟩
  have hUlower (C : ExternalIntervalProcedure ε J n m) : 0 ≤ sSup (U C) := by
    obtain ⟨u, hu⟩ := hUne C
    rcases hu with ⟨PH, hPH', rfl⟩
    exact (integral_nonneg (fun _ => le_max_left _ _)).trans
      (le_csSup (hUbd C) ⟨PH, hPH', rfl⟩)
  have hRiskBd : BddBelow {v : ℝ | ∃ C ∈ externalHonestProcedures g Qj α,
      v = sSup (U C)} := by
    refine ⟨0, ?_⟩
    rintro v ⟨C, hC', rfl⟩
    exact hUlower C
  have hUupper : sSup (U C) ≤ R := by
    apply csSup_le (hUne C)
    rintro v ⟨PH, hPH', rfl⟩
    simpa only [jointTrialLog_eq_externalExperiment g Qj hTrial hLog hInd PH hPH']
      using hbound PH hPH'
  unfold externalExcessRisk
  have hmem : sSup (U C) ∈
      {v : ℝ | ∃ C ∈ externalHonestProcedures g Qj α, v = sSup (U C)} :=
    ⟨C, hC, rfl⟩
  exact (csInf_le hRiskBd hmem).trans hUupper

end CausalSmith.PartialID.UnlinkedPropensityAte
