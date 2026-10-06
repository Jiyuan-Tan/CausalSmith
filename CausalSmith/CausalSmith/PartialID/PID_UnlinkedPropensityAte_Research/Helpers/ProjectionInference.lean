module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionIntegrated
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionPopulation
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionScorePopulation

/-! Probability bounds for the two empirical distances in the external projection. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: externalNormalizer_mul_rootSum
/-- Given [the stated mathematical inputs and assumptions](hyp:n,m,hn,hm), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalNormalizer_mul_rootSum (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    externalNormalizer n m *
        ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹) = 1 := by
  have hsn : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hsm : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
  unfold externalNormalizer
  field_simp

-- @node: externalNormalizedRisk_le_of_rootSum_bound
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,α,C,hn,hm,hR), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalNormalizedRisk_le_of_rootSum_bound
    {ε : ℝ} {J n m : ℕ} (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m)) (α C : ℝ)
    (hn : 0 < n) (hm : 0 < m)
    (hR : externalExcessRisk g Qj α ≤
      C * ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹)) :
    externalNormalizedRisk g Qj α ≤ C := by
  have hnorm : 0 ≤ externalNormalizer n m := by
    unfold externalNormalizer
    positivity
  unfold externalNormalizedRisk
  calc
    externalNormalizer n m * externalExcessRisk g Qj α ≤
        externalNormalizer n m *
          (C * ((Real.sqrt (n : ℝ))⁻¹ +
            (Real.sqrt (m : ℝ))⁻¹)) :=
      mul_le_mul_of_nonneg_left hR hnorm
    _ = C := by
      rw [mul_left_comm, externalNormalizer_mul_rootSum n m hn hm, mul_one]

-- @node: externalJointLaw_eq_experiment
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hTrial,hLog,hInd,PH,hPH), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalJointLaw_eq_experiment {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) :
    Qj PH.1 PH.2 = externalExperiment n m PH.1 PH.2 := by
  rw [hInd PH hPH, hTrial PH hPH, hLog PH hPH]
  rfl

-- @node: externalJointTrial_integral_eq_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hTrial,PH,hPH,F,hF), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalJointTrial_integral_eq_pi {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g)
    (F : TrialSample n J → ℝ) (hF : Measurable F) :
    ∫ x, F x.1 ∂Qj PH.1 PH.2 =
      ∫ x, F x ∂Measure.pi (fun _ : Fin n => releasedLaw PH.1) := by
  rw [← integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable,
    hTrial PH hPH]

-- @node: externalJointLog_integral_eq_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hLog,PH,hPH,F,hF), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalJointLog_integral_eq_pi {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hLog : ExternalLogIID g Qj)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g)
    (F : (Fin m → ScoreSpace ε) → ℝ) (hF : Measurable F) :
    ∫ x, F x.2 ∂Qj PH.1 PH.2 =
      ∫ x, F x ∂Measure.pi (fun _ : Fin m => PH.2) := by
  rw [← integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable,
    hLog PH hPH]

-- @node: externalJointTrial_meanDistance_le
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hTrial,PH,hPH,hn,hMeas,hInt), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalJointTrial_meanDistance_le {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) (hn : 0 < n)
    (hMeas : Measurable (fun x : TrialSample n J =>
      ∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (empiricalTrialCells x a r)
          (trialPopulationCells (releasedLaw PH.1) a r)))
    (hInt : ∀ a r, Integrable (fun x : TrialSample n J =>
      outcomeCDFDistance (empiricalTrialCells x a r)
        (trialPopulationCells (releasedLaw PH.1) a r))
      (Measure.pi (fun _ : Fin n => releasedLaw PH.1))) :
    (∫ x, (∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (empiricalTrialCells x.1 a r)
        (trialPopulationCells (releasedLaw PH.1) a r)) ∂Qj PH.1 PH.2) ≤
      2 * J / Real.sqrt n := by
  haveI : IsProbabilityMeasure (releasedLaw PH.1) := by
    unfold releasedLaw
    exact @Measure.isProbabilityMeasure_map _ _ _ _ PH.1 hPH.1 _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  rw [externalJointTrial_integral_eq_pi g Qj hTrial PH hPH _ hMeas]
  rw [integral_finsetSum]
  · calc
      _ = ∑ a : ArmSpace, ∑ r : LabelSpace J,
          ∫ x : TrialSample n J,
            outcomeCDFDistance (empiricalTrialCells x a r)
              (trialPopulationCells (releasedLaw PH.1) a r)
              ∂Measure.pi (fun _ : Fin n => releasedLaw PH.1) := by
                apply Finset.sum_congr rfl
                intro a _
                rw [integral_finsetSum]
                intro r _
                exact hInt a r
      _ ≤ _ := sum_meanOutcomeCDFDistance_trialPopulationCells_pi
        (releasedLaw PH.1) hn
  · intro a _
    exact integrable_finsetSum _ (fun r _ => hInt a r)

-- @node: externalJointLog_meanDistance_le
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hLog,PH,hPH,hm,hMeas,hInt), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalJointLog_meanDistance_le {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hLog : ExternalLogIID g Qj)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) (hm : 0 < m)
    (hMeas : Measurable (fun x : Fin m → ScoreSpace ε =>
      ∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (empiricalScoreCells g x a r)
          (scorePopulationCells PH.2 g a r)))
    (hInt : ∀ a r, Integrable (fun x : Fin m → ScoreSpace ε =>
      scoreCDFDistance (empiricalScoreCells g x a r)
        (scorePopulationCells PH.2 g a r))
      (Measure.pi (fun _ : Fin m => PH.2))) :
    (∫ x, (∑ a : ArmSpace, ∑ r : LabelSpace J,
      scoreCDFDistance (empiricalScoreCells g x.2 a r)
        (scorePopulationCells PH.2 g a r)) ∂Qj PH.1 PH.2) ≤
      J * (2 - 2 * ε) / Real.sqrt m := by
  have : IsProbabilityMeasure PH.2 := hPH.2.1
  rw [externalJointLog_integral_eq_pi g Qj hLog PH hPH _ hMeas]
  rw [integral_finsetSum]
  · calc
      _ = ∑ a : ArmSpace, ∑ r : LabelSpace J,
          ∫ x : Fin m → ScoreSpace ε,
            scoreCDFDistance (empiricalScoreCells g x a r)
              (scorePopulationCells PH.2 g a r)
              ∂Measure.pi (fun _ : Fin m => PH.2) := by
                apply Finset.sum_congr rfl
                intro a _
                rw [integral_finsetSum]
                intro r _
                exact hInt a r
      _ ≤ _ := sum_meanScoreCDFDistance_scorePopulationCells_pi
        hPH.2.2.overlap PH.2 g hPH.2.2.measurableRelease hm
  · intro a _
    exact integrable_finsetSum _ (fun r _ => hInt a r)

-- @node: projection_twoSource_strictBall_probability
/-- Given [the stated mathematical inputs and assumptions](hyp:Ω,μ,F,G,hFm,hGm,hF,hG,hFnonneg,hGnonneg,α,rn,rm,hrn,hrm,hFmean,hGmean), this result [establishes the stated mathematical conclusion](goal). -/
lemma projection_twoSource_strictBall_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hFm : Measurable F) (hGm : Measurable G)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hFnonneg : ∀ᵐ x ∂μ, 0 ≤ F x) (hGnonneg : ∀ᵐ x ∂μ, 0 ≤ G x)
    (α rn rm : ℝ) (hrn : 0 < rn) (hrm : 0 < rm)
    (hFmean : ∫ x, F x ∂μ ≤ α * rn / 2)
    (hGmean : ∫ x, G x ∂μ ≤ α * rm / 2) :
    1 - α ≤ μ.real {x | F x < rn ∧ G x < rm} := by
  have htailF := mul_meas_ge_le_integral_of_nonneg hFnonneg hF rn
  have htailG := mul_meas_ge_le_integral_of_nonneg hGnonneg hG rm
  have hFsmall : μ.real {x | rn ≤ F x} ≤ α / 2 := by
    calc
      _ ≤ (α * rn / 2) / rn := (le_div_iff₀ hrn).2 (by nlinarith [htailF, hFmean])
      _ = α / 2 := by field_simp
  have hGsmall : μ.real {x | rm ≤ G x} ≤ α / 2 := by
    calc
      _ ≤ (α * rm / 2) / rm := (le_div_iff₀ hrm).2 (by nlinarith [htailG, hGmean])
      _ = α / 2 := by field_simp
  have hbad : μ.real ({x | rn ≤ F x} ∪ {x | rm ≤ G x}) ≤ α := by
    calc
      _ ≤ μ.real {x | rn ≤ F x} + μ.real {x | rm ≤ G x} :=
        measureReal_union_le _ _
      _ ≤ α := by linarith
  have hevent : {x | F x < rn ∧ G x < rm} =
      ({x | rn ≤ F x} ∪ {x | rm ≤ G x})ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_union]
    push Not
    rfl
  rw [hevent, probReal_compl_eq_one_sub]
  · linarith
  · exact (measurableSet_le measurable_const hFm).union
      (measurableSet_le measurable_const hGm)

-- @node: projection_strictBall_probability_at_paper_radii
/-- Given [the stated mathematical inputs and assumptions](hyp:Ω,μ,F,G,hFm,hGm,hF,hG,hFnonneg,hGnonneg,J,n,m,hJ,hn,hm,α,ε,hα,hε,hFmean,hGmean), this result [establishes the stated mathematical conclusion](goal). -/
lemma projection_strictBall_probability_at_paper_radii
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hFm : Measurable F) (hGm : Measurable G)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hFnonneg : ∀ᵐ x ∂μ, 0 ≤ F x) (hGnonneg : ∀ᵐ x ∂μ, 0 ≤ G x)
    (J n m : ℕ) (hJ : 0 < J) (hn : 0 < n) (hm : 0 < m)
    (α ε : ℝ) (hα : 0 < α) (hε : ε < 1 / 2)
    (hFmean : ∫ x, F x ∂μ ≤ 2 * J / Real.sqrt n)
    (hGmean : ∫ x, G x ∂μ ≤ J * (2 - 2 * ε) / Real.sqrt m) :
    1 - α ≤ μ.real {x |
      F x < 4 * J / (α * Real.sqrt n) ∧
      G x < 2 * J * (2 - 2 * ε) / (α * Real.sqrt m)} := by
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hw : 0 < 2 - 2 * ε := by linarith
  have hrn : 0 < 4 * J / (α * Real.sqrt n) := by positivity
  have hrm : 0 < 2 * J * (2 - 2 * ε) / (α * Real.sqrt m) := by positivity
  apply projection_twoSource_strictBall_probability μ F G hFm hGm hF hG
    hFnonneg hGnonneg α _ _ hrn hrm
  · convert hFmean using 1 <;> field_simp <;> norm_num
  · convert hGmean using 1 <;> field_simp

end CausalSmith.PartialID.UnlinkedPropensityAte
