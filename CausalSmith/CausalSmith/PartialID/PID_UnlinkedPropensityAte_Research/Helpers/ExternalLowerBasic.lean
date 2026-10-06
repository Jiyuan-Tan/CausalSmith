module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerCertificate
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerTrialTesting
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionSharpLength

/-! Basic interval bounds used by the lower certificate and projection risk. -/

@[expose] public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: externalATE_mem_Icc
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalATE_mem_Icc {ε : ℝ} {J : ℕ}
    (P : Measure (FullRow ε J)) [IsProbabilityMeasure P] :
    ate P ∈ Set.Icc (-1 : ℝ) 1 := by
  have h₀ : Integrable (fun ω => ((outcome0 ω : OutcomeSpace) : ℝ)) P := by
    simpa using potentialOutcome_integrable P false
  have h₁ : Integrable (fun ω => ((outcome1 ω : OutcomeSpace) : ℝ)) P := by
    simpa using potentialOutcome_integrable P true
  have h₀lo : 0 ≤ ∫ ω, ((outcome0 ω : OutcomeSpace) : ℝ) ∂P :=
    integral_nonneg (fun ω => (outcome0 ω).property.1)
  have h₁lo : 0 ≤ ∫ ω, ((outcome1 ω : OutcomeSpace) : ℝ) ∂P :=
    integral_nonneg (fun ω => (outcome1 ω).property.1)
  have h₀hi : (∫ ω, ((outcome0 ω : OutcomeSpace) : ℝ) ∂P) ≤ 1 := by
    calc
      _ ≤ ∫ _ω, (1 : ℝ) ∂P := integral_mono h₀ (integrable_const 1)
        (fun ω => (outcome0 ω).property.2)
      _ = 1 := by simp
  have h₁hi : (∫ ω, ((outcome1 ω : OutcomeSpace) : ℝ) ∂P) ≤ 1 := by
    calc
      _ ≤ ∫ _ω, (1 : ℝ) ∂P := integral_mono h₁ (integrable_const 1)
        (fun ω => (outcome1 ω).property.2)
      _ = 1 := by simp
  rw [ate_eq_potentialOutcomeMeans_sub]
  exact ⟨by linarith, by linarith⟩

-- @node: externalFullInterval
/-- For [the specified mathematical inputs](hyp:ε,J,n,m), [this definition](goal) introduces the corresponding object. -/
def externalFullInterval (ε : ℝ) (J n m : ℕ) :
    ExternalIntervalProcedure ε J n m where
  lo := fun _ => -1
  hi := fun _ => 1
  measurable_lo := measurable_const
  measurable_hi := measurable_const
  lower_bound := by intro; norm_num
  ordered := by intro; norm_num
  upper_bound := by intro; norm_num

-- @node: externalFullInterval_honest
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hα,Qj,hTrial,hLog,hInd), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalFullInterval_honest {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ) (hα : 0 ≤ α)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj) :
    externalFullInterval ε J n m ∈ externalHonestProcedures g Qj α := by
  intro PH hPH
  letI : IsProbabilityMeasure (Qj PH.1 PH.2) :=
    externalLaw_jointExperiment_probability g Qj hTrial hLog hInd PH hPH
  letI : IsProbabilityMeasure (externalExperiment n m PH.1 PH.2) := by
    rw [← jointTrialLog_eq_externalExperiment g Qj hTrial hLog hInd PH hPH]
    infer_instance
  letI : IsProbabilityMeasure PH.1 := hPH.1
  have hmem := externalATE_mem_Icc PH.1
  have hset : {x : ExternalSample ε J n m |
      (externalFullInterval ε J n m).contains x (ate PH.1)} = Set.univ := by
    ext x
    simp [ExternalIntervalProcedure.contains, externalFullInterval, hmem]
  rw [hset]
  simp only [Measure.real_def, measure_univ, ENNReal.toReal_one]
  linarith

-- @node: externalExcessIntegral_le_two
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hTrial,hLog,hInd,C,PH,hPH), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalExcessIntegral_le_two {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (C : ExternalIntervalProcedure ε J n m)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) :
    (∫ x, max 0 (C.length x -
      sharpATELength PH.2 g (releasedLaw PH.1)
        (externalLawCellMasses g PH hPH)) ∂Qj PH.1 PH.2) ≤ 2 := by
  letI : IsProbabilityMeasure (Qj PH.1 PH.2) :=
    externalLaw_jointExperiment_probability g Qj hTrial hLog hInd PH hPH
  have hsharp : 0 ≤ sharpATELength PH.2 g (releasedLaw PH.1)
      (externalLawCellMasses g PH hPH) :=
    sharpATELength_nonneg_of_overlap PH.2 g (releasedLaw PH.1)
      (externalLawCellMasses g PH hPH) hPH.2.2.overlap
  have hpoint : ∀ x, max 0 (C.length x -
      sharpATELength PH.2 g (releasedLaw PH.1)
        (externalLawCellMasses g PH hPH)) ≤ 2 := by
    intro x
    have hlo := C.lower_bound x
    have hhi := C.upper_bound x
    dsimp [ExternalIntervalProcedure.length]
    exact max_le (by norm_num) (by linarith)
  calc
    _ ≤ ∫ _x, (2 : ℝ) ∂Qj PH.1 PH.2 := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with x
        exact le_max_left _ _
      · exact integrable_const 2
      · filter_upwards [] with x
        exact hpoint x
    _ = 2 := by simp

end
end CausalSmith.PartialID.UnlinkedPropensityAte
