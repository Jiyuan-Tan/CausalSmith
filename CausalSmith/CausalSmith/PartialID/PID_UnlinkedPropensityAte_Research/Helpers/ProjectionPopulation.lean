module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionIntegrated

/-! Population arm-cell finite measures underlying the external projection. -/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: trialPopulationCells
/-- For [the specified mathematical inputs](hyp:J,μ,a,r), [this definition](goal) introduces the corresponding object. -/
def trialPopulationCells {J : ℕ} (μ : Measure (Observation J))
    (a : ArmSpace) (r : LabelSpace J) : Measure OutcomeSpace :=
  (μ.restrict {z | z.1 = r ∧ z.2.1 = a}).map (fun z => z.2.2)

-- @node: trialPopulationCells_apply
/-- Given [the stated mathematical inputs and assumptions](hyp:J,μ,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialPopulationCells_apply {J : ℕ} (μ : Measure (Observation J))
    (a : ArmSpace) (r : LabelSpace J) (B : Set OutcomeSpace)
    (hB : MeasurableSet B) :
    trialPopulationCells μ a r B =
      μ {z | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B} := by
  rw [trialPopulationCells, Measure.map_apply measurable_snd.snd hB,
    Measure.restrict_apply (hB.preimage measurable_snd.snd)]
  congr 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  tauto

-- @node: trialPopulationCells_real_apply
/-- Given [the stated mathematical inputs and assumptions](hyp:J,μ,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialPopulationCells_real_apply {J : ℕ} (μ : Measure (Observation J))
    (a : ArmSpace) (r : LabelSpace J) (B : Set OutcomeSpace)
    (hB : MeasurableSet B) :
    (trialPopulationCells μ a r).real B =
      μ.real {z | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B} := by
  unfold Measure.real
  rw [trialPopulationCells_apply μ a r B hB]

-- @node: outcomeCDFDistance_trialPopulationCells
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,x,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeCDFDistance_trialPopulationCells {J n : ℕ}
    (μ : Measure (Observation J)) (x : TrialSample n J)
    (a : ArmSpace) (r : LabelSpace J) :
    outcomeCDFDistance (empiricalTrialCells x a r) (trialPopulationCells μ a r) =
      |(empiricalTrialCells x a r).real Set.univ -
        μ.real {z | z.1 = r ∧ z.2.1 = a}| +
      ∫ t in (0 : ℝ)..1,
        |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
          μ.real {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}| := by
  unfold outcomeCDFDistance
  rw [trialPopulationCells_real_apply μ a r Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, and_true]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  change |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
      (trialPopulationCells μ a r).real {y | (y : ℝ) ≤ t}| = _
  rw [trialPopulationCells_real_apply μ a r _
    (measurableSet_le (by fun_prop) measurable_const)]
  rfl

-- @node: meanOutcomeCDFDistance_trialPopulationCells_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma meanOutcomeCDFDistance_trialPopulationCells_pi {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ] (hn : 0 < n)
    (a : ArmSpace) (r : LabelSpace J) :
    ∫ x : TrialSample n J,
      outcomeCDFDistance (empiricalTrialCells x a r) (trialPopulationCells μ a r)
        ∂Measure.pi (fun _ : Fin n => μ) ≤ 1 / Real.sqrt n := by
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
  simp_rw [outcomeCDFDistance_trialPopulationCells]
  rw [integral_add hmass hcdf]
  have h₁ := meanAbs_trialCellFrequency_pi μ hn a r Set.univ MeasurableSet.univ
  have h₂ := meanIntegratedAbs_empiricalTrialCellCDF_pi μ hn a r
  have h₁' : (∫ x : TrialSample n J,
      |(empiricalTrialCells x a r).real Set.univ -
        μ.real {z | z.1 = r ∧ z.2.1 = a}| ∂Measure.pi (fun _ : Fin n => μ)) ≤
      1 / (2 * Real.sqrt n) := by
    simpa only [empiricalTrialCells_real_apply a r Set.univ MeasurableSet.univ,
      Set.mem_univ, and_true] using h₁
  calc
    _ ≤ 1 / (2 * Real.sqrt n) + 1 / (2 * Real.sqrt n) := add_le_add h₁' h₂
    _ = 1 / Real.sqrt n := by ring

-- @node: sum_meanOutcomeCDFDistance_trialPopulationCells_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_meanOutcomeCDFDistance_trialPopulationCells_pi {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ] (hn : 0 < n) :
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ∫ x : TrialSample n J,
        outcomeCDFDistance (empiricalTrialCells x a r) (trialPopulationCells μ a r)
          ∂Measure.pi (fun _ : Fin n => μ)) ≤ 2 * J / Real.sqrt n := by
  calc
    _ ≤ ∑ a : ArmSpace, ∑ _r : LabelSpace J, (1 / Real.sqrt n : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro r _
      exact meanOutcomeCDFDistance_trialPopulationCells_pi μ hn a r
    _ = 2 * J / Real.sqrt n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Fintype.card_bool, nsmul_eq_mul]
      ring

end
end CausalSmith.PartialID.UnlinkedPropensityAte
