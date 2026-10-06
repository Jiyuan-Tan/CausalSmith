module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.TunedEnergyGuarantees

/-! The actual finite-sample law of the training block and twelve evaluation roles.
Unused observations and public randomization integrate out, leaving exactly the
independent product needed for conditional coverage and length bounds. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Retain precisely the training and evaluation records used by the frozen rule. -/
-- @node: tunedRecords
def tunedRecords (n : ℕ) (ω : SampleSpace n) :
    Data (roleSize n) × EvalData (roleSize n) :=
  (foldData n ω.1 0, fun b => foldData n ω.1 (Fin.ofNat 13 (b.val + 1)))

-- @node: measurable_tunedRecords
@[fun_prop] lemma measurable_tunedRecords (n : ℕ) : Measurable (tunedRecords n) := by
  unfold tunedRecords foldData
  fun_prop

/-- Splitting the thirteen independent folds isolates the training law. -/
-- @node: fold_training_eval_map
lemma fold_training_eval_map (P : ObsLaw) (n : ℕ) :
    (dataLaw P n).map (fun data =>
      (foldData n data 0, fun b : Fin 12 =>
        foldData n data (Fin.ofNat 13 (b.val + 1)))) =
      (dataLaw P (roleSize n)).prod (evalLaw P (roleSize n)) := by
  let : IsProbabilityMeasure (dataLaw P (roleSize n)) := by
    unfold dataLaw
    infer_instance
  have hs := (measurePreserving_piFinSuccAbove
    (fun _ : Fin 13 => dataLaw P (roleSize n)) 0).map_eq
  have he : (fun data : Data n =>
      (foldData n data 0, fun b : Fin 12 => foldData n data (Fin.ofNat 13 (b.val + 1)))) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 13 => Data (roleSize n)) 0) ∘
        (fun data b => foldData n data b) := by
    funext data
    apply Prod.ext
    · rfl
    · funext b
      change foldData n data (Fin.ofNat 13 (b.val + 1)) =
        foldData n data ((0 : Fin 13).succAbove b)
      congr 1
      apply Fin.ext
      simp [Fin.succAbove, Fin.ofNat, Nat.mod_eq_of_lt (by omega : b.val + 1 < 13)]
  rw [he, ← Measure.map_map (by fun_prop) (by unfold foldData; fun_prop), fold_product_law]
  exact hs

/-- All remaining observations and the independent randomization disappear under
record selection; no divisibility assumption on the original sample size is needed. -/
-- @node: sampleLaw_tunedRecords_map
lemma sampleLaw_tunedRecords_map (P : ObsLaw) (n : ℕ) :
    (sampleLaw P n).map (tunedRecords n) =
      (dataLaw P (roleSize n)).prod (evalLaw P (roleSize n)) := by
  have he : tunedRecords n = (fun data : Data n =>
      (foldData n data 0, fun b : Fin 12 =>
        foldData n data (Fin.ofNat 13 (b.val + 1)))) ∘ Prod.fst := rfl
  rw [he, ← Measure.map_map (by unfold foldData; fun_prop) measurable_fst]
  rw [sampleLaw, Measure.map_fst_prod]
  simpa using fold_training_eval_map P n

/-- The statistic in the reporting rule is exactly the conditional energy after
selecting its training and evaluation records. -/
-- @node: tunedEnergy_eq_selected_energy
lemma tunedEnergy_eq_selected_energy (n : ℕ) (ω : SampleSpace n) :
    tunedEnergy n ω.1 = energy (tunedRecords n ω).1
      (tunedMx (roleSize n)) (tunedMy (roleSize n))
      (tunedL (roleSize n)) (tunedT (roleSize n)) (tunedJ (roleSize n))
      (tunedQ (roleSize n)) (tunedKt (roleSize n)) (tunedRecords n ω).2 := rfl

/-- A measurable event about the retained records has exactly its independent
training/evaluation probability under the original randomized sampling law. -/
-- @node: sampleLaw_tunedRecords_event
lemma sampleLaw_tunedRecords_event (P : ObsLaw) (n : ℕ)
    (E : Set (Data (roleSize n) × EvalData (roleSize n))) (hE : MeasurableSet E) :
    (sampleLaw P n).real {ω | tunedRecords n ω ∈ E} =
      ((dataLaw P (roleSize n)).prod (evalLaw P (roleSize n))).real E := by
  rw [← sampleLaw_tunedRecords_map P n, measureReal_def, measureReal_def,
    Measure.map_apply (measurable_tunedRecords n) hE]
  rfl

/-- Integrating any measurable bounded reported quantity can be performed under
the exact training/evaluation product law. -/
-- @node: sampleLaw_tunedRecords_integral
lemma sampleLaw_tunedRecords_integral (P : ObsLaw) (n : ℕ)
    (f : Data (roleSize n) × EvalData (roleSize n) → ℝ) (hf : Measurable f) :
    (∫ ω, f (tunedRecords n ω) ∂sampleLaw P n) =
      ∫ z, f z ∂(dataLaw P (roleSize n)).prod (evalLaw P (roleSize n)) := by
  rw [← sampleLaw_tunedRecords_map P n]
  exact (integral_map (measurable_tunedRecords n).aemeasurable
    hf.aestronglyMeasurable).symm

/-- Fubini transfers an integrable reported quantity to the conditional
expectation over evaluation roles followed by averaging the training records. -/
-- @node: sampleLaw_tunedRecords_integral_iterated
lemma sampleLaw_tunedRecords_integral_iterated (P : ObsLaw) (n : ℕ)
    (f : Data (roleSize n) × EvalData (roleSize n) → ℝ) (hf : Measurable f)
    (hi : Integrable f ((dataLaw P (roleSize n)).prod (evalLaw P (roleSize n)))) :
    (∫ ω, f (tunedRecords n ω) ∂sampleLaw P n) =
      ∫ train, (∫ eval, f (train, eval) ∂evalLaw P (roleSize n))
        ∂dataLaw P (roleSize n) := by
  let : IsProbabilityMeasure (dataLaw P (roleSize n)) := by
    unfold dataLaw
    infer_instance
  let : IsProbabilityMeasure (evalLaw P (roleSize n)) := by
    unfold evalLaw
    infer_instance
  rw [sampleLaw_tunedRecords_integral P n f hf]
  exact integral_prod f hi

/-- On the reporting branch the actual expected length is the average of the
conditional lengths already bounded for each good trained realization. -/
-- @node: starRule_expectedLength_iterated
lemma starRule_expectedLength_iterated (P : ObsLaw) (n : ℕ)
    (hbranch : reportingBranch n) :
    expectedLength P n (starRule n) =
      ∫ train, (∫ eval, intervalLength (invSet (energy train
        (tunedMx (roleSize n)) (tunedMy (roleSize n))
        (tunedL (roleSize n)) (tunedT (roleSize n)) (tunedJ (roleSize n))
        (tunedQ (roleSize n)) (tunedKt (roleSize n)) eval)
        (aci (tunedB n) (tunedW n))
        (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))))
          ∂evalLaw P (roleSize n)) ∂dataLaw P (roleSize n) := by
  let m := roleSize n
  let a := aci (tunedB n) (tunedW n)
  let d := dci (tunedB n) (tunedW n) (tunedV n) (tunedJ m)
  let Z := fun z : Data m × EvalData m => energy z.1
    (tunedMx m) (tunedMy m) (tunedL m) (tunedT m) (tunedJ m)
    (tunedQ m) (tunedKt m) z.2
  let f := fun z => intervalLength (invSet (Z z) a d)
  have hZ : Measurable Z := by fun_prop
  have hf : Measurable f := by
    have he : f = fun z => invUpper (Z z) a d - invLower (Z z) a d := by
      funext z
      exact inversion_length_eq _ _ _ (tuned_inversion_nonneg n).1
    rw [he]
    exact ((inversion_endpoints_measurable a d).2.comp hZ).sub
      ((inversion_endpoints_measurable a d).1.comp hZ)
  let : IsProbabilityMeasure (dataLaw P m) := by unfold dataLaw; infer_instance
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  have hi : Integrable f ((dataLaw P m).prod (evalLaw P m)) :=
    Integrable.of_bound hf.aestronglyMeasurable 16
      (Filter.Eventually.of_forall (fun z => by
        have hr := inversion_length_range (Z z) a d
        rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
        exact hr.2))
  have he : (fun ω => intervalLength (starRule n ω)) =
      fun ω => f (tunedRecords n ω) := by
    funext ω
    simp only [starRule, if_pos hbranch]
    rfl
  unfold expectedLength
  rw [he]
  exact sampleLaw_tunedRecords_integral_iterated P n f hf hi

/-- Coverage of the actual frozen rule equals coverage in the independent
training/evaluation experiment on every reporting branch. -/
-- @node: starRule_coverage_product
lemma starRule_coverage_product (P : ObsLaw) (n : ℕ) (hbranch : reportingBranch n) :
    coverage P n (starRule n) =
      ((dataLaw P (roleSize n)).prod (evalLaw P (roleSize n))).real
        {z | Psi P ∈ invSet (energy z.1 (tunedMx (roleSize n))
          (tunedMy (roleSize n)) (tunedL (roleSize n)) (tunedT (roleSize n))
          (tunedJ (roleSize n)) (tunedQ (roleSize n)) (tunedKt (roleSize n)) z.2)
          (aci (tunedB n) (tunedW n))
          (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)))} := by
  let a := aci (tunedB n) (tunedW n)
  let d := dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))
  let Z := fun z : Data (roleSize n) × EvalData (roleSize n) => energy z.1
    (tunedMx (roleSize n)) (tunedMy (roleSize n)) (tunedL (roleSize n))
    (tunedT (roleSize n)) (tunedJ (roleSize n)) (tunedQ (roleSize n))
    (tunedKt (roleSize n)) z.2
  have hZ : Measurable Z := by fun_prop
  have hE : MeasurableSet {z | Psi P ∈ invSet (Z z) a d} := by
    have heq : {z | Psi P ∈ invSet (Z z) a d} =
        {z | invLower (Z z) a d ≤ Psi P ∧ Psi P ≤ invUpper (Z z) a d} := by
      ext z
      change Psi P ∈ invSet (Z z) a d ↔ _
      rw [invSet_eq_endpoint_interval (Z z) a d (tuned_inversion_nonneg n).1]
      rfl
    rw [heq]
    exact (measurableSet_le ((inversion_endpoints_measurable a d).1.comp hZ)
      measurable_const).inter (measurableSet_le measurable_const
        ((inversion_endpoints_measurable a d).2.comp hZ))
  have he : {ω | Psi P ∈ starRule n ω} =
      {ω | tunedRecords n ω ∈ {z | Psi P ∈ invSet (Z z) a d}} := by
    ext ω
    simp only [starRule, if_pos hbranch, Set.mem_ofPred_eq]
    rfl
  unfold coverage
  rw [he]
  exact sampleLaw_tunedRecords_event P n _ hE

end CausalSmith.Stat.DensityEffectRoughNull
