module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.Hellinger
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.ComponentProduct
/-! # Original-record likelihood densities
The independent potential-outcome kernels yield the conditional likelihoods
used in the marked-component information calculation. -/
@[expose] public section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
/-- Given [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the observed bern product conclusion](goal) holds. -/
lemma observed_bern_product (e p q : ℝ) (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    ((bern e).prod ((bern p).prod (bern q))).map
      (fun w => (w.1, if w.1 then w.2.2 else w.2.1)) =
      (bern e).bind (fun A => (Measure.dirac A).prod (bern (if A then q else p))) := by
  letI := bern_probability p hp
  letI := bern_probability q hq
  apply Measure.ext_of_singleton
  rintro ⟨A,Y⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable]
  cases A <;> cases Y <;>
    simp [bern, Measure.prod_add, Measure.add_prod, Measure.prod_smul_left,
      Measure.prod_smul_right, Measure.dirac_prod_dirac, lintegral_add_measure,
      lintegral_smul_measure, lintegral_dirac, Measure.prod_prod]
  all_goals
    have hpn : ENNReal.ofReal (1-p) + ENNReal.ofReal p = 1 := by
      rw [← ENNReal.ofReal_add (by linarith [hp.2]) hp.1]
      norm_num
    have hqn : ENNReal.ofReal (1-q) + ENNReal.ofReal q = 1 := by
      rw [← ENNReal.ofReal_add (by linarith [hq.2]) hq.1]
      norm_num
  case false.false =>
    convert congrArg (fun t => t*(ENNReal.ofReal (1-p)*ENNReal.ofReal (1-e))) hqn using 1 <;> ring
  case false.true =>
    convert congrArg (fun t => t*(ENNReal.ofReal p*ENNReal.ofReal (1-e))) hqn using 1 <;> ring
  case true.false =>
    convert congrArg (fun t => t*(ENNReal.ofReal e*ENNReal.ofReal (1-q))) hpn using 1 <;> ring
  case true.true =>
    convert congrArg (fun t => t*(ENNReal.ofReal e*ENNReal.ofReal q)) hpn using 1 <;> ring
/-- Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the independent obs law conclusion](goal) holds. -/
lemma independent_obsLaw (d : ℕ) (e p q : Cov d → ℝ)
    (he : Measurable e) (hp : Measurable p) (hq : Measurable q) :
    let P := independentPrimitive e p q he hp hq
    obsLaw P = (uniformLaw d).bind (fun x =>
      (Measure.dirac x).prod (conditionalObserved P x)) := by
  dsimp only
  unfold obsLaw independentPrimitive independentFullLaw
  rw [independent_map_bind _ _ _ (measurable_independentRecordKernel e p q he hp hq)
    (show Measurable (observed (d := d)) by
      unfold observed
      exact measurable_fst.prodMk (measurable_fst.comp measurable_snd |>.prodMk
        (Measurable.ite ((measurableSet_singleton true).preimage (by fun_prop))
          (by fun_prop) (by fun_prop))) )]
  congr 1
  funext x
  let μ := (bern (probabilityClip (e x))).prod
    ((bern (probabilityClip (p x))).prod (bern (probabilityClip (q x))))
  have hmap := Measure.map_prod_map (Measure.dirac x) μ measurable_id
    (measurable_of_countable (fun w : Bool × Bool × Bool =>
      (w.1, if w.1 then w.2.2 else w.2.1)))
  change ((Measure.dirac x).prod μ).map
    (Prod.map id (fun w => (w.1, if w.1 then w.2.2 else w.2.1))) = _
  rw [← hmap, Measure.map_id]
  congr 1
  exact observed_bern_product _ _ _ (probabilityClip_mem _) (probabilityClip_mem _)

/-- Given [the specified input X](hyp:X), [the specified input S](hyp:S), [the reference measure ν](hyp:ν), [the finite measure μ](hyp:μ), [the kernel κ](hyp:κ), [its measurability](hyp:hκ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input hf0](hyp:hf0), [the density representation](hyp:hκf), [the finite joint density conclusion](goal) holds. -/
lemma finite_joint_density {X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [Fintype S] [MeasurableSingletonClass S] (ν : Measure X) (μ : Measure S)
    [IsFiniteMeasure μ] (κ : X → Measure S) (hκ : Measurable κ)
    (f : X × S → ℝ) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (hκf : ∀ x, κ x = μ.withDensity (fun s => ENNReal.ofReal (f (x,s)))) :
    ν.bind (fun x => (Measure.dirac x).prod (κ x)) =
      (ν.prod μ).withDensity (fun z => ENNReal.ofReal (f z)) := by
  classical
  have hk : Measurable (fun x => (Measure.dirac x).prod (κ x)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    rw [show (fun x => (Measure.dirac x).prod (κ x) A) =
      (fun x => ∑ s : S, if (x,s) ∈ A then κ x {s} else 0) by
        funext x
        rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hA]
        rw [← Measure.sum_smul_dirac (κ x)]
        simp only [Measure.sum_apply _ (hA.preimage measurable_prodMk_left),
          Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (hA.preimage measurable_prodMk_left)]
        simp [tsum_fintype, Set.indicator, mul_ite]]
    apply Finset.measurable_fun_sum
    intro s _
    exact Measurable.ite (hA.preimage (measurable_id.prodMk measurable_const))
      ((Measure.measurable_coe (measurableSet_singleton s)).comp hκ) measurable_const
  ext A hA
  rw [Measure.bind_apply hA hk.aemeasurable, withDensity_apply _ hA,
    ← lintegral_indicator hA, lintegral_prod _ (hf.ennreal_ofReal.indicator hA).aemeasurable]
  apply lintegral_congr
  intro x
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hA, hκf,
    withDensity_apply _ (hA.preimage measurable_prodMk_left), ← lintegral_indicator]
  · rfl
  · exact hA.preimage measurable_prodMk_left
/-- Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the measurable label likelihood conclusion](goal) holds. -/
@[fun_prop] lemma measurable_labelLikelihood {d : ℕ} (P : PrimitiveLaw d) :
    Measurable (fun z : Cov d × (Bool × Bool) => labelLikelihood P z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro s
  unfold labelLikelihood
  have he := (Measure.measurable_coe (measurableSet_singleton s.1)).comp (measurable_bern P.e P.measurable_e)
  have hm : Measurable (fun x => if s.1 then P.mu1 x else P.mu0 x) := by
    cases s.1 <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      first | exact P.measurable_mu0 | exact P.measurable_mu1
  have hy := (Measure.measurable_coe (measurableSet_singleton s.2)).comp (measurable_bern _ hm)
  exact (measurable_const.mul he.ennreal_toReal).mul hy.ennreal_toReal

/-- Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input x](hyp:x), [the conditional observed density conclusion](goal) holds. -/
lemma conditionalObserved_density {d : ℕ} (P : PrimitiveLaw d) (x : Cov d) :
    conditionalObserved P x = fairObserved.withDensity
      (fun s => ENNReal.ofReal (labelLikelihood P x s)) := by
  apply Measure.ext_of_singleton
  intro s
  rw [conditionalObserved_singleton, withDensity_apply _ (measurableSet_singleton s)]
  rw [lintegral_singleton]
  have hs : fairObserved {s} = ENNReal.ofReal (1/4:ℝ) := by
    rcases s with ⟨A,Y⟩
    cases A <;> cases Y <;> norm_num [fairObserved, bern, Measure.prod_apply, ← ENNReal.ofReal_mul]
  rw [hs]
  rcases s with ⟨A,Y⟩
  cases A <;> cases Y <;>
    norm_num [bern, labelLikelihood, ENNReal.ofReal_mul, ENNReal.ofReal_toReal,
      bern_singleton_ne_top, mul_assoc, mul_comm, mul_left_comm]
  all_goals
    have h4 : (4:ℝ≥0∞)*ENNReal.ofReal (1/4:ℝ) = 1 := by
      rw [show (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [← mul_assoc, h4, one_mul]
/-- Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input x](hyp:x), [the auxiliary likelihood density conclusion](goal) holds. -/
lemma auxiliaryLikelihood_density {d : ℕ} (P : PrimitiveLaw d) (x : Cov d) :
    bern (P.e x) = (bern (1/2)).withDensity
      (fun s => ENNReal.ofReal (auxiliaryLikelihood P x s)) := by
  apply Measure.ext_of_singleton
  intro s
  rw [withDensity_apply _ (measurableSet_singleton s), lintegral_singleton]
  have hs : bern (1/2) {s} = ENNReal.ofReal (1/2:ℝ) := by cases s <;> norm_num [bern]
  rw [hs]
  unfold auxiliaryLikelihood
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal (bern_singleton_ne_top _ _)]
  have h2 : ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (1/2:ℝ) = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
  rw [mul_assoc, mul_comm (bern (P.e x) {s}), ← mul_assoc, h2, one_mul]

/-- Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the measurable auxiliary likelihood conclusion](goal) holds. -/
@[fun_prop] lemma measurable_auxiliaryLikelihood {d : ℕ} (P : PrimitiveLaw d) :
    Measurable (fun z : Cov d × Bool => auxiliaryLikelihood P z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro s
  unfold auxiliaryLikelihood
  exact measurable_const.mul ((Measure.measurable_coe (measurableSet_singleton s)).comp
    (measurable_bern P.e P.measurable_e)).ennreal_toReal

/-- Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the independent obs law density conclusion](goal) holds. -/
lemma independent_obsLaw_density (d : ℕ) (e p q : Cov d → ℝ)
    (he : Measurable e) (hp : Measurable p) (hq : Measurable q) :
    let P := independentPrimitive e p q he hp hq
    obsLaw P = ((uniformLaw d).prod fairObserved).withDensity
      (fun z => ENNReal.ofReal (labelLikelihood P z.1 z.2)) := by
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  dsimp only
  rw [independent_obsLaw]
  let P := independentPrimitive e p q he hp hq
  apply finite_joint_density
  · apply Measure.measurable_of_measurable_coe
    intro A hA
    rw [show (fun x => conditionalObserved P x A) =
      (fun x => ∑ s : Bool × Bool, if s ∈ A then conditionalObserved P x {s} else 0) by
        funext x
        rw [← Measure.sum_smul_dirac (conditionalObserved P x)]
        simp [Measure.sum_apply, hA, tsum_fintype, Measure.dirac_apply' _ hA, Set.indicator, mul_ite]]
    apply Finset.measurable_fun_sum
    intro s _
    by_cases hs : s ∈ A
    · simp only [if_pos hs, conditionalObserved_singleton]
      have he := (Measure.measurable_coe (measurableSet_singleton s.1)).comp (measurable_bern P.e P.measurable_e)
      have hm : Measurable (fun x => if s.1 then P.mu1 x else P.mu0 x) := by
        cases s.1 <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
          first | exact P.measurable_mu0 | exact P.measurable_mu1
      exact he.mul ((Measure.measurable_coe (measurableSet_singleton s.2)).comp (measurable_bern _ hm))
    · simp only [if_neg hs]; exact measurable_const
  · exact measurable_labelLikelihood P
  · intro z; unfold labelLikelihood; positivity
  · exact conditionalObserved_density P

/-- Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the independent xa law density conclusion](goal) holds. -/
lemma independent_xaLaw_density (d : ℕ) (e p q : Cov d → ℝ)
    (he : Measurable e) (hp : Measurable p) (hq : Measurable q) :
    let P := independentPrimitive e p q he hp hq
    xaLaw P = ((uniformLaw d).prod (bern (1/2))).withDensity
      (fun z => ENNReal.ofReal (auxiliaryLikelihood P z.1 z.2)) := by
  letI := bern_probability (1/2) (by norm_num)
  dsimp only
  let P := independentPrimitive e p q he hp hq
  have hxa : xaLaw P = (uniformLaw d).bind (fun x => (Measure.dirac x).prod (bern (P.e x))) := by
    change (independentFullLaw e p q).map _ = _
    rw [independentFullLaw_margin d e p q he hp hq |>.1,
      independentFullLaw_covariates d e p q he hp hq]
    exact (bernRecord_bind_eq_compProd d _ (measurable_probabilityClip e he)
      (fun x => probabilityClip_mem _)).symm
  rw [hxa]
  apply finite_joint_density
  · exact measurable_bern P.e P.measurable_e
  · exact measurable_auxiliaryLikelihood P
  · intro z; unfold auxiliaryLikelihood; positivity
  · exact auxiliaryLikelihood_density P
/-- Given [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the specified input s](hyp:s), [the bern atom le one conclusion](goal) holds. -/
lemma bern_atom_le_one (p : ℝ) (hp : p ∈ Icc (0:ℝ) 1) (s : Bool) :
    (bern p {s}).toReal ≤ 1 := by
  letI := bern_probability p hp
  have h : bern p {s} ≤ bern p univ := measure_mono (by simp)
  rw [measure_univ] at h
  simpa using ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ⊤) h

/-- Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the independent likelihood bounds conclusion](goal) holds. -/
lemma independent_likelihood_bounds (d : ℕ) (e p q : Cov d → ℝ)
    (he : Measurable e) (hp : Measurable p) (hq : Measurable q) :
    let P := independentPrimitive e p q he hp hq
    (∀ z : Cov d × (Bool × Bool), 0 ≤ labelLikelihood P z.1 z.2 ∧ labelLikelihood P z.1 z.2 ≤ 4) ∧
    (∀ z : Cov d × Bool, 0 ≤ auxiliaryLikelihood P z.1 z.2 ∧ auxiliaryLikelihood P z.1 z.2 ≤ 2) := by
  let P := independentPrimitive e p q he hp hq
  have he1 (x : Cov d) : P.e x ∈ Icc (0:ℝ) 1 := probabilityClip_mem _
  have hm1 (x : Cov d) (A : Bool) : (if A then P.mu1 x else P.mu0 x) ∈ Icc (0:ℝ) 1 := by
    cases A <;> exact probabilityClip_mem _
  constructor
  · intro z
    have ha := bern_atom_le_one _ (he1 z.1) z.2.1
    have hy := bern_atom_le_one _ (hm1 z.1 z.2.1) z.2.2
    constructor
    · unfold labelLikelihood; positivity
    · unfold labelLikelihood
      have hb := mul_le_mul ha hy (ENNReal.toReal_nonneg) zero_le_one
      nlinarith
  · intro z
    have ha := bern_atom_le_one _ (he1 z.1) z.2
    constructor
    · unfold auxiliaryLikelihood; positivity
    · unfold auxiliaryLikelihood; linarith

/-- Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the independent likelihood integrable conclusion](goal) holds. -/
lemma independent_likelihood_integrable (d : ℕ) (e p q : Cov d → ℝ)
    (he : Measurable e) (hp : Measurable p) (hq : Measurable q) :
    let P := independentPrimitive e p q he hp hq
    Integrable (fun z : Cov d × (Bool × Bool) => labelLikelihood P z.1 z.2)
      ((uniformLaw d).prod fairObserved) ∧
    Integrable (fun z : Cov d × Bool => auxiliaryLikelihood P z.1 z.2)
      ((uniformLaw d).prod (bern (1/2))) := by
  letI := uniformLaw_probability d
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  let P := independentPrimitive e p q he hp hq
  obtain ⟨hl, ha⟩ := independent_likelihood_bounds d e p q he hp hq
  constructor
  · apply (integrable_const (4:ℝ)).mono' (measurable_labelLikelihood P).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hl z).1]; exact (hl z).2)
  · apply (integrable_const (2:ℝ)).mono' (measurable_auxiliaryLikelihood P).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (ha z).1]; exact (ha z).2)
/-- Reference records have the common uniform design and independent fair spins.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [fair dataset](goal) is the corresponding construction. -/
def fairDataset (d n m : ℕ) : Measure (Dataset d n m) :=
  (Measure.pi (fun _ : Fin n => (uniformLaw d).prod fairObserved)).prod
    (Measure.pi (fun _ : Fin m => (uniformLaw d).prod (bern (1/2))))

/-- Concatenate the covariates of the original labeled and auxiliary records.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input D](hyp:D), [dataset covariates](goal) is the corresponding construction. -/
def datasetCovariates {d n m : ℕ} (D : Dataset d n m) : Fin (n+m) → Cov d :=
  recordCovariates (fun i => (D.1 i).1) (fun j => (D.2 j).1)

/-- Retain the two observed bits in labeled records and the treatment bit in auxiliaries.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input D](hyp:D), [dataset spins](goal) is the corresponding construction. -/
def datasetSpins {d n m : ℕ} (D : Dataset d n m) : RecordSpins n m :=
  (fun i => (D.1 i).2, fun j => (D.2 j).2)

/-- The original-record mixture likelihood is the conditional mixed likelihood.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input D](hyp:D), [dataset density](goal) is the corresponding construction. -/
def datasetDensity {d n m : ℕ} (H : MarkedPriors d) (theta : Bool)
    (D : Dataset d n m) : ℝ := mixedDensity H theta (datasetCovariates D) (datasetSpins D)

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input D](hyp:D), [the dataset record product conclusion](goal) holds. -/
lemma dataset_record_product {d n m : ℕ} (P : PrimitiveLaw d) (D : Dataset d n m) :
    (∏ i, recordLikelihood P (datasetCovariates D) (datasetSpins D) i) =
      (∏ i : Fin n, labelLikelihood P (D.1 i).1 (D.1 i).2) *
      (∏ j : Fin m, auxiliaryLikelihood P (D.2 j).1 (D.2 j).2) := by
  rw [Fin.prod_univ_add]
  simp [recordLikelihood, datasetCovariates, datasetSpins, recordCovariates]

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the measurable dataset density conclusion](goal) holds. -/
@[fun_prop] lemma measurable_datasetDensity {d n m : ℕ} (H : MarkedPriors d) (theta : Bool) :
    Measurable (datasetDensity (n:=n) (m:=m) H theta) := by
  unfold datasetDensity mixedDensity
  simp_rw [dataset_record_product]
  apply Finset.measurable_fun_sum
  intro sigma _
  apply Measurable.const_mul
  exact (Finset.measurable_prod _ (fun i _ => (measurable_labelLikelihood _).comp (by fun_prop))).mul
    (Finset.measurable_prod _ (fun j _ => (measurable_auxiliaryLikelihood _).comp (by fun_prop)))

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input hw](hyp:hw), [the specified input D](hyp:D), [the dataset density nonneg conclusion](goal) holds. -/
lemma datasetDensity_nonneg {d n m : ℕ} (H : MarkedPriors d) (theta : Bool)
    (hw : ∀ sigma, 0 ≤ H.weight theta sigma) (D : Dataset d n m) :
    0 ≤ datasetDensity H theta D := by
  unfold datasetDensity mixedDensity
  apply Finset.sum_nonneg
  intro sigma _
  apply mul_nonneg (hw sigma)
  apply Finset.prod_nonneg
  intro i _
  unfold recordLikelihood
  refine Fin.addCases ?_ ?_ i
  · intro j; simp only [Fin.addCases_left]; unfold labelLikelihood; positivity
  · intro j; simp only [Fin.addCases_right]; unfold auxiliaryLikelihood; positivity

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the independent dataset density conclusion](goal) holds. -/
lemma independent_dataset_density (d n m : ℕ) (e p q : Cov d → ℝ)
    (he : Measurable e) (hp : Measurable p) (hq : Measurable q) :
    let P := independentPrimitive e p q he hp hq
    (Measure.pi (fun _ : Fin n => obsLaw P)).prod
      (Measure.pi (fun _ : Fin m => xaLaw P)) =
    (fairDataset d n m).withDensity (fun D => ENNReal.ofReal
      (∏ i, recordLikelihood P (datasetCovariates D) (datasetSpins D) i)) := by
  letI := uniformLaw_probability d
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  let P := independentPrimitive e p q he hp hq
  letI : IsProbabilityMeasure (obsLaw P) := by
    unfold obsLaw
    apply Measure.isProbabilityMeasure_map
    have ho : Measurable (observed (d := d)) := by
      unfold observed
      apply Measurable.prodMk (by fun_prop)
      apply Measurable.prodMk (by fun_prop)
      exact Measurable.ite ((measurableSet_singleton true).preimage (by fun_prop)) (by fun_prop) (by fun_prop)
    exact ho.aemeasurable
  letI : IsProbabilityMeasure (xaLaw P) := by
    unfold xaLaw
    exact Measure.isProbabilityMeasure_map (show Measurable (fun w : FullRecord d => (w.1,w.2.1)) by fun_prop).aemeasurable
  obtain ⟨hl, ha⟩ := independent_likelihood_integrable d e p q he hp hq
  have hL := pi_real_density (fun _ : Fin n => (uniformLaw d).prod fairObserved)
    (fun _ => obsLaw P) (fun _ z => labelLikelihood P z.1 z.2) (fun _ => hl)
    (fun _ z => by unfold labelLikelihood; positivity)
    (fun _ => independent_obsLaw_density d e p q he hp hq)
  have hA := pi_real_density (fun _ : Fin m => (uniformLaw d).prod (bern (1/2)))
    (fun _ => xaLaw P) (fun _ z => auxiliaryLikelihood P z.1 z.2) (fun _ => ha)
    (fun _ z => by unfold auxiliaryLikelihood; positivity)
    (fun _ => independent_xaLaw_density d e p q he hp hq)
  dsimp only
  rw [hL, hA, prod_withDensity (by fun_prop) (by fun_prop)]
  unfold fairDataset
  apply congrArg _
  funext D
  rw [dataset_record_product, ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => by unfold labelLikelihood; positivity))]

/-- Given [the specified input S](hyp:S), [the specified input Q](hyp:Q), [the specified input w](hyp:w), [the specified input f](hyp:f), [the specified input hw](hyp:hw), [the specified input hf](hyp:hf), [the specified input hf0](hyp:hf0), [the specified input hQ](hyp:hQ), [the finite prior with density conclusion](goal) holds. -/
lemma finite_prior_withDensity {Ω S : Type*} [MeasurableSpace Ω] [Fintype S]
    (μ : Measure Ω) (Q : S → Measure Ω) (w : S → ℝ) (f : S → Ω → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hf : ∀ s, Measurable (f s)) (hf0 : ∀ s x, 0 ≤ f s x)
    (hQ : ∀ s, Q s = μ.withDensity (fun x => ENNReal.ofReal (f s x))) :
    (∑ s, ENNReal.ofReal (w s) • Q s) =
      μ.withDensity (fun x => ENNReal.ofReal (∑ s, w s * f s x)) := by
  ext A hA
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, hQ, withDensity_apply _ hA]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => mul_nonneg (hw s) (hf0 s _)),
    ENNReal.ofReal_mul (hw _)]
  rw [lintegral_finsetSum (f := fun s x => ENNReal.ofReal (w s) * ENNReal.ofReal (f s x)) Finset.univ
    (fun s _ => (measurable_const.mul (hf s).ennreal_ofReal))]
  simp only [lintegral_const_mul, (hf _).ennreal_ofReal]

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the marked mixture density conclusion](goal) holds. -/
lemma markedMixture_density (d n m : ℕ) (h delta a b : ℝ) (theta : Bool) :
    markedMixture (markedHandle d h delta a b) theta n m =
      (fairDataset d n m).withDensity (fun D => ENNReal.ofReal
        (datasetDensity (markedHandle d h delta a b) theta D)) := by
  unfold markedMixture
  apply finite_prior_withDensity
  · exact (marked_prior_mass d h delta theta).1
  · intro sigma
    simp_rw [dataset_record_product]
    exact (Finset.measurable_prod _ (fun i _ => (measurable_labelLikelihood _).comp (by fun_prop))).mul
      (Finset.measurable_prod _ (fun j _ => (measurable_auxiliaryLikelihood _).comp (by fun_prop)))
  · intro sigma D
    rw [dataset_record_product]
    apply mul_nonneg <;> apply Finset.prod_nonneg
    · intro i _; unfold labelLikelihood; positivity
    · intro j _; unfold auxiliaryLikelihood; positivity
  · intro sigma
    exact independent_dataset_density d n m _ _ _
      (measurable_markedPropensity h delta a sigma)
      (measurable_markedMean h delta a b theta false sigma)
      (measurable_markedMean h delta a b theta true sigma)
end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
