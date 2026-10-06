module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Estimator
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial.Basis
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Independence.Integration

/-!
# Treatment moments under the uniform design

Conditional Bernoulli integration and localization identities used to compute the
population rectangular Gram matrix from the original-record experiment.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 600000
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- For [covariate dimension d](hyp:d), [the observation map is Borel, including its treatment-dependent outcome selection](goal). -/
@[fun_prop] lemma population_measurable_observed {d : ℕ} : Measurable (observed (d := d)) := by
  unfold observed
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.prodMk (by fun_prop)
  exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    (by fun_prop) (by fun_prop)

/-- A primitive treatment-margin identity guarantees that its Bernoulli kernel is s-finite.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the primitive propensity kernel sfinite conclusion](goal) holds. -/
lemma primitive_propensity_kernel_sfinite {d : ℕ} (P : PrimitiveLaw d) :
    IsSFiniteKernel (bernKernel P.e P.measurable_e) := by
  by_contra hn
  have hz := P.margin_e
  rw [Measure.compProd_of_not_isSFiniteKernel _ _ hn] at hz
  have hm := congrArg (fun μ => μ Set.univ) hz
  have hmap : IsProbabilityMeasure (P.law.map (fun w => (w.1, w.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI := hmap
  simpa using hm

/-- The treatment-record law is a probability measure.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the xa law probability conclusion](goal) holds. -/
lemma xaLaw_probability {d : ℕ} (P : PrimitiveLaw d) : IsProbabilityMeasure (xaLaw P) := by
  unfold xaLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Discarding outcomes in an observed record gives exactly the treatment-record marginal.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the obs law map treatment conclusion](goal) holds. -/
lemma obsLaw_map_treatment {d : ℕ} (P : PrimitiveLaw d) :
    (obsLaw P).map (fun w => (w.1, w.2.1)) = xaLaw P := by
  unfold obsLaw xaLaw
  rw [Measure.map_map (by fun_prop) population_measurable_observed]
  rfl

/-- The observed-record law is a probability measure.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the obs law probability conclusion](goal) holds. -/
lemma obsLaw_probability {d : ℕ} (P : PrimitiveLaw d) : IsProbabilityMeasure (obsLaw P) := by
  unfold obsLaw
  exact Measure.isProbabilityMeasure_map population_measurable_observed.aemeasurable

/-- Integrating a treatment bit against its Bernoulli law returns its probability.  Given [the specified input p](hyp:p), [the specified input c](hyp:c), [the specified input hp](hyp:hp), [the bern bit integral conclusion](goal) holds. -/
lemma bern_bit_integral (p c : ℝ) (hp : 0 ≤ p) :
    (∫ a, c * bit a ∂bern p) = c * p := by
  have hi (q : ℝ) : Integrable (fun a => c * bit a) (ENNReal.ofReal q • Measure.dirac false) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  have hj (q : ℝ) : Integrable (fun a => c * bit a) (ENNReal.ofReal q • Measure.dirac true) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [bern, integral_add_measure (hi _) (hj _)]
  simp [integral_smul_measure, bit, ENNReal.toReal_ofReal hp]
  ring

/-- Uniform-design integration of a bounded covariate function times treatment
uses the primitive law's conditional treatment margin.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input hdesign](hyp:hdesign), [the specified input hoverlap](hyp:hoverlap), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the overlap level eps](hyp:eps), [the xa law treatment moment conclusion](goal) holds. -/
lemma xaLaw_treatment_moment {d : ℕ} {eps : ℝ} (P : PrimitiveLaw d)
    (hdesign : UniformDesign P) (hoverlap : Overlap eps P)
    (f : Cov d → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ w, f w.1 * bit w.2 ∂xaLaw P) = ∫ x, f x * P.e x ∂uniformLaw d := by
  letI : SFinite (uniformLaw d) := by unfold uniformLaw; infer_instance
  letI := primitive_propensity_kernel_sfinite P
  letI := xaLaw_probability P
  have hi : Integrable (fun w : Cov d × Bool => f w.1 * bit w.2) (xaLaw P) := by
    apply (integrable_const B).mono' ((hf.comp measurable_fst).mul (show Measurable (fun w : Cov d × Bool => bit w.2) from (measurable_of_finite bit).comp measurable_snd)).aestronglyMeasurable
    filter_upwards [] with w
    rcases w with ⟨x, a⟩
    cases a
    · simpa [bit] using (norm_nonneg (f x)).trans (hB x)
    · simpa [bit] using hB x
  have hmargin : xaLaw P = uniformLaw d ⊗ₘ bernKernel P.e P.measurable_e := by
    exact P.margin_e.trans (congrArg (fun μ => μ ⊗ₘ bernKernel P.e P.measurable_e) hdesign)
  rw [hmargin] at hi ⊢
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (show MeasurableSet (cube d) from by
    unfold cube; simp only [setOf_forall]; exact MeasurableSet.iInter (fun i =>
      measurableSet_Icc.preimage (by fun_prop)))] with x hx
  exact bern_bit_integral (P.e x) (f x) (by linarith [(hoverlap.unit x hx).1])

/-- Weighted integration under the uniform design is exactly localization integration.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input f](hyp:f), [the uniform law localization integral conclusion](goal) holds. -/
lemma uniformLaw_localization_integral (d : ℕ) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (f : Cov d → ℝ) :
    (∫ x, locWeight h x * f x ∂uniformLaw d) = ∫ x, f x ∂locLaw d h := by
  have hsub : locCube d h ⊆ cube d := by
    intro x hx i
    constructor <;> linarith [(hx i).1, (hx i).2]
  have hfun : (fun x => locWeight h x * f x) =
      (locCube d h).indicator (fun x => h^(-(d:ℝ)) * f x) := by
    funext x
    by_cases hx : x ∈ locCube d h <;> simp [locWeight, hx]
  rw [hfun, integral_indicator (isClosed_locCube d h).measurableSet]
  unfold uniformLaw locLaw
  rw [Measure.restrict_restrict (isClosed_locCube d h).measurableSet,
    Set.inter_eq_left.mpr hsub, integral_const_mul, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hh.le _)]
  rfl

/-- A bounded function on the localization box has a globally bounded weighted extension.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input f](hyp:f), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hf](hyp:hf), [the specified input x](hyp:x), [the loc weight mul norm bound conclusion](goal) holds. -/
lemma locWeight_mul_norm_bound {d : ℕ} (h : ℝ) (hh : 0 < h)
    (f : Cov d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ x ∈ locCube d h, ‖f x‖ ≤ B) (x : Cov d) :
    ‖locWeight h x * f x‖ ≤ h^(-(d:ℝ)) * B := by
  by_cases hx : x ∈ locCube d h
  · rw [locWeight, if_pos hx, norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hh _)]
    exact mul_le_mul_of_nonneg_left (hf x hx) (Real.rpow_pos_of_pos hh _).le
  · simp only [locWeight, if_neg hx, zero_mul, norm_zero]
    positivity

/-- A localized treatment moment uses the designated admissible version,
even when the raw primitive carrier stores different conditional versions.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the designated local treatment moment conclusion](goal) holds. -/
lemma designated_local_treatment_moment {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (f : Cov d → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ x ∈ locCube d h, ‖f x‖ ≤ B) :
    (∫ w, locWeight h w.1 * f w.1 * bit w.2 ∂xaLaw P) =
      ∫ x, f x * designatedPropensity P hP x ∂locLaw d h := by
  have hs := canonicalLaw_spec P hP
  have hxa : xaLaw P = xaLaw (canonicalLaw P hP) := by
    unfold xaLaw
    rw [hs.1]
  rw [hxa, xaLaw_treatment_moment _ hs.2.1 hs.2.2.2.1 _
    (by fun_prop) _ (locWeight_mul_norm_bound h hh f B hB hfB)]
  simp_rw [mul_assoc]
  rw [uniformLaw_localization_integral d h hh hh']
  unfold locLaw
  apply integral_congr_ae
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem (isClosed_locCube d h).measurableSet] with x hx
  have hcube : x ∈ cube d := by
    intro i
    constructor <;> linarith [(hx i).1, (hx i).2]
  simp only [designatedPropensity, if_pos hcube]

/-- The independent randomizer has unit mass.  [the population randomizer probability conclusion](goal) holds. -/
lemma population_randomizer_probability :
    IsProbabilityMeasure (volume.restrict (Icc (0:ℝ) 1)) := by
  constructor
  simp [Real.volume_Icc]

/-- The original-record experiment is a probability measure.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input n](hyp:n), [the specified input m](hyp:m), [the population experiment probability conclusion](goal) holds. -/
lemma population_experiment_probability {d : ℕ} (P : PrimitiveLaw d) (n m : ℕ) :
    IsProbabilityMeasure (experiment P n m) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  unfold experiment
  infer_instance

/-- Dataset-only statistics integrate out the independent public randomizer.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input F](hyp:F), [the experiment integral dataset conclusion](goal) holds. -/
lemma experiment_integral_dataset {d n m : ℕ} (P : PrimitiveLaw d)
    (F : Dataset d n m → ℝ) :
    (∫ w : Sample d n m, F w.1 ∂experiment P n m) =
      ∫ D, F D ∂(Measure.pi (fun _ : Fin n => obsLaw P)).prod
        (Measure.pi (fun _ : Fin m => xaLaw P)) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  exact (integral_fun_fst F).trans (by simp)

/-- An outcome-discarded labeled record has the treatment-record marginal.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input j](hyp:j), [the experiment labeled treatment integral conclusion](goal) holds. -/
lemma experiment_labeled_treatment_integral {d n m : ℕ} (P : PrimitiveLaw d)
    (f : Cov d × Bool → ℝ) (hf : Measurable f) (j : Fin n) :
    (∫ w : Sample d n m, f ((w.1.1 j).1, (w.1.1 j).2.1) ∂experiment P n m) =
      ∫ z, f z ∂xaLaw P := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  rw [experiment_integral_dataset P (fun D : Dataset d n m => f ((D.1 j).1, (D.1 j).2.1))]
  rw [integral_fun_fst (fun D : Fin n → Cov d × Bool × Bool =>
    f ((D j).1, (D j).2.1))]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [integral_comp_eval (μ := fun _ : Fin n => obsLaw P) (i := j) (f := fun z : Cov d × Bool × Bool => f (z.1,z.2.1)) ((hf.comp (by fun_prop)).aestronglyMeasurable)]
  rw [← obsLaw_map_treatment P, integral_map (by fun_prop) hf.aestronglyMeasurable]

/-- Different labeled records give a product of treatment-record expectations.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hij](hyp:hij), [the experiment distinct labeled treatment integral conclusion](goal) holds. -/
lemma experiment_distinct_labeled_treatment_integral {d n m : ℕ} (P : PrimitiveLaw d)
    (f g : Cov d × Bool → ℝ) (hf : Measurable f) (hg : Measurable g)
    (i j : Fin n) (hij : i ≠ j) :
    (∫ w : Sample d n m, f ((w.1.1 i).1, (w.1.1 i).2.1) *
      g ((w.1.1 j).1, (w.1.1 j).2.1) ∂experiment P n m) =
      (∫ z, f z ∂xaLaw P) * (∫ z, g z ∂xaLaw P) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  rw [experiment_integral_dataset P (fun D : Dataset d n m => f ((D.1 i).1, (D.1 i).2.1) * g ((D.1 j).1, (D.1 j).2.1))]
  rw [integral_fun_fst (fun D : Fin n → Cov d × Bool × Bool =>
    f ((D i).1, (D i).2.1) * g ((D j).1, (D j).2.1))]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  have hi := (iIndepFun_pi (μ := fun _ : Fin n => obsLaw P)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have hfg := hi.comp (φ := fun z : Cov d × Bool × Bool => f (z.1,z.2.1))
    (ψ := fun z : Cov d × Bool × Bool => g (z.1,z.2.1))
    (by fun_prop) (by fun_prop)
  have hprod : (∫ D : Fin n → Cov d × Bool × Bool,
      f ((D i).1, (D i).2.1) * g ((D j).1, (D j).2.1) ∂Measure.pi (fun _ => obsLaw P)) =
      (∫ D, f ((D i).1, (D i).2.1) ∂Measure.pi (fun _ : Fin n => obsLaw P)) *
      (∫ D, g ((D j).1, (D j).2.1) ∂Measure.pi (fun _ : Fin n => obsLaw P)) := by
    simpa only [Function.comp_def, id_eq, Pi.mul_apply] using
      hfg.integral_mul_eq_mul_integral ((hf.comp (by fun_prop)).aestronglyMeasurable)
        ((hg.comp (by fun_prop)).aestronglyMeasurable)
  rw [hprod]
  rw [integral_comp_eval (μ := fun _ : Fin n => obsLaw P) (i := i) (f := fun z : Cov d × Bool × Bool => f (z.1,z.2.1)) ((hf.comp (by fun_prop)).aestronglyMeasurable),
    integral_comp_eval (μ := fun _ : Fin n => obsLaw P) (i := j) (f := fun z : Cov d × Bool × Bool => g (z.1,z.2.1)) ((hg.comp (by fun_prop)).aestronglyMeasurable)]
  rw [← obsLaw_map_treatment P]
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_map (by fun_prop) hg.aestronglyMeasurable]

/-- A treatment-role record and an outcome-role record have independent
expectations, including treatment records from the auxiliary block.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hi](hyp:hi), [the specified input hj](hyp:hj), [the experiment role product integral conclusion](goal) holds. -/
lemma experiment_role_product_integral {d n m : ℕ} (P : PrimitiveLaw d)
    (f g : Cov d × Bool → ℝ) (hf : Measurable f) (hg : Measurable g)
    (i : Fin (n+m)) (j : Fin n)
    (hi : i ∈ (roleSplit n m).2) (hj : j ∈ (roleSplit n m).1) :
    (∫ w : Sample d n m, f (treatmentRecords w.1 i) *
      g ((w.1.1 j).1, (w.1.1 j).2.1) ∂experiment P n m) =
      (∫ z, f z ∂xaLaw P) * (∫ z, g z ∂xaLaw P) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  revert hi
  refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) i
  · simp only [treatmentRecords, Fin.addCases_left]
    change (∫ w : Sample d n m, f ((w.1.1 i).1, (w.1.1 i).2.1) *
      g ((w.1.1 j).1, (w.1.1 j).2.1) ∂experiment P n m) = _
    apply experiment_distinct_labeled_treatment_integral P f g hf hg i j
    have hit : n/2 ≤ i.val := (Finset.mem_filter.mp hi).2
    have hjt : j.val < n/2 := (Finset.mem_filter.mp hj).2
    intro heq
    have := congrArg Fin.val heq
    omega
  · simp only [treatmentRecords, Fin.addCases_right]
    change (∫ w : Sample d n m, f (w.1.2 i) *
      g ((w.1.1 j).1, (w.1.1 j).2.1) ∂experiment P n m) = _
    rw [experiment_integral_dataset P (fun D : Dataset d n m => f (D.2 i) * g ((D.1 j).1, (D.1 j).2.1))]
    simp_rw [mul_comm (f _)]
    rw [integral_prod_mul (fun D : Fin n → Cov d × Bool × Bool => g ((D j).1, (D j).2.1)) (fun D : Fin m → Cov d × Bool => f (D i)), integral_comp_eval (μ := fun _ : Fin n => obsLaw P) (i := j) (f := fun z : Cov d × Bool × Bool => g (z.1,z.2.1)) ((hg.comp (by fun_prop)).aestronglyMeasurable), integral_comp_eval (μ := fun _ : Fin m => xaLaw P) (i := i) (f := f) hf.aestronglyMeasurable]
    rw [← obsLaw_map_treatment P,
      integral_map (by fun_prop) hg.aestronglyMeasurable]
    ring

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
