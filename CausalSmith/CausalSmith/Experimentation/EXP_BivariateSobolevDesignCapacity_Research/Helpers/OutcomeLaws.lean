module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.HTTransfer
public import Mathlib.Probability.Kernel.Disintegration.Unique

/-! # Single-unit outcome laws

Concrete Gaussian completions and the finite-support witness used by the published
class bridge, with their probability and conditional-prognosis properties.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The single-unit Gaussian completion map. -/
def gaussianOutcomeMap {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d)
    (ω : Cube d × ℝ × ℝ) : Cube d × ℝ × ℝ :=
  (ω.1, m.val ω.1 - tauFn hd ω.1 / 2 + ω.2.1,
    m.val ω.1 + tauFn hd ω.1 / 2 + ω.2.2)
/-- The single-unit Gaussian completion measure. -/
def gaussianOutcomeMeasure {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    Measure (Cube d × ℝ × ℝ) :=
  ((cubeMeasure d).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))).map
    (gaussianOutcomeMap hd m)
/-- The uniform cube sampling measure has total mass one.](goal) This uses [the stated conclusion](goal). -/
-- @node: cubeMeasure_probability
lemma cubeMeasure_probability (d : ℕ) : IsProbabilityMeasure (cubeMeasure d) := by
  let : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  unfold cubeMeasure
  infer_instance

/-- The concrete Gaussian completion has total mass one. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: gaussianOutcomeMeasure_probability
lemma gaussianOutcomeMeasure_probability {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    IsProbabilityMeasure (gaussianOutcomeMeasure hd m) := by
  let := cubeMeasure_probability d
  have hm : Measurable m.val := m.property.1
  have hmap : Measurable (gaussianOutcomeMap hd m) := by
    unfold gaussianOutcomeMap tauFn
    fun_prop
  exact Measure.isProbabilityMeasure_map hmap.aemeasurable
/-- The Gaussian single-unit completion as a probability law. -/
def gaussianOutcomeLaw {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) : OutcomeLaw d :=
  ⟨gaussianOutcomeMeasure hd m, gaussianOutcomeMeasure_probability hd m⟩
/-- Image of the stated Gaussian completion over legal prognostic functions. -/
def gaussianLawClass (d : ℕ) (hd : 0 < d) (s : ℝ) : Set (OutcomeLaw d) :=
  {P | ∃ m : CenteredL2Fn d, SobolevClass d s m ∧ P = gaussianOutcomeLaw hd m}
/-- Two equal ±1 potential outcomes, independent of the uniform covariate. -/
def twoPointOutcomeMeasure (d : ℕ) : Measure (Cube d × ℝ × ℝ) :=
  ((cubeMeasure d).prod ((PMF.uniformOfFintype Bool).toMeasure)).map
    (fun ω => (ω.1, sgn ω.2, sgn ω.2))
/-- The explicit two-point witness has total mass one. [The asserted mathematical result follows](goal). -/
-- @node: twoPointOutcomeMeasure_probability
lemma twoPointOutcomeMeasure_probability (d : ℕ) :
    IsProbabilityMeasure (twoPointOutcomeMeasure d) := by
  let := cubeMeasure_probability d
  have hmap : Measurable (fun ω : Cube d × Bool => (ω.1, sgn ω.2, sgn ω.2)) := by
    fun_prop
  exact Measure.isProbabilityMeasure_map hmap.aemeasurable
/-- The explicit non-Gaussian completion witness. -/
def twoPointOutcomeLaw (d : ℕ) : OutcomeLaw d :=
  ⟨twoPointOutcomeMeasure d, twoPointOutcomeMeasure_probability d⟩

/-- The Gaussian outcome map is Borel for every legal representative. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
@[fun_prop]
-- @node: gaussianOutcomeMap_measurable
lemma gaussianOutcomeMap_measurable {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    Measurable (gaussianOutcomeMap hd m) := by
  have hm : Measurable m.val := m.property.1
  unfold gaussianOutcomeMap tauFn
  fun_prop

/-- The completion preserves the uniform covariate marginal. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: gaussianOutcomeLaw_covMarginal
lemma gaussianOutcomeLaw_covMarginal {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    covMarginal (gaussianOutcomeLaw hd m) = cubeMeasure d := by
  let := cubeMeasure_probability d
  change (gaussianOutcomeMeasure hd m).map Prod.fst = _
  rw [gaussianOutcomeMeasure, Measure.map_map measurable_fst
    (gaussianOutcomeMap_measurable hd m)]
  change (((cubeMeasure d).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))).map
    Prod.fst) = _
  simp

/-- [ Both completed potential outcomes have finite second moments.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: gaussianOutcomeLaw_finiteMoments
lemma gaussianOutcomeLaw_finiteMoments {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    FiniteOutcomeMoments (gaussianOutcomeLaw hd m) := by
  let := cubeMeasure_probability d
  have hm := m.property.2.1.comp_fst ((gaussianReal 0 1).prod (gaussianReal 0 1))
  have ht := (tauFn_memLp hd).comp_fst ((gaussianReal 0 1).prod (gaussianReal 0 1))
  have hg : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have he0 := (hg.comp_fst (gaussianReal 0 1)).comp_snd
    (cubeMeasure d)
  have he1 := (hg.comp_snd (gaussianReal 0 1)).comp_snd
    (cubeMeasure d)
  constructor
  · change MemLp (fun ω : Cube d × ℝ × ℝ => ω.2.1) 2
      (Measure.map (gaussianOutcomeMap hd m) _)
    rw [memLp_map_measure_iff (by fun_prop) (gaussianOutcomeMap_measurable hd m).aemeasurable]
    convert (hm.sub (ht.mul_const (2 : ℝ)⁻¹)).add he0 using 1
    · simp [Function.comp_def, gaussianOutcomeMap, div_eq_mul_inv]
      rfl
  · change MemLp (fun ω : Cube d × ℝ × ℝ => ω.2.2) 2
      (Measure.map (gaussianOutcomeMap hd m) _)
    rw [memLp_map_measure_iff (by fun_prop) (gaussianOutcomeMap_measurable hd m).aemeasurable]
    convert (hm.add (ht.mul_const (2 : ℝ)⁻¹)).add he1 using 1
    · simp [Function.comp_def, gaussianOutcomeMap, div_eq_mul_inv]
      rfl

/-- [ The conditional Gaussian outcome distribution draws two independent unit noises. -/
-- @node: gaussianUnitKernel
def gaussianUnitKernel {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    Kernel (Cube d) (ℝ × ℝ) :=
  ⟨fun x => ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun e => (gaussianOutcomeMap hd m (x, e)).2), by
    have hj : Measurable (fun ω : Cube d × ℝ × ℝ => (gaussianOutcomeMap hd m ω).2) := by
      exact (gaussianOutcomeMap_measurable hd m).snd
    have h := (Measure.measurable_map _ hj).comp
      (Measurable.map_prodMk_left (ν := (gaussianReal 0 1).prod (gaussianReal 0 1))
        (α := Cube d))
    simpa only [Function.comp_def, Measure.map_map hj measurable_prodMk_left] using h⟩

/-- The explicit conditional outcome distribution is a Markov kernel. -/
-- @node: gaussianUnitKernel_markov
instance gaussianUnitKernel_markov {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    IsMarkovKernel (gaussianUnitKernel hd m) := by
  constructor
  intro x
  have hm : Measurable m.val := m.property.1
  change IsProbabilityMeasure (Measure.map (fun e => (gaussianOutcomeMap hd m (x, e)).2) _)
  exact Measure.isProbabilityMeasure_map
    (((gaussianOutcomeMap_measurable hd m).comp measurable_prodMk_left).snd.aemeasurable)

/-- Disintegrating the completion recovers the explicit conditional Gaussian kernel.](goal) Under [the stated conditions](hyp:hd). This uses [the stated conclusion](goal). -/
-- @node: gaussianOutcomeMeasure_disintegration
lemma gaussianOutcomeMeasure_disintegration {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    gaussianOutcomeMeasure hd m = cubeMeasure d ⊗ₘ gaussianUnitKernel hd m := by
  let := cubeMeasure_probability d
  have hm : Measurable m.val := m.property.1
  ext s hs
  rw [gaussianOutcomeMeasure, Measure.map_apply (gaussianOutcomeMap_measurable hd m) hs,
    Measure.prod_apply ((gaussianOutcomeMap_measurable hd m) hs), Measure.compProd_apply hs]
  congr 1
  funext x
  change _ = Measure.map (fun e => (gaussianOutcomeMap hd m (x, e)).2) _ _
  have hf : Measurable (fun e : ℝ × ℝ => (gaussianOutcomeMap hd m (x, e)).2) :=
    ((gaussianOutcomeMap_measurable hd m).comp (measurable_prodMk_left (x := x))).snd
  rw [Measure.map_apply hf (measurable_prodMk_left hs)]
  rfl

/-- [ Mean-zero independent Gaussian errors leave the conditional midpoint equal to m.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: gaussianUnitKernel_prognosis
lemma gaussianUnitKernel_prognosis {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d)
    (x : Cube d) :
    (∫ y, (y.2 + y.1) / 2 ∂gaussianUnitKernel hd m x) = m.val x := by
  have hm : Measurable m.val := m.property.1
  have he0 : Integrable (fun e : ℝ × ℝ => e.1)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).comp_fst _
  have he1 : Integrable (fun e : ℝ × ℝ => e.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).comp_snd _
  change (∫ y, (y.2 + y.1) / 2 ∂Measure.map
    (fun e => (gaussianOutcomeMap hd m (x, e)).2) _) = _
  have hfmap : Measurable (fun e : ℝ × ℝ => (gaussianOutcomeMap hd m (x, e)).2) :=
    ((gaussianOutcomeMap_measurable hd m).comp (measurable_prodMk_left (x := x))).snd
  rw [integral_map hfmap.aemeasurable (by fun_prop)]
  have hid (e : ℝ × ℝ) :
      ((gaussianOutcomeMap hd m (x, e)).2.2 + (gaussianOutcomeMap hd m (x, e)).2.1) / 2 =
        m.val x + (e.2 + e.1) / 2 := by
    simp only [gaussianOutcomeMap]
    ring
  simp_rw [hid]
  have he : Integrable (fun e : ℝ × ℝ => (e.2 + e.1) / 2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa only [Pi.add_apply] using (he1.add he0).div_const 2
  rw [integral_add (integrable_const _) he, integral_div, integral_add he1 he0,
    integral_const]
  have hf := integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (id : ℝ → ℝ)
  have hs := integral_fun_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (id : ℝ → ℝ)
  simp only [id_eq, integral_id_gaussianReal, smul_zero] at hf hs
  simp [hf, hs]

/-- [ The law's pinned conditional prognosis agrees almost everywhere with its input.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: gaussianOutcomeLaw_prognosis
lemma gaussianOutcomeLaw_prognosis {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    prognosisOf (gaussianOutcomeLaw hd m) =ᵐ[cubeMeasure d] m.val := by
  let := cubeMeasure_probability d
  let := gaussianOutcomeMeasure_probability hd m
  have hk := condKernel_compProd (cubeMeasure d) (gaussianUnitKernel hd m)
  have hk' : (gaussianOutcomeMeasure hd m).condKernel =ᵐ[cubeMeasure d]
      gaussianUnitKernel hd m := by
    simpa only [← gaussianOutcomeMeasure_disintegration hd m] using hk
  filter_upwards [hk'] with x hx
  change (∫ y, (y.2 + y.1) / 2 ∂(gaussianOutcomeMeasure hd m).condKernel x) = _
  rw [hx]
  exact gaussianUnitKernel_prognosis hd m x

/-- [ Uniform zero-intercept correctly specified published laws. -/
def frozenUniformClass (d : ℕ) (s : ℝ) : Set (OutcomeLaw d) :=
  {P | covMarginal P = cubeMeasure d ∧ FiniteOutcomeMoments P ∧
    ∃ m : CenteredL2Fn d, SobolevClass d s m ∧ prognosisOf P =ᵐ[cubeMeasure d] m.val}
  -- @realizes Q_s(uniform laws with arbitrary square-integrable outcomes and pinned H prognosis)
/-- The complete prognostic image, saturated under Lebesgue null representatives. -/
def publishedPrognosticImage (d : ℕ) (s : ℝ) : Set (Cube d → ℝ) :=
  {f | ∃ P ∈ frozenUniformClass d s, f =ᵐ[cubeMeasure d] prognosisOf P}
/-- The outcome class image, saturated under Lebesgue null representatives. -/
def sobolevImage (d : ℕ) (s : ℝ) : Set (Cube d → ℝ) :=
  {f | ∃ m : CenteredL2Fn d, SobolevClass d s m ∧ f =ᵐ[cubeMeasure d] m.val}

/-- Gaussian completions belong to the published uniform class with their chosen prognosis.](goal) Under [the stated conditions](hyp:hd,hm). This uses [the stated conclusion](goal). -/
-- @node: gaussianOutcomeLaw_mem_frozenUniformClass
lemma gaussianOutcomeLaw_mem_frozenUniformClass {d : ℕ} (hd : 0 < d) {s : ℝ}
    (m : CenteredL2Fn d) (hm : SobolevClass d s m) :
    gaussianOutcomeLaw hd m ∈ frozenUniformClass d s :=
  ⟨gaussianOutcomeLaw_covMarginal hd m, gaussianOutcomeLaw_finiteMoments hd m,
    m, hm, gaussianOutcomeLaw_prognosis hd m⟩

/-- [ The Gaussian family is contained in the arbitrary finite-second-moment uniform class.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: gaussianLawClass_subset_frozenUniformClass
lemma gaussianLawClass_subset_frozenUniformClass {d : ℕ} (hd : 0 < d) (s : ℝ) :
    gaussianLawClass d hd s ⊆ frozenUniformClass d s := by
  rintro P ⟨m, hm, rfl⟩
  exact gaussianOutcomeLaw_mem_frozenUniformClass hd m hm

/-- [ The prognostic image is exactly the Sobolev class modulo cube-null changes;
every reverse inclusion is witnessed by the prescribed Gaussian completion.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: publishedPrognosticImage_eq_sobolevImage
lemma publishedPrognosticImage_eq_sobolevImage (d : ℕ) (hd : 0 < d) (s : ℝ) :
    publishedPrognosticImage d s = sobolevImage d s := by
  ext f
  constructor
  · rintro ⟨P, hP, hf⟩
    obtain ⟨hU, hmom, m, hm, heq⟩ := hP
    exact ⟨m, hm, hf.trans heq⟩
  · rintro ⟨m, hm, hf⟩
    exact ⟨gaussianOutcomeLaw hd m, gaussianOutcomeLaw_mem_frozenUniformClass hd m hm,
      hf.trans (gaussianOutcomeLaw_prognosis hd m).symm⟩

/-- [ The zero function has zero restriction Sobolev energy, witnessed by its zero extension. -/
lemma sobolevNormSq_zero (p : ℕ) (s : ℝ) :
    sobolevNormSq p s (fun _ => 0) = 0 := by
  apply le_antisymm _ zero_le
  unfold sobolevNormSq
  refine iInf_le_of_le (fun _ => 0) (iInf_le_of_le ?_ ?_)
  · exact ⟨integrable_zero _ _ _, MemLp.zero', Filter.EventuallyEq.rfl⟩
  · simp [Fourier]

/-- Zero prognosis has the exact order-two representation and zero pooled budget.](goal) Under [the stated conditions](hyp:hm). This uses [the stated conclusion](goal). -/
-- @node: sobolevClass_zero
lemma sobolevClass_zero (d : ℕ) (s : ℝ)
    (hm : Measurable (fun _ : Cube d => (0 : ℝ)) ∧
      MemLp (fun _ : Cube d => (0 : ℝ)) 2 (cubeMeasure d) ∧
      (∫ _ : Cube d, (0 : ℝ) ∂cubeMeasure d) = 0) :
    SobolevClass d s ⟨fun _ => 0, hm⟩ := by
  have hg1 (j : Fin d) (u : ℝ) : g1 (fun _ : Cube d => 0) j u = 0 := by simp [g1]
  have hg2 (j l : Fin d) (u v : ℝ) : g2 (fun _ : Cube d => 0) j l u v = 0 := by
    simp [g2, hg1]
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    simp [hg1, hg2]
  · simp [PooledBudget, hg1, hg2, sobolevNormSq_zero]

/-- The two-point law is a product of uniform covariates and one fair diagonal sign. [The asserted mathematical result follows](goal). -/
-- @node: twoPointOutcomeMeasure_product
lemma twoPointOutcomeMeasure_product (d : ℕ) :
    twoPointOutcomeMeasure d = (cubeMeasure d).prod
      (((PMF.uniformOfFintype Bool).toMeasure).map (fun b => (sgn b, sgn b))) := by
  let := cubeMeasure_probability d
  rw [← Measure.map_id (μ := cubeMeasure d), Measure.map_prod_map _ _ measurable_id (by fun_prop)]
  rfl

/-- [ The two-point witness retains uniform covariates.](goal) -/
-- @node: twoPointOutcomeLaw_covMarginal
lemma twoPointOutcomeLaw_covMarginal (d : ℕ) :
    covMarginal (twoPointOutcomeLaw d) = cubeMeasure d := by
  let := cubeMeasure_probability d
  let : IsProbabilityMeasure (((PMF.uniformOfFintype Bool).toMeasure).map
      (fun b => (sgn b, sgn b))) := Measure.isProbabilityMeasure_map (by fun_prop)
  change (twoPointOutcomeMeasure d).fst = _
  rw [twoPointOutcomeMeasure_product]
  simp

/-- [ Bounded two-point outcomes have finite second moments.](goal) -/
-- @node: twoPointOutcomeLaw_finiteMoments
lemma twoPointOutcomeLaw_finiteMoments (d : ℕ) :
    FiniteOutcomeMoments (twoPointOutcomeLaw d) := by
  let := cubeMeasure_probability d
  have hb : MemLp sgn 2 (PMF.uniformOfFintype Bool).toMeasure := by
    apply (memLp_const (1 : ℝ)).mono (by fun_prop)
    filter_upwards with b
    cases b <;> simp [sgn]
  have hp := hb.comp_snd (cubeMeasure d)
  constructor <;>
    change MemLp _ 2 (Measure.map (fun ω : Cube d × Bool => (ω.1, sgn ω.2, sgn ω.2)) _)
  all_goals
    rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
    exact hp

/-- [ The fair diagonal sign has zero conditional midpoint expectation.](goal) -/
-- @node: twoPointOutcomeLaw_prognosis
lemma twoPointOutcomeLaw_prognosis (d : ℕ) :
    prognosisOf (twoPointOutcomeLaw d) =ᵐ[cubeMeasure d] fun _ => 0 := by
  let := cubeMeasure_probability d
  let := twoPointOutcomeMeasure_probability d
  let ν := ((PMF.uniformOfFintype Bool).toMeasure).map (fun b => (sgn b, sgn b))
  let : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hprod : twoPointOutcomeMeasure d = cubeMeasure d ⊗ₘ Kernel.const (Cube d) ν := by
    rw [Measure.compProd_const]
    exact twoPointOutcomeMeasure_product d
  have hk : (twoPointOutcomeMeasure d).condKernel =ᵐ[cubeMeasure d] Kernel.const (Cube d) ν := by
    simpa only [← hprod] using condKernel_compProd (cubeMeasure d) (Kernel.const (Cube d) ν)
  filter_upwards [hk] with x hx
  change (∫ y, (y.2 + y.1) / 2 ∂(twoPointOutcomeMeasure d).condKernel x) = 0
  rw [hx]
  change (∫ y, (y.2 + y.1) / 2 ∂Measure.map (fun b => (sgn b, sgn b)) _) = 0
  rw [integral_map (by fun_prop) (by fun_prop)]
  have heq (b : Bool) : (sgn b + sgn b) / 2 = sgn b := by ring
  simp_rw [heq]
  rw [integral_fintype (Integrable.of_finite)]
  simp [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, sgn]

/-- [ The finite-support witness is legal in every uniform Sobolev law class.](goal) -/
-- @node: twoPointOutcomeLaw_mem_frozenUniformClass
lemma twoPointOutcomeLaw_mem_frozenUniformClass (d : ℕ) (s : ℝ) :
    twoPointOutcomeLaw d ∈ frozenUniformClass d s := by
  have hm : Measurable (fun _ : Cube d => (0 : ℝ)) ∧
      MemLp (fun _ : Cube d => (0 : ℝ)) 2 (cubeMeasure d) ∧
      (∫ _ : Cube d, (0 : ℝ) ∂cubeMeasure d) = 0 :=
    ⟨measurable_const, MemLp.zero', by simp⟩
  exact ⟨twoPointOutcomeLaw_covMarginal d, twoPointOutcomeLaw_finiteMoments d,
    ⟨fun _ => 0, hm⟩, sobolevClass_zero d s hm, twoPointOutcomeLaw_prognosis d⟩

/-- [ Equal two-point potential outcomes lie on the diagonal with probability one.](goal) -/
-- @node: twoPointOutcomeMeasure_diagonal
lemma twoPointOutcomeMeasure_diagonal (d : ℕ) :
    twoPointOutcomeMeasure d {ω | ω.2.1 = ω.2.2} = 1 := by
  let := cubeMeasure_probability d
  rw [twoPointOutcomeMeasure, Measure.map_apply (by fun_prop)
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))]
  simp

/-- Independent continuous Gaussian errors give the outcome diagonal probability zero. Under [the stated conditions](hyp:hd), [the asserted mathematical result follows](goal). -/
-- @node: gaussianOutcomeMeasure_diagonal
lemma gaussianOutcomeMeasure_diagonal {d : ℕ} (hd : 0 < d) (m : CenteredL2Fn d) :
    gaussianOutcomeMeasure hd m {ω | ω.2.1 = ω.2.2} = 0 := by
  let := cubeMeasure_probability d
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  rw [gaussianOutcomeMeasure, Measure.map_apply (gaussianOutcomeMap_measurable hd m)
    (measurableSet_eq_fun (by fun_prop) (by fun_prop)),
    Measure.prod_apply ((gaussianOutcomeMap_measurable hd m)
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)))]
  have hz (x : Cube d) : ((gaussianReal 0 1).prod (gaussianReal 0 1))
      {e | m.val x - tauFn hd x / 2 + e.1 = m.val x + tauFn hd x / 2 + e.2} = 0 := by
    rw [Measure.prod_apply (measurableSet_eq_fun (by fun_prop) (by fun_prop))]
    have hs (a : ℝ) : {b : ℝ | m.val x - tauFn hd x / 2 + a =
        m.val x + tauFn hd x / 2 + b} = {a - tauFn hd x} := by
      ext b
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor <;> intro h <;> linarith
    simp only [show ∀ a : ℝ, Prod.mk a ⁻¹' {e : ℝ × ℝ |
        m.val x - tauFn hd x / 2 + e.1 = m.val x + tauFn hd x / 2 + e.2} =
        {a - tauFn hd x} from hs, measure_singleton, lintegral_zero]
  change (∫⁻ x, ((gaussianReal 0 1).prod (gaussianReal 0 1))
    {e | m.val x - tauFn hd x / 2 + e.1 = m.val x + tauFn hd x / 2 + e.2}
      ∂cubeMeasure d) = 0
  simp_rw [hz]
  exact lintegral_zero

/-- [ A law supported on equal two-point outcomes cannot be a Gaussian completion.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: twoPointOutcomeLaw_not_mem_gaussianLawClass
lemma twoPointOutcomeLaw_not_mem_gaussianLawClass {d : ℕ} (hd : 0 < d) (s : ℝ) :
    twoPointOutcomeLaw d ∉ gaussianLawClass d hd s := by
  rintro ⟨m, hm, heq⟩
  have hmeasure : twoPointOutcomeMeasure d = gaussianOutcomeMeasure hd m :=
    congrArg ProbabilityMeasure.toMeasure heq
  have hdiag := twoPointOutcomeMeasure_diagonal d
  rw [hmeasure, gaussianOutcomeMeasure_diagonal hd m] at hdiag
  exact zero_ne_one hdiag

/-- [ The Gaussian inclusion is strict, witnessed by the legal diagonal two-point law.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: gaussianLawClass_ssubset_frozenUniformClass
lemma gaussianLawClass_ssubset_frozenUniformClass {d : ℕ} (hd : 0 < d) (s : ℝ) :
    gaussianLawClass d hd s ⊂ frozenUniformClass d s := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨gaussianLawClass_subset_frozenUniformClass hd s, ?_⟩
  intro heq
  have hmem := twoPointOutcomeLaw_mem_frozenUniformClass d s
  rw [← heq] at hmem
  exact twoPointOutcomeLaw_not_mem_gaussianLawClass hd s hmem

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
