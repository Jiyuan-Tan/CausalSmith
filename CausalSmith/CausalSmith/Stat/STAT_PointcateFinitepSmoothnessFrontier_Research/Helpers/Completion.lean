module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Basic
public import Causalean.Tactic.CondexpLinearity
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-! Finite-moment point-CATE frontier: Helpers/Completion. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- The propensity-indexed Bernoulli conditional measure. -/
def bernMeasure (e : unitInterval → ℝ) (x : unitInterval) : Measure Bool :=
  ENNReal.ofReal (e x) • Measure.dirac true + ENNReal.ofReal (1-e x) • Measure.dirac false
/-- The propensity-indexed Bernoulli measures form a measurable family. -/
-- @node: measurable_bernMeasure
@[fun_prop] lemma measurable_bernMeasure (e : unitInterval → ℝ) (he : Measurable e) :
    Measurable (bernMeasure e) := by
  unfold bernMeasure
  fun_prop
/-- The Bernoulli kernel for assignment. -/
def bernKernel (law : ObservedLaw) : Kernel unitInterval Bool :=
  ⟨bernMeasure law.e, measurable_bernMeasure law.e law.e_measurable⟩
/-- Full records retain both real potential outcomes. -/
abbrev CausalRecord := unitInterval × Bool × ℝ × ℝ
-- @node: def:completion
/-- Independent arm draws and independent assignment conditional on the uniform covariate. -/
def causalCompletion (law : ObservedLaw) : Measure CausalRecord :=
  design ⊗ₘ ((bernKernel law).prod ((law.Q false).prod (law.Q true))) -- @realizes completion(canonical conditionally independent completion)
/-- Covariate coordinate in the completion. -/
def completionX (r : CausalRecord) : unitInterval := r.1
/-- Treatment coordinate in the completion. -/
def completionA (r : CausalRecord) : Bool := r.2.1
/-- Control potential outcome in the completion. -/
def Y0 (r : CausalRecord) : ℝ := r.2.2.1 -- @realizes Y0(control potential-outcome coordinate)
/-- Treated potential outcome in the completion. -/
def Y1 (r : CausalRecord) : ℝ := r.2.2.2 -- @realizes Y1(treated potential-outcome coordinate)
/-- Factual response is the potential response selected by assignment. -/
def observedY (r : CausalRecord) : ℝ := if completionA r then Y1 r else Y0 r -- @realizes Y(consistency-selected response under completion)
/-- Observation retains X, A and the factual response. -/
def observe (r : CausalRecord) : O := (completionX r, completionA r, observedY r)
/-- Assignment weights define a Markov kernel. -/
-- @node: bernKernel_markov
lemma bernKernel_markov (law : ObservedLaw) : IsMarkovKernel (bernKernel law) := by
  constructor
  intro x
  constructor
  change (bernMeasure law.e x) univ = 1
  simp only [bernMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (law.e_range x).1 (sub_nonneg.mpr (law.e_range x).2)]
  simp

/-- Selecting the factual mark keeps assignment and discards the unused outcome. -/
-- @node: selectCompletionMark
def selectCompletionMark (r : Bool × ℝ × ℝ) : Bool × ℝ :=
  (r.1, if r.1 then r.2.2 else r.2.1)

/-- Factual mark selection is Borel. -/
-- @node: measurable_selectCompletionMark
@[fun_prop] lemma measurable_selectCompletionMark : Measurable selectCompletionMark := by
  unfold selectCompletionMark
  apply measurable_fst.prodMk
  apply Measurable.ite
    (measurableSet_eq_fun measurable_fst measurable_const)
    (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)

/-- At fixed assignment, selection integrates out the unused independent arm. -/
-- @node: selectCompletionMark_dirac_prod
lemma selectCompletionMark_dirac_prod (a : Bool) (μ₀ μ₁ : Measure ℝ)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] :
    ((Measure.dirac a).prod (μ₀.prod μ₁)).map selectCompletionMark =
      (Measure.dirac a).prod (if a then μ₁ else μ₀) := by
  rw [Measure.dirac_prod, Measure.map_map measurable_selectCompletionMark measurable_prodMk_left]
  cases a
  · change (μ₀.prod μ₁).map (fun r => (false, r.1)) = _
    rw [show (fun r : ℝ × ℝ => (false, r.1)) = (Prod.mk false) ∘ Prod.fst from rfl,
      ← Measure.map_map measurable_prodMk_left measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul, Measure.dirac_prod]
    rfl
  · change (μ₀.prod μ₁).map (fun r => (true, r.2)) = _
    rw [show (fun r : ℝ × ℝ => (true, r.2)) = (Prod.mk true) ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_prodMk_left measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, Measure.dirac_prod]
    rfl

/-- The completion's conditional factual marks have the original record kernel. -/
-- @node: completion_mark_kernel
lemma completion_mark_kernel (law : ObservedLaw) :
    ((bernKernel law).prod ((law.Q false).prod (law.Q true))).map selectCompletionMark =
      recordKernel law.e law.e_measurable law.Q := by
  let := bernKernel_markov law
  ext x : 1
  rw [Kernel.map_apply _ measurable_selectCompletionMark, Kernel.prod_apply,
    Kernel.prod_apply]
  change ((bernMeasure law.e x).prod ((law.Q false x).prod (law.Q true x))).map
    selectCompletionMark = recordMeasure law.e law.Q x
  rw [bernMeasure, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_add _ _ measurable_selectCompletionMark, Measure.map_smul,
    Measure.map_smul, selectCompletionMark_dirac_prod, selectCompletionMark_dirac_prod]
  rfl

/-- Uniform design and the conditional mark calculation recover the observed marginal. -/
-- @node: completion_observed_marginal
lemma completion_observed_marginal (law : ObservedLaw) (hu : UniformDesign law) :
    (causalCompletion law).map observe = law.P := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let := bernKernel_markov law
  change (design ⊗ₘ ((bernKernel law).prod ((law.Q false).prod (law.Q true)))).map
    (Prod.map id selectCompletionMark) = law.P
  rw [← Measure.compProd_map measurable_selectCompletionMark, completion_mark_kernel]
  conv_rhs => rw [law.record_version, hu]

/-- The completion is a probability measure. -/
-- @node: completion_probability
lemma completion_probability (law : ObservedLaw) : IsProbabilityMeasure (causalCompletion law) := by
  let := bernKernel_markov law
  unfold causalCompletion design
  infer_instance
/-- The explicit completion carries its probability instance. -/
instance (law : ObservedLaw) : IsProbabilityMeasure (causalCompletion law) := completion_probability law
/-- The covariate coordinate of the completion is measurable. -/
-- @node: measurable_completionX
@[fun_prop] lemma measurable_completionX : Measurable completionX := by
  exact measurable_fst

/-- Assignment and the pair of potential outcomes are conditionally independent under
 the completion, because their conditional kernel factors at every covariate. -/
-- @node: completion_exchangeability
lemma completion_exchangeability (law : ObservedLaw) :
    CondIndepFun (MeasurableSpace.comap completionX inferInstance)
      measurable_completionX.comap_le completionA (fun r => (Y0 r, Y1 r))
      (causalCompletion law) := by
  let := bernKernel_markov law
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hx : (causalCompletion law).map completionX = design := by
    exact Measure.fst_compProd design _
  have ha : Measurable completionA := by
    unfold completionA
    fun_prop
  have hy : Measurable (fun r : CausalRecord => (Y0 r, Y1 r)) := by
    unfold Y0 Y1
    fun_prop
  have hma : (causalCompletion law).map (fun r => (completionX r, completionA r)) =
      design ⊗ₘ bernKernel law := by
    change (design ⊗ₘ ((bernKernel law).prod ((law.Q false).prod (law.Q true)))).map
      (Prod.map id Prod.fst) = _
    rw [← Measure.compProd_map measurable_fst]
    rw [← Kernel.fst_eq, Kernel.fst_prod]
  have hmy : (causalCompletion law).map (fun r => (completionX r, (Y0 r, Y1 r))) =
      design ⊗ₘ ((law.Q false).prod (law.Q true)) := by
    change (design ⊗ₘ ((bernKernel law).prod ((law.Q false).prod (law.Q true)))).map
      (Prod.map id Prod.snd) = _
    rw [← Measure.compProd_map measurable_snd]
    rw [← Kernel.snd_eq, Kernel.snd_prod]
  have hca := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    measurable_completionX ha (hma.trans (by rw [hx]))
  have hcy := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    measurable_completionX hy (hmy.trans (by rw [hx]))
  apply (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    ha hy measurable_completionX).mpr
  rw [← Measure.compProd_eq_comp_prod]
  have hk :
      (condDistrib completionA completionX (causalCompletion law)).prod
        (condDistrib (fun r => (Y0 r, Y1 r)) completionX (causalCompletion law))
      =ᵐ[(causalCompletion law).map completionX]
        (bernKernel law).prod ((law.Q false).prod (law.Q true)) := by
    filter_upwards [hca, hcy] with x hax hyx
    simp only [Kernel.prod_apply, hax, hyx]
  rw [Measure.compProd_congr hk, hx]
  exact Measure.map_id

/-- Integrating an arm's absolute response is bounded by one plus its raw p-moment. -/
-- @node: arm_absolute_lintegral_bound
lemma arm_absolute_lintegral_bound (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hmodel : InModel κ law) (a : Bool) :
    ∫⁻ r : unitInterval × ℝ, ENNReal.ofReal |r.2| ∂(design ⊗ₘ law.Q a) ≤ 11 := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  rw [Measure.lintegral_compProd (by fun_prop)]
  calc
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal |y| ∂law.Q a x ∂design) ≤
        ∫⁻ x, (11 : ℝ≥0∞) ∂design := by
      apply lintegral_mono_ae
      filter_upwards [hmodel.conditionalMoment] with x hx
      calc
        (∫⁻ y, ENNReal.ofReal |y| ∂law.Q a x) ≤
            ∫⁻ y, 1 + ENNReal.ofReal (|y| ^ κ.p) ∂law.Q a x := by
          apply lintegral_mono
          intro y
          have hab : |y| ≤ 1 + |y| ^ κ.p := by
            by_cases hy : |y| ≤ 1
            · exact hy.trans (le_add_of_nonneg_right (by positivity))
            · exact (Real.self_le_rpow_of_one_le (le_of_not_ge hy) hκ.1.1.le).trans
                (le_add_of_nonneg_left (by norm_num))
          dsimp only
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
          exact ENNReal.ofReal_le_ofReal hab
        _ = 1 + ∫⁻ y, ENNReal.ofReal (|y| ^ κ.p) ∂law.Q a x := by
          rw [lintegral_add_left measurable_const]
          simp
        _ ≤ 11 := by
          have hb := add_le_add_left (hx a) (1 : ℝ≥0∞)
          norm_num only at hb
          simpa only [add_comm] using hb
    _ = 11 := by simp

/-- The uniform arm joint law has an integrable response under the model moment envelope. -/
-- @node: arm_joint_integrable
lemma arm_joint_integrable (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hmodel : InModel κ law) (a : Bool) :
    Integrable (fun r : unitInterval × ℝ => r.2) (design ⊗ₘ law.Q a) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs]
  exact (arm_absolute_lintegral_bound κ hκ law hmodel a).trans_lt (by norm_num)

/-- Marginalizing independent assignment and the unused arm gives the control joint law. -/
-- @node: completion_control_joint
lemma completion_control_joint (law : ObservedLaw) :
    (causalCompletion law).map (fun r => (completionX r, Y0 r)) =
      design ⊗ₘ law.Q false := by
  let := bernKernel_markov law
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  change (design ⊗ₘ ((bernKernel law).prod ((law.Q false).prod (law.Q true)))).map
    (Prod.map id (Prod.fst ∘ Prod.snd)) = _
  rw [← Measure.compProd_map (by fun_prop),
    Kernel.map_comp_right _ measurable_snd measurable_fst,
    ← Kernel.snd_eq, Kernel.snd_prod, ← Kernel.fst_eq, Kernel.fst_prod]

/-- Marginalizing independent assignment and the unused arm gives the treated joint law. -/
-- @node: completion_treated_joint
lemma completion_treated_joint (law : ObservedLaw) :
    (causalCompletion law).map (fun r => (completionX r, Y1 r)) =
      design ⊗ₘ law.Q true := by
  let := bernKernel_markov law
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  change (design ⊗ₘ ((bernKernel law).prod ((law.Q false).prod (law.Q true)))).map
    (Prod.map id (Prod.snd ∘ Prod.snd)) = _
  rw [← Measure.compProd_map (by fun_prop),
    Kernel.map_comp_right _ measurable_snd measurable_snd]
  simp only [← Kernel.snd_eq, Kernel.snd_prod]

/-- Both completion outcomes are integrable by the moment bound and their arm marginals. -/
-- @node: completion_outcomes_integrable
lemma completion_outcomes_integrable (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hmodel : InModel κ law) :
    Integrable Y0 (causalCompletion law) ∧ Integrable Y1 (causalCompletion law) := by
  constructor
  · have h := arm_joint_integrable κ hκ law hmodel false
    rw [← completion_control_joint law] at h
    exact h.comp_measurable (by unfold completionX Y0; fun_prop)
  · have h := arm_joint_integrable κ hκ law hmodel true
    rw [← completion_treated_joint law] at h
    exact h.comp_measurable (by unfold completionX Y1; fun_prop)

/-- An outcome with the constructed arm joint law has conditional mean equal to the arm kernel mean. -/
-- @node: completion_arm_conditional_mean
lemma completion_arm_conditional_mean (law : ObservedLaw) (a : Bool)
    (Z : CausalRecord → ℝ) (hZ : Measurable Z)
    (hjoint : (causalCompletion law).map (fun r => (completionX r, Z r)) =
      design ⊗ₘ law.Q a) (hInt : Integrable Z (causalCompletion law)) :
    (causalCompletion law)[Z | MeasurableSpace.comap completionX inferInstance]
      =ᵐ[causalCompletion law] fun r => ∫ y, y ∂law.Q a (completionX r) := by
  let := bernKernel_markov law
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hx : (causalCompletion law).map completionX = design :=
    Measure.fst_compProd design _
  have hkernel := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    measurable_completionX hZ (hjoint.trans (by rw [hx]))
  have hpull := ae_of_ae_map measurable_completionX.aemeasurable hkernel
  have hce := condExp_ae_eq_integral_condDistrib' measurable_completionX hInt
  filter_upwards [hce, hpull] with r hr hk
  rw [hr, hk]

/-- The completed potential-outcome contrast has the continuous original contrast as conditional mean. -/
-- @node: completion_contrast_conditional_mean
lemma completion_contrast_conditional_mean (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hmodel : InModel κ law) :
    (causalCompletion law)[fun r => Y1 r - Y0 r |
      MeasurableSpace.comap completionX inferInstance]
      =ᵐ[causalCompletion law] fun r => law.tau (completionX r) := by
  obtain ⟨hY0, hY1⟩ := completion_outcomes_integrable κ hκ law hmodel
  have h0 := completion_arm_conditional_mean law false Y0 (by unfold Y0; fun_prop)
    (completion_control_joint law) hY0
  have h1 := completion_arm_conditional_mean law true Y1 (by unfold Y1; fun_prop)
    (completion_treated_joint law) hY1
  have hx : (causalCompletion law).map completionX = design := by
    let := bernKernel_markov law
    let : IsProbabilityMeasure design := by unfold design; infer_instance
    exact Measure.fst_compProd design _
  have hm0 := law.mean0_version
  have hm1 := law.mean1_version
  rw [hmodel.uniform] at hm0 hm1
  rw [← hx] at hm0 hm1
  have hp0 := ae_of_ae_map measurable_completionX.aemeasurable hm0
  have hp1 := ae_of_ae_map measurable_completionX.aemeasurable hm1
  have hsub :
      (causalCompletion law)[fun r => Y1 r - Y0 r |
        MeasurableSpace.comap completionX inferInstance]
        =ᵐ[causalCompletion law] fun r =>
          (causalCompletion law)[Y1 | MeasurableSpace.comap completionX inferInstance] r -
          (causalCompletion law)[Y0 | MeasurableSpace.comap completionX inferInstance] r := by
    condexp_linearity [hY1, hY0]
  filter_upwards [hsub, h0, h1, hp0, hp1] with r hr hr0 hr1 hm0r hm1r
  rw [hr, hr1, hr0, ← hm1r, ← hm0r]
  ring

/-- The factual response satisfies consistency for every completed record. -/
-- @node: completion_consistency
lemma completion_consistency (r : CausalRecord) :
    observedY r = (if completionA r then (1 : ℝ) else 0) * Y1 r +
      (1 - (if completionA r then (1 : ℝ) else 0)) * Y0 r := by
  cases ha : completionA r <;> simp [observedY, ha]

/-- A continuous function on the unit interval is determined by its uniform almost-everywhere values. -/
-- @node: continuous_eq_of_design_ae_eq
lemma continuous_eq_of_design_ae_eq {f g : unitInterval → ℝ}
    (hf : Continuous f) (hg : Continuous g) (heq : f =ᵐ[design] g) : f = g := by
  let π : ℝ → unitInterval := Set.projIcc 0 1 (by norm_num)
  have hπ : Continuous π := continuous_projIcc
  have hmap : (volume : Measure unitInterval).map Subtype.val =
      (volume : Measure ℝ).restrict (Icc 0 1) := unitInterval.measurePreserving_coe.map_eq
  have hext : (fun x => f (π x)) =ᵐ[(volume : Measure ℝ).restrict (Icc 0 1)]
      (fun x => g (π x)) := by
    rw [← hmap]
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_eq_fun (hf.comp hπ).measurable (hg.comp hπ).measurable)).2
    filter_upwards [heq] with x hx
    simpa [π, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) x.property] using hx
  have hpoint := Measure.eqOn_Icc_of_ae_eq (μ := (volume : Measure ℝ))
    (by norm_num : (0 : ℝ) ≠ 1) hext (hf.comp hπ).continuousOn (hg.comp hπ).continuousOn
  funext x
  simpa [π, Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) x.property] using hpoint x.property

/-- The original record kernel is Markov, as follows from its completion factorization. -/
-- @node: completion_record_kernel_markov
lemma completion_record_kernel_markov (law : ObservedLaw) :
    IsMarkovKernel (recordKernel law.e law.e_measurable law.Q) := by
  let := bernKernel_markov law
  rw [← completion_mark_kernel law]
  exact Kernel.IsMarkovKernel.map _ measurable_selectCompletionMark

/-- Equal original laws have equal conditional record measures almost everywhere. -/
-- @node: original_record_kernel_identified
lemma original_record_kernel_identified (law law' : ObservedLaw)
    (hP : law'.P = law.P) :
    recordKernel law.e law.e_measurable law.Q
      =ᵐ[law.P.map X] recordKernel law'.e law'.e_measurable law'.Q := by
  let := completion_record_kernel_markov law
  let := completion_record_kernel_markov law'
  have h (l : ObservedLaw) :
      condDistrib Prod.snd X l.P =ᵐ[l.P.map X]
        recordKernel l.e l.e_measurable l.Q := by
    let := completion_record_kernel_markov l
    apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by exact measurable_fst) (by fun_prop)
    change l.P.map id = _
    rw [Measure.map_id, ← l.record_version]
  have h' := h law'
  simp only [hP] at h'
  exact (h law).symm.trans h'

/-- A singleton assignment slice of the record measure is its weighted outcome law. -/
-- @node: recordMeasure_arm_slice
lemma recordMeasure_arm_slice (law : ObservedLaw) (x : unitInterval) (a : Bool)
    (s : Set ℝ) :
    recordMeasure law.e law.Q x ({a} ×ˢ s) =
      ENNReal.ofReal (if a then law.e x else 1 - law.e x) * law.Q a x s := by
  cases a <;> simp [recordMeasure, Measure.prod_prod, Measure.dirac_apply']

/-- Overlap makes both arm weights strictly positive. -/
-- @node: original_arm_weight_pos
lemma original_arm_weight_pos (law : ObservedLaw) (ho : Overlap law)
    (x : unitInterval) (a : Bool) :
    0 < (if a then law.e x else 1 - law.e x) := by
  have hx := ho x
  cases a <;> dsimp <;> linarith

/-- Equal conditional records identify each arm measure by positive-weight cancellation. -/
-- @node: original_arm_measures_identified
lemma original_arm_measures_identified (law law' : ObservedLaw)
    (ho : Overlap law) (x : unitInterval)
    (hr : recordMeasure law.e law.Q x = recordMeasure law'.e law'.Q x) :
    ∀ a, law.Q a x = law'.Q a x := by
  intro a
  have hw := congrArg (fun μ : Measure (Bool × ℝ) => μ ({a} ×ˢ univ)) hr
  simp only [recordMeasure_arm_slice, measure_univ, mul_one] at hw
  ext s hs
  have hs' := congrArg (fun μ : Measure (Bool × ℝ) => μ ({a} ×ˢ s)) hr
  simp only [recordMeasure_arm_slice, ← hw] at hs'
  exact (ENNReal.mul_right_inj (ne_of_gt (ENNReal.ofReal_pos.mpr
    (original_arm_weight_pos law ho x a))) ENNReal.ofReal_ne_top).mp hs'

/-- Continuous contrasts are determined by the original observed law under overlap. -/
-- @node: original_contrast_identified
lemma original_contrast_identified (κ : Params) (law law' : ObservedLaw)
    (hm : InModel κ law) (hm' : InModel κ law') (hP : law'.P = law.P) :
    law'.tau = law.tau := by
  have hk := original_record_kernel_identified law law' hP
  rw [hm.uniform] at hk
  have h0 := law.mean0_version
  have h1 := law.mean1_version
  have h0' := law'.mean0_version
  have h1' := law'.mean1_version
  rw [hm.uniform] at h0 h1
  rw [hm'.uniform] at h0' h1'
  apply continuous_eq_of_design_ae_eq hm'.effectHolder.1 hm.effectHolder.1
  filter_upwards [hk, h0, h1, h0', h1'] with x hx hx0 hx1 hx0' hx1'
  have hq := original_arm_measures_identified law law' hm.overlap x hx
  rw [← hq false] at hx0'
  rw [← hq true] at hx1'
  linarith

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
