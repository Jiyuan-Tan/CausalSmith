module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Basic
public import Causalean.Mathlib.Probability.Independence.Conditional.CondExp
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.MetricSpace.Holder
/-! Continuity selects the uniquely identified point-CATE representative from the observed law. -/
public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The model's contrast modulus is an ordinary Lipschitz bound.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP). -/
-- @node: contrast_lipschitzWith
lemma contrast_lipschitzWith (P : CausalLaw) (hP : CompleteModel P) :
    LipschitzWith 3 (tau P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_ofNat, L] using
    hP.contrast_lipschitz x y

/-- The selected contrast is continuous under the complete model. The result uses [the stated assumptions](hyp:hP) and establishes [the displayed conclusion](goal). -/
-- @node: continuous_tau
@[fun_prop] lemma continuous_tau (P : CausalLaw) (hP : CompleteModel P) :
    Continuous (tau P) := by
  exact (contrast_lipschitzWith P hP).continuous

/-- The positive design density transfers design-null sets to Lebesgue-null sets. The result uses [the stated assumptions](hyp:hP) and establishes [the displayed conclusion](goal). -/
-- @node: volume_absolutelyContinuous_PX
lemma volume_absolutelyContinuous_PX (P : CausalLaw) (hP : CompleteModel P) :
    (volume : Measure Covariate) ≪ PX P := by
  rw [PX, P.density_version hP.density.1]
  apply withDensity_absolutelyContinuous'
  · exact (ENNReal.measurable_ofReal.comp P.f_measurable).aemeasurable
  · filter_upwards [hP.density.2] with x hx
    exact ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le (by norm_num) hx.1)

/-- Continuous functions on the unit interval that agree Lebesgue-almost everywhere agree
at every point, including the two boundary points.  [the theorem's stated inputs and assumptions](hyp:hv,hw,heq), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:v,w). -/
-- @node: continuous_eq_of_volume_ae_eq
lemma continuous_eq_of_volume_ae_eq {v w : Covariate → ℝ}
    (hv : Continuous v) (hw : Continuous w) (heq : v =ᵐ[volume] w) : v = w := by
  let c : ℝ → Covariate := projIcc 0 1 (by norm_num)
  have hc : Continuous c := by fun_prop
  have hae : (v ∘ c) =ᵐ[(volume : Measure ℝ).restrict (Icc 0 1)] (w ∘ c) := by
    rw [← unitInterval.measurePreserving_coe.map_eq]
    apply (ae_map_iff (by fun_prop)
      (isClosed_eq (hv.comp hc) (hw.comp hc)).measurableSet).mpr
    filter_upwards [heq] with x hx
    simpa [c, projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) x.property] using hx
  have hevery := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ)
    (by norm_num : (0 : ℝ) ≠ 1) hae (hv.comp hc).continuousOn (hw.comp hc).continuousOn
  funext x
  simpa [c, projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) x.property] using hevery x.property

/-- Positive design density makes the continuous representative of the contrast unique.  [the theorem's stated inputs and assumptions](hyp:v,hv,heq), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP). -/
-- @node: continuous_tau_unique
lemma continuous_tau_unique (P : CausalLaw) (hP : CompleteModel P)
    (v : Covariate → ℝ) (hv : Continuous v) (heq : v =ᵐ[PX P] tau P) : v = tau P := by
  exact continuous_eq_of_volume_ae_eq hv (continuous_tau P hP)
    ((volume_absolutelyContinuous_PX P hP).ae_eq heq)

/-- The treatment coordinate is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_A
@[fun_prop] lemma measurable_A : Measurable A := by unfold A; fun_prop

/-- The observed outcome coordinate is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_Y
@[fun_prop] lemma measurable_Y : Measurable Y := by unfold Y; fun_prop

/-- The numerical encoding of a Boolean mark is measurable. -/
@[fun_prop] lemma measurable_bit : Measurable bit := by
  unfold bit
  fun_prop

/-- Each treatment-arm event is measurable.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:d). -/
-- @node: arm_event_measurable
lemma arm_event_measurable (d : Bool) : MeasurableSet {z : Record | A z = d} := by
  exact measurableSet_eq_fun measurable_A measurable_const

/-- The arm-specific design measure evaluates a covariate set as its joint arm event.  [the theorem's stated inputs and assumptions](hyp:P,d,s,hs), and [the asserted conclusion follows](goal). -/
-- @node: arm_design_apply
lemma arm_design_apply (P : CausalLaw) (d : Bool) (s : Set Covariate)
    (hs : MeasurableSet s) :
    ((P.law.restrict {z | A z = d}).map X) s = P.law {z | X z ∈ s ∧ A z = d} := by
  rw [Measure.map_apply measurable_X hs, Measure.restrict_apply (measurable_X hs)]
  rfl

/-- The selected propensity and its complement integrate to the two arm probabilities.  [the theorem's stated inputs and assumptions](hyp:hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,d,s). -/
-- @node: arm_prob_setIntegral
lemma arm_prob_setIntegral (P : CausalLaw) (d : Bool) (s : Set Covariate)
    (hs : MeasurableSet s) :
    ∫ x in s, (if d then P.e x else 1 - P.e x) ∂PX P =
      P.law.real {z | X z ∈ s ∧ A z = d} := by
  let : IsProbabilityMeasure (PX P) := Measure.isProbabilityMeasure_map measurable_X.aemeasurable
  have he : Integrable P.e (PX P) := P.e_integrable
  cases d
  · have hpartition : (X ⁻¹' s) = {z | X z ∈ s ∧ A z = false} ∪
        {z | X z ∈ s ∧ A z = true} := by
      ext z
      cases h : A z <;> simp [h]
    have hd : Disjoint {z | X z ∈ s ∧ A z = false}
        {z | X z ∈ s ∧ A z = true} := by
      rw [Set.disjoint_left]
      intro z hz hz'
      exact Bool.false_ne_true (hz.2.symm.trans hz'.2)
    have ht : MeasurableSet {z | X z ∈ s ∧ A z = true} :=
      (measurable_X hs).inter (arm_event_measurable true)
    have hm : (PX P).real s = P.law.real {z | X z ∈ s ∧ A z = false} +
        P.law.real {z | X z ∈ s ∧ A z = true} := by
      rw [PX, measureReal_def, Measure.map_apply measurable_X hs, hpartition,
        ← measureReal_def, measureReal_union hd ht]
    simp only [Bool.false_eq_true, if_false]
    rw [integral_sub (integrable_const _).integrableOn he.integrableOn,
      setIntegral_const, smul_eq_mul, mul_one]
    have hv : ∫ x in s, P.e x ∂PX P = P.law.real {z | X z ∈ s ∧ A z = true} :=
      P.e_version s hs
    linarith
  · exact P.e_version s hs

/-- Overlap transfers arm-specific null sets to design null sets.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP,d). -/
-- @node: PX_absolutelyContinuous_arm
lemma PX_absolutelyContinuous_arm (P : CausalLaw) (hP : CompleteModel P) (d : Bool) :
    PX P ≪ (P.law.restrict {z | A z = d}).map X := by
  let : IsProbabilityMeasure (PX P) := Measure.isProbabilityMeasure_map measurable_X.aemeasurable
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hzero : P.law.real {z | X z ∈ s ∧ A z = d} = 0 := by
    rw [measureReal_def, ← arm_design_apply P d s hs, hz, ENNReal.toReal_zero]
  have hi : Integrable (fun x => if d then P.e x else 1 - P.e x) (PX P) := by
    cases d
    · exact (integrable_const _).sub P.e_integrable
    · exact P.e_integrable
  have hl : ∫ x in s, (1/4 : ℝ) ∂PX P ≤
      ∫ x in s, (if d then P.e x else 1 - P.e x) ∂PX P := by
    apply integral_mono_ae (integrable_const _) hi.integrableOn
    filter_upwards with x
    cases d <;> simp only [Bool.false_eq_true, if_false, if_true]
    · linarith [(hP.overlap x).2]
    · exact (hP.overlap x).1
  rw [arm_prob_setIntegral P d s hs, hzero, setIntegral_const, smul_eq_mul] at hl
  have hr : (PX P).real s = 0 := by
    have := measureReal_nonneg (μ := PX P) (s := s)
    nlinarith
  exact (ENNReal.toReal_eq_zero_iff (PX P s)).mp hr |>.resolve_right (measure_ne_top _ _)

/-- The control Holder modulus gives continuity of the selected control mean. The result uses [the stated assumptions](hyp:hP) and establishes [the displayed conclusion](goal). -/
-- @node: continuous_mu0
@[fun_prop] lemma continuous_mu0 (P : CausalLaw) (hP : CompleteModel P) :
    Continuous P.mu0 := by
  have hh : HolderWith 3 (1/10 : ℝ≥0) P.mu0 := by
    intro x y
    rw [edist_dist, edist_dist]
    have hr := hP.control_holder x y
    have hn : (0 : ℝ) ≤ 1/10 := by norm_num
    have he := ENNReal.ofReal_le_ofReal hr
    simpa only [L, ← Real.dist_eq, ← Subtype.dist_eq,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist x y) hn,
      ENNReal.ofReal_ofNat, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
      ENNReal.coe_ofNat] using he
  exact hh.continuous (by norm_num)

/-- Continuity of the control mean and contrast gives continuity of the treated mean. The result uses [the stated assumptions](hyp:hP) and establishes [the displayed conclusion](goal). -/
-- @node: continuous_mu1
@[fun_prop] lemma continuous_mu1 (P : CausalLaw) (hP : CompleteModel P) :
    Continuous P.mu1 := by
  have hid : P.mu1 = fun x => P.mu0 x + tau P x := by
    funext x
    simp [tau]
  rw [hid]
  exact (continuous_mu0 P hP).add (continuous_tau P hP)

/-- The observed binary response bounds each selected arm mean almost everywhere. [The displayed conclusion](goal) follows. -/
-- @node: arm_mean_ae_mem_Icc
lemma arm_mean_ae_mem_Icc (P : CausalLaw) (d : Bool) :
    ∀ᵐ x ∂((P.law.restrict {z | A z = d}).map X),
      (if d then P.mu1 x else P.mu0 x) ∈ Icc (0 : ℝ) 1 := by
  have hi : Integrable (fun x => if d then P.mu1 x else P.mu0 x)
      ((P.law.restrict {z | A z = d}).map X) := by
    cases d
    · exact P.mu0_integrable
    · exact P.mu1_integrable
  have hv (s : Set Covariate) (hs : MeasurableSet s) :
      ∫ x in s, (if d then P.mu1 x else P.mu0 x)
        ∂((P.law.restrict {z | A z = d}).map X) =
      ∫ z in {z | X z ∈ s ∧ A z = d}, bit (Y z) ∂P.law := by
    cases d
    · exact P.mu0_version s hs
    · exact P.mu1_version s hs
  have hlo : 0 ≤ᵐ[((P.law.restrict {z | A z = d}).map X)]
      (fun x => if d then P.mu1 x else P.mu0 x) := by
    apply ae_nonneg_of_forall_setIntegral_nonneg hi
    intro s hs _
    rw [hv s hs]
    apply integral_nonneg
    intro z
    simp only [bit]
    split_ifs <;> norm_num
  have hup : (fun x => if d then P.mu1 x else P.mu0 x) ≤ᵐ[
      ((P.law.restrict {z | A z = d}).map X)] (fun _ => (1 : ℝ)) := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const _)
    intro s hs _
    rw [hv s hs, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      arm_design_apply P d s hs, ← measureReal_def, ← setIntegral_one_eq_measureReal]
    apply integral_mono_ae
    · apply Integrable.of_mem_Icc 0 1 (by fun_prop)
      filter_upwards with z
      simp only [bit]
      split_ifs <;> norm_num
    · exact integrable_const _
    · filter_upwards with z
      simp only [bit]
      split_ifs <;> norm_num
  filter_upwards [hlo, hup] with x hx hy
  exact ⟨hx, hy⟩

/-- Continuity and positive arm support extend the binary mean bounds to every covariate. The result uses [the stated assumptions](hyp:hP) and establishes [the displayed conclusion](goal). -/
-- @node: arm_mean_mem_Icc
lemma arm_mean_mem_Icc (P : CausalLaw) (hP : CompleteModel P) (d : Bool) (x : Covariate) :
    (if d then P.mu1 x else P.mu0 x) ∈ Icc (0 : ℝ) 1 := by
  let m : Covariate → ℝ := fun x => if d then P.mu1 x else P.mu0 x
  have hc : Continuous m := by
    cases d
    · exact continuous_mu0 P hP
    · exact continuous_mu1 P hP
  have hae : ∀ᵐ x ∂(volume : Measure Covariate), m x ∈ Icc (0 : ℝ) 1 :=
    ((volume_absolutelyContinuous_PX P hP).trans (PX_absolutelyContinuous_arm P hP d)).ae_le
      (arm_mean_ae_mem_Icc P d)
  have heq : m = fun x => max 0 (min 1 (m x)) := by
    apply continuous_eq_of_volume_ae_eq hc (by fun_prop)
    filter_upwards [hae] with x hx
    rw [min_eq_right hx.2, max_eq_right hx.1]
  change m x ∈ Icc (0 : ℝ) 1
  rw [congrFun heq x]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The difference of the two binary arm means bounds the point target between minus one and one.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP). -/
-- @node: theta_mem_Icc
lemma theta_mem_Icc (P : CausalLaw) (hP : CompleteModel P) : theta P ∈ Icc (-1 : ℝ) 1 := by
  have h0 := arm_mean_mem_Icc P hP false x0
  have h1 := arm_mean_mem_Icc P hP true x0
  simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
  change P.mu1 x0 - P.mu0 x0 ∈ Icc (-1 : ℝ) 1
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- The observation map is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_observe
@[fun_prop] lemma measurable_observe : Measurable observe := by
  unfold observe
  fun_prop

/-- The observed marginal determines each arm-specific covariate measure. [The displayed conclusion](goal) follows. -/
-- @node: arm_design_eq_observed
lemma arm_design_eq_observed (P : CausalLaw) (d : Bool) :
    (P.law.restrict {z | A z = d}).map X =
      ((Pobs P).restrict {z : O | z.2.1 = d}).map Prod.fst := by
  rw [Pobs, Measure.restrict_map measurable_observe
    (measurableSet_eq_fun (by fun_prop) measurable_const),
    Measure.map_map measurable_fst measurable_observe]
  rfl

/-- The observed marginal determines the response integral on every joint covariate-arm event.  [the theorem's stated inputs and assumptions](hyp:s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,d). -/
-- @node: observed_arm_outcome_integral
lemma observed_arm_outcome_integral (P : CausalLaw) (d : Bool)
    (s : Set Covariate) (hs : MeasurableSet s) :
    ∫ z in {z | X z ∈ s ∧ A z = d}, bit (Y z) ∂P.law =
      ∫ z in {z : O | z.1 ∈ s ∧ z.2.1 = d}, bit z.2.2 ∂Pobs P := by
  have ht : MeasurableSet {z : O | z.1 ∈ s ∧ z.2.1 = d} :=
    (hs.preimage measurable_fst).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const)
  rw [Pobs, setIntegral_map ht (by fun_prop) measurable_observe.aemeasurable]
  rfl

/-- Equal observed laws have identical continuous arm-mean versions at every covariate. The result uses [the stated assumptions](hyp:hP,hP',hobs) and establishes [the displayed conclusion](goal). -/
-- @node: arm_mean_eq_of_observed_eq
lemma arm_mean_eq_of_observed_eq (P P' : CausalLaw) (hP : CompleteModel P)
    (hP' : CompleteModel P') (hobs : Pobs P' = Pobs P) (d : Bool) :
    (fun x => if d then P'.mu1 x else P'.mu0 x) =
      (fun x => if d then P.mu1 x else P.mu0 x) := by
  have hmeasure : (P'.law.restrict {z | A z = d}).map X =
      (P.law.restrict {z | A z = d}).map X := by
    rw [arm_design_eq_observed P' d, arm_design_eq_observed P d, hobs]
  have hi (R : CausalLaw) : Integrable (fun x => if d then R.mu1 x else R.mu0 x)
      ((R.law.restrict {z | A z = d}).map X) := by
    cases d
    · exact R.mu0_integrable
    · exact R.mu1_integrable
  have hv (R : CausalLaw) (s : Set Covariate) (hs : MeasurableSet s) :
      ∫ x in s, (if d then R.mu1 x else R.mu0 x)
        ∂((R.law.restrict {z | A z = d}).map X) =
      ∫ z in {z : O | z.1 ∈ s ∧ z.2.1 = d}, bit z.2.2 ∂Pobs R := by
    rw [← observed_arm_outcome_integral R d s hs]
    cases d
    · exact R.mu0_version s hs
    · exact R.mu1_version s hs
  have hae : (fun x => if d then P'.mu1 x else P'.mu0 x) =ᵐ[
      ((P.law.restrict {z | A z = d}).map X)] (fun x => if d then P.mu1 x else P.mu0 x) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq
    · rw [← hmeasure]
      exact hi P'
    · exact hi P
    · intro s hs _
      rw [← hmeasure, hv P' s hs, hmeasure, hv P s hs, hobs]
  apply continuous_eq_of_volume_ae_eq
  · cases d
    · exact continuous_mu0 P' hP'
    · exact continuous_mu1 P' hP'
  · cases d
    · exact continuous_mu0 P hP
    · exact continuous_mu1 P hP
  · exact ((volume_absolutelyContinuous_PX P hP).trans
      (PX_absolutelyContinuous_arm P hP d)).ae_eq hae

/-- The observed law identifies the point target through uniqueness of the continuous arm means. The result uses [the stated assumptions](hyp:hP,hP',hobs) and establishes [the displayed conclusion](goal). -/
-- @node: theta_eq_of_observed_eq
lemma theta_eq_of_observed_eq (P P' : CausalLaw) (hP : CompleteModel P)
    (hP' : CompleteModel P') (hobs : Pobs P' = Pobs P) : theta P' = theta P := by
  have h0 := congrFun (arm_mean_eq_of_observed_eq P P' hP hP' hobs false) x0
  have h1 := congrFun (arm_mean_eq_of_observed_eq P P' hP hP' hobs true) x0
  simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
  change P'.mu1 x0 - P'.mu0 x0 = P.mu1 x0 - P.mu0 x0
  rw [h0, h1]

/-- Each arm-specific design measure has the selected arm probability as its density relative to
the design.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP,d). -/
-- @node: arm_design_withDensity
lemma arm_design_withDensity (P : CausalLaw) (hP : CompleteModel P) (d : Bool) :
    (P.law.restrict {z | A z = d}).map X =
      (PX P).withDensity (fun x => ENNReal.ofReal (if d then P.e x else 1-P.e x)) := by
  have hq : Measurable (fun x => if d then P.e x else 1-P.e x) := by
    have he := P.e_measurable
    cases d <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  have hi : Integrable (fun x => if d then P.e x else 1-P.e x) (PX P) := by
    let : IsProbabilityMeasure (PX P) := Measure.isProbabilityMeasure_map measurable_X.aemeasurable
    cases d
    · exact (integrable_const _).sub P.e_integrable
    · exact P.e_integrable
  have hn (x : Covariate) : 0 ≤ (if d then P.e x else 1-P.e x) := by
    cases d <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      linarith [(hP.overlap x).1, (hP.overlap x).2]
  ext s hs
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ hn),
    arm_prob_setIntegral P d s hs, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), arm_design_apply P d s hs]

/-- A measurable binary response is integrable under any finite measure.  [the theorem's stated inputs and assumptions](hyp:b,hb), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:Ω,μ). -/
-- @node: integrable_bit_comp
lemma integrable_bit_comp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (b : Ω → Bool) (hb : Measurable b) :
    Integrable (fun z => bit (b z)) μ := by
  apply Integrable.of_mem_Icc 0 1 (by fun_prop)
  filter_upwards with z
  simp only [bit]
  split_ifs <;> norm_num

/-- Exchangeability factors the arm-potential product; consistency and overlap identify its
conditional mean.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP,d). -/
-- @node: arm_conditional_mean
lemma arm_conditional_mean (P : CausalLaw) (hP : CompleteModel P) (d : Bool) :
    P.law[(fun z => bit (if d then (Ypot z).2 else (Ypot z).1)) |
      MeasurableSpace.comap X inferInstance] =ᵐ[P.law]
      (fun z => if d then P.mu1 (X z) else P.mu0 (X z)) := by
  have hσ : MeasurableSpace.comap X inferInstance ≤
      (inferInstance : MeasurableSpace Record) := measurable_X.comap_le
  let q : Covariate → ℝ := fun x => if d then P.e x else 1-P.e x
  let m : Covariate → ℝ := fun x => if d then P.mu1 x else P.mu0 x
  let r : Bool → ℝ := fun a => if a = d then 1 else 0
  let b : Record → Bool := fun z => if d then (Ypot z).2 else (Ypot z).1
  have hq : Measurable q := by
    have he := P.e_measurable
    cases d <;> dsimp [q] <;> fun_prop
  have hm : Measurable m := by cases d <;> dsimp [m] <;> fun_prop
  have hr : Measurable r := by dsimp [r]; fun_prop
  have hb : Measurable b := by cases d <;> dsimp [b, Ypot] <;> fun_prop
  have hqr (x : Covariate) : q x ∈ Icc (0 : ℝ) 1 := by
    dsimp [q]
    cases d <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      constructor <;> linarith [(hP.overlap x).1, (hP.overlap x).2]
  have hmr (x : Covariate) : m x ∈ Icc (0 : ℝ) 1 := arm_mean_mem_Icc P hP d x
  have hqi : Integrable (fun z => q (X z)) P.law :=
    Integrable.of_mem_Icc 0 1 (by fun_prop) (ae_of_all _ (fun z => hqr (X z)))
  have hqmi : Integrable (fun z => q (X z) * m (X z)) P.law := by
    apply Integrable.of_mem_Icc 0 1 (by fun_prop)
    filter_upwards with z
    exact ⟨mul_nonneg (hqr _).1 (hmr _).1,
      mul_le_one₀ (hqr _).2 (hmr _).1 (hmr _).2⟩
  have hri : Integrable (fun z => r (A z)) P.law := by
    apply Integrable.of_mem_Icc 0 1 (by fun_prop)
    filter_upwards with z
    dsimp [r]
    split_ifs <;> norm_num
  have hyi := integrable_bit_comp P.law Y measurable_Y
  have hbi := integrable_bit_comp P.law b hb
  have hryi : Integrable (fun z => r (A z) * bit (Y z)) P.law := by
    have heq : (fun z => r (A z) * bit (Y z)) =
        {z | A z = d}.indicator (fun z => bit (Y z)) := by
      funext z
      simp [r, Set.indicator]
    rw [heq]
    exact hyi.indicator (arm_event_measurable d)
  have harm : P.law[(fun z => r (A z)) | MeasurableSpace.comap X inferInstance]
      =ᵐ[P.law] fun z => q (X z) := by
    symm
    apply ae_eq_condExp_of_forall_setIntegral_eq hσ hri
      (fun _ _ _ => hqi.integrableOn)
    · intro s hs _
      obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
      have hi := setIntegral_map (μ := P.law) ht hq.aestronglyMeasurable measurable_X.aemeasurable
      have hv := arm_prob_setIntegral P d t ht
      have heq : (fun z => r (A z)) = {z | A z = d}.indicator (fun _ => (1 : ℝ)) := by
        funext z
        simp [r, Set.indicator]
      rw [heq, setIntegral_indicator (arm_event_measurable d), setIntegral_one_eq_measureReal]
      exact hi.symm.trans hv
    · exact (hq.comp (comap_measurable X)).aestronglyMeasurable
  have hprod : P.law[(fun z => r (A z) * bit (Y z)) |
      MeasurableSpace.comap X inferInstance] =ᵐ[P.law]
      fun z => q (X z) * m (X z) := by
    symm
    apply ae_eq_condExp_of_forall_setIntegral_eq hσ hryi
      (fun _ _ _ => hqmi.integrableOn)
    · intro s hs _
      obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
      have hi := setIntegral_map (μ := P.law) ht
        (hq.mul hm).aestronglyMeasurable measurable_X.aemeasurable
      have hw : ∫ x in t, m x ∂((P.law.restrict {z | A z = d}).map X) =
          ∫ x in t, q x * m x ∂PX P := by
        rw [arm_design_withDensity P hP d]
        change (∫ x in t, m x ∂(PX P).withDensity (ENNReal.ofReal ∘ q)) = _
        rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ (μ := PX P)
            (ENNReal.measurable_ofReal.comp hq).aemeasurable
            (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) m ht]
        apply integral_congr_ae
        filter_upwards with x
        simp [q, ENNReal.toReal_ofReal (hqr x).1, smul_eq_mul]
      have hv : ∫ x in t, m x ∂((P.law.restrict {z | A z = d}).map X) =
          ∫ z in {z | X z ∈ t ∧ A z = d}, bit (Y z) ∂P.law := by
        cases d
        · exact P.mu0_version t ht
        · exact P.mu1_version t ht
      have heq : (fun z => r (A z) * bit (Y z)) =
          {z | A z = d}.indicator (fun z => bit (Y z)) := by
        funext z
        simp [r, Set.indicator]
      rw [heq, setIntegral_indicator (arm_event_measurable d)]
      exact hi.symm.trans (hw.symm.trans hv)
    · exact ((hq.mul hm).comp (comap_measurable X)).aestronglyMeasurable
  have hci : CondIndepFun (MeasurableSpace.comap X inferInstance) hσ A b P.law := by
    cases d
    · exact hP.exchangeability.symm.comp measurable_id measurable_fst
    · exact hP.exchangeability.symm.comp measurable_id measurable_snd
  have hcons : (fun z => r (A z) * bit (Y z)) =ᵐ[P.law]
      fun z => r (A z) * bit (b z) := by
    filter_upwards [hP.consistency] with z hz
    dsimp [r, b]
    by_cases ha : A z = d
    · cases d <;> simp_all
    · simp [ha]
  have hf := Causalean.Mathlib.Probability.Independence.Conditional.condExp_mul_of_condIndep
    hσ measurable_A hb hci hr measurable_bit hri hbi (hryi.congr hcons)
  have hfact := (condExp_congr_ae hcons).trans hf
  filter_upwards [harm, hprod, hfact] with z ha hp hf
  simp only [Pi.mul_apply] at hf
  rw [ha] at hf
  have hn : q (X z) ≠ 0 := by
    have hpos : 1/4 ≤ q (X z) := by
      dsimp [q]
      cases d <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
        linarith [(hP.overlap (X z)).1, (hP.overlap (X z)).2]
    linarith
  exact mul_left_cancel₀ hn (hf.symm.trans hp)

/-- Conditional-expectation linearity identifies the selected contrast with the conditional causal
effect.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP). -/
-- @node: tau_conditional_causal_contrast
lemma tau_conditional_causal_contrast (P : CausalLaw) (hP : CompleteModel P) :
    (fun z => tau P (X z)) =ᵐ[P.law]
      P.law[(fun z => bit (Ypot z).2 - bit (Ypot z).1) |
        MeasurableSpace.comap X inferInstance] := by
  have h1 := arm_conditional_mean P hP true
  have h0 := arm_conditional_mean P hP false
  have hi1 := integrable_bit_comp P.law (fun z => (Ypot z).2) (by unfold Ypot; fun_prop)
  have hi0 := integrable_bit_comp P.law (fun z => (Ypot z).1) (by unfold Ypot; fun_prop)
  exact ((condExp_sub hi1 hi0 _).trans (h1.sub h0)).symm

/-- Model regularity selects a unique continuous contrast, bounds the target, and identifies
both the conditional causal contrast and its point value from the observed marginal. The result uses [the stated assumptions](hyp:hP) and establishes [the displayed conclusion](goal). -/
-- @node: lem:point-version
lemma point_version (P : CausalLaw) (hP : CompleteModel P) :
    Continuous (tau P) ∧
    (∀ v : Covariate → ℝ, Continuous v → v =ᵐ[PX P] tau P → v = tau P) ∧
    theta P ∈ Set.Icc (-1) 1 ∧
    (fun z => tau P (X z)) =ᵐ[P.law]
      P.law[(fun z => bit (Ypot z).2 - bit (Ypot z).1) |
        MeasurableSpace.comap X inferInstance] ∧
    (∀ P' : CausalLaw, CompleteModel P' → Pobs P' = Pobs P → theta P' = theta P) := by
  refine ⟨continuous_tau P hP, ?_, ?_⟩
  · intro v hv heq
    exact continuous_tau_unique P hP v hv heq
  · refine ⟨theta_mem_Icc P hP, tau_conditional_causal_contrast P hP, ?_⟩
    intro P' hP' hobs
    exact theta_eq_of_observed_eq P P' hP hP' hobs
end CausalSmith.Stat.PrivateCateRoughdesign
