module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerDecision

/-! Whole-class honesty and length reduction for the finite sign priors. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Membership of a fixed target is measurable for the bounded interval codes. -/
-- @node: lower_interval_membership_measurable
lemma lower_interval_membership_measurable (θ : ℝ) :
    MeasurableSet {c : IntervalCode | θ ∈ c.toSet} := by
  apply measurableSet_sum_iff.mpr
  constructor
  · simp [IntervalCode.toSet]
  · have hlo : Measurable (fun c : Endpoints => c.1.1) := by fun_prop
    have hhi : Measurable (fun c : Endpoints => c.1.2.1) := by fun_prop
    have hbl : MeasurableSet {c : Endpoints | c.1.2.2.1 = true} :=
      measurableSet_eq_fun (by fun_prop) measurable_const
    have hbh : MeasurableSet {c : Endpoints | c.1.2.2.2 = true} :=
      measurableSet_eq_fun (by fun_prop) measurable_const
    have h := hbl.ite (hbh.ite ((measurableSet_le hlo (measurable_const (a := θ))).inter
      (measurableSet_le (measurable_const (a := θ)) hhi)) ((measurableSet_le hlo (measurable_const (a := θ))).inter
      (measurableSet_lt (measurable_const (a := θ)) hhi)))
      (hbh.ite ((measurableSet_lt hlo (measurable_const (a := θ))).inter
      (measurableSet_le (measurable_const (a := θ)) hhi)) ((measurableSet_lt hlo (measurable_const (a := θ))).inter
      (measurableSet_lt (measurable_const (a := θ)) hhi)))
    convert h using 1
    ext c
    cases hb : c.1.2.2.1 <;> cases hh : c.1.2.2.2 <;>
      simp [IntervalCode.toSet,Set.ite,hb,hh]

/-- Endpoint-coded lengths are measurable, nonnegative, and bounded by one. -/
-- @node: lower_interval_length_properties
lemma lower_interval_length_properties : Measurable IntervalCode.length ∧
    ∀ c : IntervalCode, 0 ≤ c.length ∧ c.length ≤ 1 := by
  constructor
  · change Measurable (Sum.elim (fun _ : Unit => (0 : ℝ))
      (fun c : Endpoints => max 0 (c.1.2.1-c.1.1)))
    apply Measurable.sumElim measurable_const
    fun_prop
  · intro c
    cases c with
    | inl u => exact ⟨le_rfl,by norm_num [IntervalCode.length]⟩
    | inr c =>
      change 0 ≤ max 0 (c.1.2.1-c.1.1) ∧ max 0 (c.1.2.1-c.1.1) ≤ 1
      exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith [c.2.1,c.2.2.2])⟩

/-- A coded interval containing both targets has length at least their distance. -/
-- @node: lower_interval_separation
lemma lower_interval_separation (c : IntervalCode) (θ0 θ1 : ℝ)
    (h0 : θ0 ∈ c.toSet) (h1 : θ1 ∈ c.toSet) : |θ1-θ0| ≤ c.length := by
  cases c with
  | inl u => simp [IntervalCode.toSet] at h0
  | inr c =>
    have hmem : ∀ θ ∈ IntervalCode.toSet (Sum.inr c), c.1.1 ≤ θ ∧ θ ≤ c.1.2.1 := by
      intro θ hθ
      cases hb : c.1.2.2.1 <;> cases hh : c.1.2.2.2 <;>
        simp [IntervalCode.toSet,hb,hh] at hθ <;> constructor <;> linarith [hθ.1,hθ.2]
    have ha := hmem θ0 h0
    have hb := hmem θ1 h1
    change |θ1-θ0| ≤ max 0 (c.1.2.1-c.1.1)
    exact (abs_le.mpr ⟨by linarith [ha.1,ha.2,hb.1,hb.2],
      by linarith [ha.1,ha.2,hb.1,hb.2]⟩).trans (le_max_right _ _)

/-- Uniform averaging preserves a common real event-probability lower bound. -/
-- @node: lower_uniform_mixture_event_ge
lemma lower_uniform_mixture_event_ge {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Ω] (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (E : Set Ω) (hE : MeasurableSet E) (a : ℝ) (ha : ∀ i, a ≤ (ν i).real E) :
    a ≤ (((Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, ν i)).real E := by
  have hi (i : ι) : Integrable (E.indicator (fun _ => (1 : ℝ))) (ν i) :=
    (integrable_const _).indicator hE
  have h := lower_uniform_mixture_integral_le ν
    (fun z => -(E.indicator (fun _ => (1 : ℝ)) z)) (-a) (fun i => (hi i).neg)
    (fun i => by simpa [integral_neg, integral_indicator hE] using neg_le_neg (ha i))
  simpa [integral_neg, integral_indicator hE] using (neg_le_neg h)

/-- Honesty over the full model transfers to each finite sign mixture. -/
-- @node: lower_mixture_coverage
lemma lower_mixture_coverage (κ : Params) (n : ℕ) (hκ : κ.Valid)
    (hb : boundary κ ≤ 1) (hn : 2 ≤ n) (i : OriginalIntervalProc n)
    (hh : ∀ law, InModel κ law → 9/10 ≤ coverage n jointLaw (fun _ => ()) i law)
    (ε : Bool) :
    9/10 ≤ ((lowerMixture κ n ε).prod design).real
      {z | lowerEffect κ n ε xstar ∈ (i.1 (z.1,z.2,())).toSet} := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI (v : Signs κ n) : IsProbabilityMeasure (jointLaw n (lowerPriorLaw κ n ε v).P) := by
    unfold jointLaw; infer_instance
  have hE : MeasurableSet {z : Experiment n |
      lowerEffect κ n ε xstar ∈ (i.1 (z.1,z.2,())).toSet} :=
    (lower_interval_membership_measurable _).preimage (i.2.comp (by fun_prop))
  rw [lower_seeded_mixture_eq]
  apply lower_uniform_mixture_event_ge _ _ hE
  intro v
  rw [← lower_prior_target κ n hκ hb hn ε v]
  exact hh _ (lower_prior_membership κ n hκ hb hn ε v).1

/-- Bounded coded interval lengths are integrable in every probability experiment. -/
-- @node: lower_interval_length_integrable
lemma lower_interval_length_integrable (n : ℕ) (i : OriginalIntervalProc n)
    (μ : Measure (Experiment n)) [IsProbabilityMeasure μ] :
    Integrable (fun z => (i.1 (z.1,z.2,())).length) μ := by
  have hm := lower_interval_length_properties.1.comp (i.2.comp
    (by fun_prop : Measurable (fun z : Experiment n => (z.1,z.2,()))))
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [] with z
  change ‖(i.1 (z.1,z.2,())).length‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (lower_interval_length_properties.2 _).1]
  exact (lower_interval_length_properties.2 _).2

/-- The finite prior's mean interval length is at most the whole-model worst mean length. -/
-- @node: lower_mixture_length_le_worst
lemma lower_mixture_length_le_worst (κ : Params) (n : ℕ) (hκ : κ.Valid)
    (hb : boundary κ ≤ 1) (hn : 2 ≤ n) (i : OriginalIntervalProc n) (ε : Bool) :
    (∫ z, (i.1 (z.1,z.2,())).length ∂(lowerMixture κ n ε).prod design) ≤
      ⨆ law : {law // InModel κ law}, expectedLength n jointLaw (fun _ => ()) i law.1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hB : BddAbove (Set.range (fun law : {law // InModel κ law} =>
      expectedLength n jointLaw (fun _ => ()) i law.1)) := by
    refine ⟨1,?_⟩
    rintro _ ⟨law,rfl⟩
    letI : IsProbabilityMeasure (jointLaw n law.1.P) := by unfold jointLaw; infer_instance
    simpa [expectedLength] using integral_mono
      (lower_interval_length_integrable n i (jointLaw n law.1.P))
      (integrable_const (1 : ℝ)) (fun z => (lower_interval_length_properties.2 _).2)
  rw [lower_seeded_mixture_eq]
  apply lower_uniform_mixture_integral_le
  · intro v
    letI : IsProbabilityMeasure (jointLaw n (lowerPriorLaw κ n ε v).P) := by
      unfold jointLaw; infer_instance
    exact lower_interval_length_integrable n i _
  · intro v
    exact le_ciSup hB ⟨lowerPriorLaw κ n ε v,
      (lower_prior_membership κ n hκ hb hn ε v).1⟩

/-- TV transfer and simultaneous coverage force the interaction length for every honest procedure. -/
-- @node: lower_interaction_worst_length
lemma lower_interaction_worst_length (κ : Params) (n : ℕ) (hκ : κ.Valid)
    (hb : boundary κ ≤ 1) (hn : 2 ≤ n) (i : OriginalIntervalProc n)
    (hh : ∀ law, InModel κ law → 9/10 ≤ coverage n jointLaw (fun _ => ()) i law) :
    cInter κ*(n : ℝ)^(-rInter κ) ≤
      ⨆ law : {law // InModel κ law}, expectedLength n jointLaw (fun _ => ()) i law.1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI (ε : Bool) : IsProbabilityMeasure (lowerMixture κ n ε) :=
    lower_uniform_mixture_probability _
  let ν0 := (lowerMixture κ n true).prod design
  let ν1 := (lowerMixture κ n false).prod design
  let E0 := {z : Experiment n | lowerEffect κ n true xstar ∈ (i.1 (z.1,z.2,())).toSet}
  let E1 := {z : Experiment n | lowerEffect κ n false xstar ∈ (i.1 (z.1,z.2,())).toSet}
  have hE0 : MeasurableSet E0 :=
    (lower_interval_membership_measurable _).preimage (i.2.comp (by fun_prop))
  have hE1 : MeasurableSet E1 :=
    (lower_interval_membership_measurable _).preimage (i.2.comp (by fun_prop))
  have hc0 := lower_mixture_coverage κ n hκ hb hn i hh true
  have hc1 := lower_mixture_coverage κ n hκ hb hn i hh false
  have htv : Causalean.Stat.tvDist ν0 ν1 ≤ 1/4 := by
    rw [two_prior_seed_tv]
    exact lower_mixture_tv κ n hκ hb hn
  have htransfer := (Causalean.Stat.measureReal_sub_le_tvDist
    (μ := ν0) (ν := ν1) hE1).trans htv
  have hmass : (11/20 : ℝ) ≤ ν0.real (E0 ∩ E1) := by
    have h := measureReal_union_add_inter (μ := ν0) (s := E0) hE1
    have hu : ν0.real (E0 ∪ E1) ≤ 1 := measureReal_le_one
    change 9/10 ≤ ν0.real E0 at hc0
    change 9/10 ≤ ν1.real E1 at hc1
    linarith
  let Δ := |lowerEffect κ n false xstar-lowerEffect κ n true xstar|
  have hthreshold := threshold_mass_le_lintegral ν0
    (fun z => (i.1 (z.1,z.2,())).length) Δ (abs_nonneg _) (E0 ∩ E1) (hE0.inter hE1)
    (fun z hz => lower_interval_separation _ _ _ hz.1 hz.2)
  rw [← ofReal_integral_eq_lintegral_ofReal (lower_interval_length_integrable n i ν0)
    (Filter.Eventually.of_forall (fun z => (lower_interval_length_properties.2 _).1))] at hthreshold
  have hr := (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg (fun z => (lower_interval_length_properties.2 _).1))).mp hthreshold
  have hlen : (3/16 : ℝ)*Δ ≤ ∫ z, (i.1 (z.1,z.2,())).length ∂ν0 := by
    have hΔ : 0 ≤ Δ := abs_nonneg _
    have hm := mul_le_mul_of_nonneg_left hmass hΔ
    nlinarith
  rw [cInter_separation_identity κ n hn,abs_sub_comm]
  exact hlen.trans (lower_mixture_length_le_worst κ n hκ hb hn i true)

/-- The full target interval witnesses nonemptiness of the whole-class honest decisions. -/
-- @node: lower_honest_procedures_nonempty
lemma lower_honest_procedures_nonempty (κ : Params) (n : ℕ) :
    Nonempty {i : IntervalProc n Unit //
      ∀ law, InModel κ law → 9/10 ≤ coverage n jointLaw (fun _ => ()) i law} := by
  let c : IntervalCode := .inr ⟨(-1/2,1/2,true,true),by norm_num⟩
  refine ⟨⟨⟨fun _ => c,measurable_const⟩,?_⟩⟩
  intro law hm
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (jointLaw n law.P) := by unfold jointLaw; infer_instance
  have hθ : law.theta ∈ c.toSet := by
    have ht := hm.effectRange xstar
    change |law.theta| ≤ 1/2 at ht
    have ha := abs_le.mp ht
    change -1/2 ≤ law.theta ∧ law.theta ≤ 1/2
    constructor <;> linarith [ha.1,ha.2]
  simp [coverage,hθ]
  norm_num

/-- Infimizing over whole-class honest procedures gives the interaction length bound. -/
-- @node: lower_interaction_honest_length
lemma lower_interaction_honest_length (κ : Params) (n : ℕ) (hκ : κ.Valid)
    (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
    cInter κ*(n : ℝ)^(-rInter κ) ≤ honestLength κ n := by
  haveI := lower_honest_procedures_nonempty κ n
  exact le_ciInf (fun i => lower_interaction_worst_length κ n hκ hb hn i.1 i.2)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
