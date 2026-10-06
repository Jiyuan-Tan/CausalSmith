module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.LowerPairs

/-! # Generic block-experiment risk separation

The local information budget, measurable learner representatives, and the
pointwise welfare loss give a two-point floor without any extra law-class premise.
-/

@[expose] public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory

/-- The generic block construction has the support and conditional versions of a row law. -/
-- @node: blockPair_wellFormed
lemma blockPair_wellFormed (m q h : ℝ) (σ : Bool)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    WellFormed (blockPair m q h σ) := by
  exact ⟨blockPair_probability m q h σ, blockPair_full_score_support m q h σ,
    blockPair_observed_support m q h σ,
    (blockLogger_measurable m q).comp measurable_subtype_coe,
    (blockPair_tau_measurable m q h σ).comp measurable_subtype_coe,
    blockPair_logger_identity m q h σ hq hq1,
    blockPair_effect_identity m q h σ hh hh1⟩

/-- The effect in either block alternative is bounded by one. -/
-- @node: blockPair_tau_bound
lemma blockPair_tau_bound (m q h : ℝ) (σ : Bool)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (x : ℝ) :
    |(blockPair m q h σ).tau x| ≤ 1 := by
  change |blockMeanOne m h σ x - blockMeanZero m x| ≤ 1
  unfold blockMeanOne blockMeanZero
  cases σ <;> split_ifs <;> simp [abs_of_nonneg hh, abs_neg] <;> linarith

/-- A supported Borel policy has integrable welfare in the block experiment. -/
-- @node: blockPair_welfare_integrable
@[fun_prop] lemma blockPair_welfare_integrable (m q h : ℝ) (σ : Bool)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (φ : ℝ → Bool)
    (hφ : φ ∈ binaryPolicyClass) :
    Integrable (fun x => (if φ x then (1:ℝ) else 0) *
      (blockPair m q h σ).tau x) uniformRandomizer := by
  haveI := uniformRandomizer_probability
  have hp : Measurable (fun x : Set.Icc (0:ℝ) 1 => φ x) := hφ
  have hm : Measurable (fun x : Set.Icc (0:ℝ) 1 =>
      (if φ x then (1:ℝ) else 0) * (blockPair m q h σ).tau x) :=
    (measurable_const.ite (hp (measurableSet_singleton true)) measurable_const).mul
      ((blockPair_tau_measurable m q h σ).comp measurable_subtype_coe)
  have ha := aemeasurable_restrict_of_measurable_subtype
    (μ := uniformRandomizer)
    (f := fun x => (if φ x then (1:ℝ) else 0) * (blockPair m q h σ).tau x)
    measurableSet_Icc hm
  rw [Measure.restrict_eq_self_of_ae_mem (μ := uniformRandomizer)
    (ae_restrict_mem measurableSet_Icc :
      ∀ᵐ x ∂uniformRandomizer, x ∈ Set.Icc (0:ℝ) 1)] at ha
  apply Integrable.of_bound ha.aestronglyMeasurable 1
  filter_upwards with x
  cases φ x <;> simpa using (blockPair_tau_bound m q h σ hh hh1 x)

/-- The pointwise loss is the difference of canonical and policy welfare. -/
-- @node: blockPolicyLoss
noncomputable def blockPolicyLoss (m q h : ℝ) (σ : Bool) (φ : ℝ → Bool) (x : ℝ) : ℝ :=
  ((if canonicalPolicy (blockPair m q h σ) x then (1:ℝ) else 0) -
    (if φ x then (1:ℝ) else 0)) * (blockPair m q h σ).tau x

/-- Canonical welfare dominates every binary policy pointwise. -/
-- @node: blockPolicyLoss_bounds
lemma blockPolicyLoss_bounds (m q h : ℝ) (σ : Bool) (φ : ℝ → Bool)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (x : ℝ) :
    0 ≤ blockPolicyLoss m q h σ φ x ∧ blockPolicyLoss m q h σ φ x ≤ 1 := by
  have hb := blockPair_tau_bound m q h σ hh hh1 x
  unfold blockPolicyLoss canonicalPolicy
  by_cases ht : 0 ≤ (blockPair m q h σ).tau x
  · cases φ x <;> simp [ht] <;> simpa [abs_of_nonneg ht] using hb
  · have ht' : (blockPair m q h σ).tau x ≤ 0 := le_of_not_ge ht
    cases φ x <;> simp [ht]
    exact ⟨ht', by simpa [abs_of_nonpos ht'] using hb⟩

/-- Binary choices incur the full block effect across the two signs. -/
-- @node: blockPolicyLoss_sum
lemma blockPolicyLoss_sum (m q h : ℝ) (φ : ℝ → Bool)
    (hh : 0 < h) (hh1 : h ≤ 1) (x : ℝ) :
    h * (if x ≤ m then (1:ℝ) else 0) ≤
      blockPolicyLoss m q h true φ x + blockPolicyLoss m q h false φ x := by
  by_cases hx : x ≤ m
  · cases hp : φ x <;>
      simp [blockPolicyLoss, canonicalPolicy, blockPair, blockMeanOne,
        blockMeanZero, hx, hp, hh.le, not_le.mpr (neg_neg_of_pos hh)]
  · simpa [hx] using add_nonneg
      (blockPolicyLoss_bounds m q h true φ hh.le hh1 x).1
      (blockPolicyLoss_bounds m q h false φ hh.le hh1 x).1

/-- Welfare subtraction equals the integral of the pointwise loss. -/
-- @node: blockPair_regret_integral
lemma blockPair_regret_integral (m q h : ℝ) (σ : Bool)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (φ : ℝ → Bool)
    (hφ : φ ∈ binaryPolicyClass) :
    rawRegret (blockPair m q h σ) φ =
      ∫ x, blockPolicyLoss m q h σ φ x ∂uniformRandomizer := by
  have hc : canonicalPolicy (blockPair m q h σ) ∈ binaryPolicyClass := by
    change Measurable (fun x : Set.Icc (0:ℝ) 1 => canonicalPolicy (blockPair m q h σ) x)
    unfold canonicalPolicy
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq, Function.comp_def] using
      (measurableSet_le measurable_const
        ((blockPair_tau_measurable m q h σ).comp measurable_subtype_coe))
  unfold rawRegret rawWelfare
  rw [blockPair_score_uniform, ← integral_sub
    (blockPair_welfare_integrable m q h σ hh hh1 _ hc)
    (blockPair_welfare_integrable m q h σ hh hh1 φ hφ)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [blockPolicyLoss, sub_mul]

/-- The loss integral is integrable as a difference of welfare integrands. -/
-- @node: blockPolicyLoss_integrable
@[fun_prop] lemma blockPolicyLoss_integrable (m q h : ℝ) (σ : Bool)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (φ : ℝ → Bool)
    (hφ : φ ∈ binaryPolicyClass) :
    Integrable (blockPolicyLoss m q h σ φ) uniformRandomizer := by
  have hc : canonicalPolicy (blockPair m q h σ) ∈ binaryPolicyClass := by
    change Measurable (fun x : Set.Icc (0:ℝ) 1 => canonicalPolicy (blockPair m q h σ) x)
    unfold canonicalPolicy
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq, Function.comp_def] using
      (measurableSet_le measurable_const
        ((blockPair_tau_measurable m q h σ).comp measurable_subtype_coe))
  change Integrable (fun x =>
    ((if canonicalPolicy (blockPair m q h σ) x then (1:ℝ) else 0) -
      (if φ x then (1:ℝ) else 0)) * (blockPair m q h σ).tau x) uniformRandomizer
  simp only [sub_mul]
  exact
    (blockPair_welfare_integrable m q h σ hh hh1 _ hc).sub
      (blockPair_welfare_integrable m q h σ hh hh1 φ hφ)

/-- The policy regret is nonnegative and bounded under the generic block law. -/
-- @node: blockPair_policy_regret_bounds
lemma blockPair_policy_regret_bounds (m q h : ℝ) (σ : Bool)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (φ : ℝ → Bool)
    (hφ : φ ∈ binaryPolicyClass) :
    0 ≤ rawRegret (blockPair m q h σ) φ ∧ rawRegret (blockPair m q h σ) φ ≤ 1 := by
  haveI := uniformRandomizer_probability
  rw [blockPair_regret_integral m q h σ hh hh1 φ hφ]
  constructor
  · exact integral_nonneg (fun x => (blockPolicyLoss_bounds m q h σ φ hh hh1 x).1)
  · simpa using integral_mono (blockPolicyLoss_integrable m q h σ hh hh1 φ hφ)
      (integrable_const (1:ℝ)) (fun x => (blockPolicyLoss_bounds m q h σ φ hh hh1 x).2)

/-- Integrating the pointwise separation yields the block regret separation. -/
-- @node: blockPair_policy_regret_sum
lemma blockPair_policy_regret_sum (m q h : ℝ)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (φ : ℝ → Bool) (hφ : φ ∈ binaryPolicyClass) :
    m*h ≤ rawRegret (blockPair m q h true) φ + rawRegret (blockPair m q h false) φ := by
  haveI := uniformRandomizer_probability
  rw [blockPair_regret_integral m q h true hh.le hh1 φ hφ,
    blockPair_regret_integral m q h false hh.le hh1 φ hφ,
    ← integral_add (blockPolicyLoss_integrable m q h true hh.le hh1 φ hφ)
      (blockPolicyLoss_integrable m q h false hh.le hh1 φ hφ)]
  have hb : Integrable (fun x => h * (if x ≤ m then (1:ℝ) else 0)) uniformRandomizer := by
    have heq : (fun x => h * (if x ≤ m then (1:ℝ) else 0)) =
        (Set.Iic m).indicator (fun _ => h) := by
      ext x
      by_cases hx : x ≤ m <;> simp [Set.indicator, hx]
    rw [heq]
    exact (integrable_const h).indicator measurableSet_Iic
  have hi := integral_mono hb
    ((blockPolicyLoss_integrable m q h true hh.le hh1 φ hφ).add
      (blockPolicyLoss_integrable m q h false hh.le hh1 φ hφ))
    (blockPolicyLoss_sum m q h φ hh hh1)
  rw [integral_const_mul, uniformRandomizer_coin_integral m hm hm1] at hi
  simpa [mul_comm] using hi

/-- A jointly Borel policy family has Borel regret in either block alternative. -/
-- @node: blockPair_regret_family_measurable
@[fun_prop] lemma blockPair_regret_family_measurable {Ω : Type*} [MeasurableSpace Ω]
    (m q h : ℝ) (σ : Bool) (ψ : Ω → ℝ → Bool)
    (hψ : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 => ψ z.1 z.2)) :
    Measurable (fun w => rawRegret (blockPair m q h σ) (ψ w)) := by
  haveI : IsProbabilityMeasure uniformRandomizer := uniformRandomizer_probability
  have hs : ∀ᵐ x ∂uniformRandomizer, x ∈ Set.Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have ht : Measurable (fun x : Set.Icc (0:ℝ) 1 => (blockPair m q h σ).tau x) :=
    (blockPair_tau_measurable m q h σ).comp measurable_subtype_coe
  have hm : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 =>
      (if ψ z.1 z.2 then (1:ℝ) else 0) * (blockPair m q h σ).tau z.2) := by
    have hb : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 =>
        if ψ z.1 z.2 then (1:ℝ) else 0) := by
      exact measurable_const.ite (hψ (measurableSet_singleton true)) measurable_const
    exact hb.mul (ht.comp measurable_snd)
  have hi : Measurable (fun w => ∫ x : Set.Icc (0:ℝ) 1,
      (if ψ w x then (1:ℝ) else 0) * (blockPair m q h σ).tau x
      ∂Measure.comap Subtype.val uniformRandomizer) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have heq (w : Ω) : rawWelfare (blockPair m q h σ) (ψ w) =
      ∫ x : Set.Icc (0:ℝ) 1, (if ψ w x then (1:ℝ) else 0) * (blockPair m q h σ).tau x
        ∂Measure.comap Subtype.val uniformRandomizer := by
    rw [integral_subtype_comap (μ := uniformRandomizer) measurableSet_Icc
      (fun x => (if ψ w x then (1:ℝ) else 0) * (blockPair m q h σ).tau x),
      Measure.restrict_eq_self_of_ae_mem hs]
    simp only [rawWelfare, blockPair_score_uniform]
  simp_rw [rawRegret, heq]
  exact hi.const_sub _

/-- Well-formed laws support only valid observations and randomizers. -/
-- @node: learner_input_support_of_wellFormed
lemma learner_input_support_of_wellFormed (n : ℕ) (P : RowLaw) (hP : WellFormed P) :
    ∀ᵐ du ∂experiment P n,
      (∀ i, (du.1 i).X ∈ Set.Icc (0:ℝ) 1 ∧ (du.1 i).Y ∈ Set.Icc (-1:ℝ) 1) ∧
      du.2 ∈ Set.Icc (0:ℝ) 1 := by
  have hψ : Measurable (fun o : FullRow => (⟨o.X,o.A,o.Y⟩ : Observation)) := by
    apply measurable_comap_iff.mpr
    exact (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ =>
      (t.1,t.2.1,t.2.2.1))).comp (comap_measurable _)
  have hX : Measurable (fun o : Observation => o.X) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.1)).comp
      (comap_measurable _)
  have hY : Measurable (fun o : Observation => o.Y) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.2.2)).comp
      (comap_measurable _)
  have hobs : ∀ᵐ o ∂P.obsLaw,
      o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1 := by
    apply (ae_map_iff hψ.aemeasurable
      ((hX measurableSet_Icc).inter (hY measurableSet_Icc))).2
    filter_upwards [ae_iff.mpr hP.2.1, ae_iff.mpr hP.2.2.1] with o hx hy
    exact ⟨hx,hy⟩
  haveI : IsProbabilityMeasure P.full := hP.1
  haveI : IsProbabilityMeasure P.obsLaw := Measure.isProbabilityMeasure_map hψ.aemeasurable
  have hdata : ∀ᵐ d ∂sampleLaw P n, ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1 :=
    Filter.eventually_all.2 (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => P.obsLaw) (i := i)).eventually hobs)
  have hU : ∀ᵐ u ∂uniformRandomizer, u ∈ Set.Icc (0:ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hdata,
    Measure.quasiMeasurePreserving_snd.ae hU] with du hd hu
  exact ⟨hd, hu⟩

end CausalSmith.Stat.ScorethresholdOverlapRegret
