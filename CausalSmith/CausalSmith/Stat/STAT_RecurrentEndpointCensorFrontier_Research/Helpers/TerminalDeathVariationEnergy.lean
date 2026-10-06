module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessFiniteRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathOptionalVariation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathPlugin
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleTails

/-! # Terminal death optional-variation energy

Roadmap (40): compensate deterministic terminal marks before applying the
binomial reciprocal-risk bound. The endpoint envelope is integrable under
subcritical retention; no independence of estimated weights is used.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier
namespace DeathCP

open Causalean.Stat.RecurrentEvent.CountingProcess

/-- The canonical reciprocal risk has a finite first moment. -/
-- @node: reference_inverseRisk_integrable
lemma reference_inverseRisk_integrable (P : SubjectLaw) (a : Arm) (n : ℕ) (t : ℝ) :
    Integrable (fun x : Sample n => inverseRisk t x)
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    ⟨(armDeathFailureLaw_nonnegativeTimeLaw P a).1⟩
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
      (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
    infer_instance
  apply Integrable.of_bound
    (inverseRisk_jointMeasurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  filter_upwards [] with x
  change |inverseRisk t x| ≤ 1
  rw [abs_of_nonneg (pairInverseRisk_mem_Icc t x).1]
  exact (pairInverseRisk_mem_Icc t x).2

/-- The exact binomial bound also controls the extended reciprocal-risk
expectation, permitting Tonelli for terminal weights. -/
-- @node: reference_inverseRisk_lintegral_le
lemma reference_inverseRisk_lintegral_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫⁻ x : Sample n, ENNReal.ofReal (inverseRisk t x)
      ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
    ENNReal.ofReal (2 / ((n : ℝ) * (P.p a * retention P a t * survival P a t))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (reference_inverseRisk_integrable P a n t)
    (Eventually.of_forall (fun x => (pairInverseRisk_mem_Icc t x).1))]
  exact ENNReal.ofReal_le_ofReal (integral_inverseRisk_le_arm_tail c P hP a hn ht0 ht1)

/-- Compensated terminal squared inverse-risk marks satisfy the exact
population death-energy envelope on every positive sample size. -/
-- @node: reference_terminal_death_marks_lintegral_le
lemma reference_terminal_death_marks_lintegral_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (H : ℝ → ℝ) (hH : Measurable H) {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal (n : ℝ) *
      (∫⁻ x : Sample n, ∑ i : Fin n, ENNReal.ofReal
        (if T < (x i).2 ∧ (x i).2 ≤ 1 ∧ (x i).2 < (x i).1 then
          H (x i).2 ^ 2 * inverseRisk (x i).2 x ^ 2 else 0)
        ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a)) ≤
    ∫⁻ t in Ioc T 1, ENNReal.ofReal
      ((2 / P.p a) * (H t ^ 2 * P.hazard a t /
        (survival P a t * retention P a t))) ∂volume := by
  rw [terminalInverseRiskSq_sum_tonelli _ _ _ H
    (armDeathFailureLaw_nonnegativeTimeLaw P a) (referenceDeathLaw_hasCensorHazard hP a)
    hH T (by norm_num)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hset : Ioc T 1 = Icc (0 : ℝ) 1 ∩ Ioi T := by
    ext t
    simp only [mem_Ioc, mem_inter_iff, mem_Icc, mem_Ioi]
    constructor
    · intro ht; exact ⟨⟨hT.trans ht.1.le, ht.2⟩, ht.1⟩
    · rintro ⟨ht, htT⟩; exact ⟨htT, ht.2⟩
  rw [hset, inter_comm (Icc (0 : ℝ) 1) (Ioi T),
    ← Measure.restrict_restrict measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (volume.restrict (Icc (0 : ℝ) 1)).ae_ne (1 : ℝ)] with t ht htne
  by_cases htT : T < t
  · have ht0 : 0 < t := hT.trans_lt htT
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne
    simp only [indicator_apply, mem_Ioi, if_pos htT]
    apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl
      (reference_inverseRisk_lintegral_le c P hP a hn ht0 ht1))).trans_eq
    rw [referenceDeathHazard_eq P a ht, ← ENNReal.ofReal_mul
      (mul_nonneg (sq_nonneg _) (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    congr 1
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hp : P.p a ≠ 0 := (c.pMin_pos.trans_le (hP.treatmentOverlap a)).ne'
    have hg : retention P a t ≠ 0 := (retention_pos_of_modelClass c P hP a t ht0.le ht1).ne'
    have hs : survival P a t ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  · simp [htT, indicator_apply]

/-- A continuous deterministic remaining-mean envelope has integrable death
energy through the endpoint under subcritical retention. -/
-- @node: terminal_death_envelope_intervalIntegrable
lemma terminal_death_envelope_intervalIntegrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (H : ℝ → ℝ)
    (hH : ContinuousOn H (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun t => (2 / P.p a) *
      (H t ^ 2 * P.hazard a t / (survival P a t * retention P a t))) volume 0 1 := by
  have hc := ((hH.pow 2).mul (hP.deathHolder a).1.continuousOn).div
    (modelClass_survival_continuousOn c P hP a) (fun t _ => (Real.exp_pos _).ne')
  simpa only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply, div_div] using
    (subcritical_continuous_invRetention_intervalIntegrable c P hP hk a _ hc).const_mul
      (2 / P.p a)

/-- The terminal envelope vanishes uniformly in all positive sample sizes
in extended expectation. The envelope is compensated before taking limits. -/
-- @node: reference_terminal_death_marks_uniform_small
lemma reference_terminal_death_marks_uniform_small
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (H : ℝ → ℝ) (hH : Measurable H)
    (hc : ContinuousOn H (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in nhdsWithin 1 (Icc (0 : ℝ) 1), ∀ n : ℕ, 0 < n →
      ENNReal.ofReal (n : ℝ) *
        (∫⁻ x : Sample n, ∑ i : Fin n, ENNReal.ofReal
          (if T < (x i).2 ∧ (x i).2 ≤ 1 ∧ (x i).2 < (x i).1 then
            H (x i).2 ^ 2 * inverseRisk (x i).2 x ^ 2 else 0)
          ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
            (armDeathFailureLaw P a) (referenceDeathLaw P a)) < ENNReal.ofReal ε := by
  let f := fun t => (2 / P.p a) *
    (H t ^ 2 * P.hazard a t / (survival P a t * retention P a t))
  have hi := terminal_death_envelope_intervalIntegrable c P hP hk a H hc
  have hlim := studyWindow_integral_tail_tendsto_zero f hi
  filter_upwards [self_mem_nhdsWithin, hlim.eventually (gt_mem_nhds hε)] with T hT hsmall
  intro n hn
  have hsub : uIcc T 1 ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hT.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hT.1 le_rfl
  have hiT := hi.mono_set hsub
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.2] at hiT
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioc T 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hp := (c.pMin_pos.trans_le (hP.treatmentOverlap a)).le
    have hd := c.dMin_pos.le.trans (hP.deathBounds a t ⟨hT.1.trans ht.1.le, ht.2⟩).1
    have hg : 0 ≤ retention P a t := measureReal_nonneg
    dsimp [f]
    exact mul_nonneg (div_nonneg (by norm_num) hp)
      (div_nonneg (mul_nonneg (sq_nonneg _) hd) (mul_nonneg (Real.exp_pos _).le hg))
  have heq : (∫⁻ t in Ioc T 1, ENNReal.ofReal (f t) ∂volume) =
      ENNReal.ofReal (∫ t in T..1, f t) := by
    rw [intervalIntegral.integral_of_le hT.2]
    exact (ofReal_integral_eq_lintegral_ofReal hiT hf0).symm
  apply (reference_terminal_death_marks_lintegral_le c P hP a hn H hH hT.1).trans_lt
  change (∫⁻ t in Ioc T 1, ENNReal.ofReal (f t) ∂volume) < _
  rw [heq]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hsmall

/-- Synthetic stopping preserves zero-safe reciprocal risk at each study time. -/
-- @node: terminal_referenceStoppedSyntheticSample_inverseRisk
lemma terminal_referenceStoppedSyntheticSample_inverseRisk {n : ℕ} (x : Sample n)
    (hfirst0 : ∀ i, 0 ≤ (x i).1) (hfirst1 : ∀ i, (x i).1 ≤ 1)
    (hsecond0 : ∀ i, 0 ≤ (x i).2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    inverseRisk t (referenceStoppedSyntheticSample x) = inverseRisk t x := by
  have hr : Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t
      (referenceStoppedSyntheticSample x) =
      Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t x := by
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskSet
    apply Finset.sum_congr rfl
    intro i _
    have hi := referenceStoppedSyntheticSample_riskIndicator x hfirst0 hfirst1 hsecond0 i ht0 ht1
    unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator at hi
    exact_mod_cast hi
  simp only [inverseRisk, hr]

/-- Terminal death mark sums are invariant under the synthetic stopped map;
only genuine deaths before the censoring coordinate contribute. -/
-- @node: terminal_referenceStoppedSyntheticSample_marks
lemma terminal_referenceStoppedSyntheticSample_marks {n : ℕ} (x : Sample n)
    (hfirst0 : ∀ i, 0 ≤ (x i).1) (hfirst1 : ∀ i, (x i).1 ≤ 1)
    (hsecond0 : ∀ i, 0 ≤ (x i).2) (H : ℝ → ℝ) (T : ℝ) :
    (∑ i : Fin n, ENNReal.ofReal
      (if T < (referenceStoppedSyntheticSample x i).2 ∧
          (referenceStoppedSyntheticSample x i).2 ≤ 1 ∧
          (referenceStoppedSyntheticSample x i).2 < (referenceStoppedSyntheticSample x i).1 then
        H (referenceStoppedSyntheticSample x i).2 ^ 2 *
          inverseRisk (referenceStoppedSyntheticSample x i).2 (referenceStoppedSyntheticSample x) ^ 2
      else 0)) =
    ∑ i : Fin n, ENNReal.ofReal
      (if T < (x i).2 ∧ (x i).2 ≤ 1 ∧ (x i).2 < (x i).1 then
        H (x i).2 ^ 2 * inverseRisk (x i).2 x ^ 2 else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  by_cases hd : (x i).2 < (x i).1
  · have hd1 : (x i).2 ≤ 1 := hd.le.trans (hfirst1 i)
    have he : referenceStoppedSyntheticSample x i = ((x i).2 + 1, (x i).2) := by
      simp [referenceStoppedSyntheticSample, stoppedSyntheticDeathPair, hd,
        min_eq_left hd1, min_eq_right hd.le]
    rw [he]
    simp only [hd, hd1, and_true, show (x i).2 < (x i).2 + 1 by linarith]
    rw [terminal_referenceStoppedSyntheticSample_inverseRisk x hfirst0 hfirst1 hsecond0
      (hsecond0 i) hd1]
  · have hfmin : (x i).1 ≤ min (x i).2 1 := le_min (le_of_not_gt hd) (hfirst1 i)
    have he : referenceStoppedSyntheticSample x i = ((x i).1, (x i).1 + 1) := by
      simp [referenceStoppedSyntheticSample, stoppedSyntheticDeathPair, hd,
        min_eq_left hfmin, not_lt_of_ge (hfirst1 i)]
    rw [he]
    simp [hd, show ¬(x i).1 + 1 < (x i).1 by linarith]

end DeathCP
/-- The paper's actual terminal optional variation has exactly the reference
product-sample extended expectation. -/
-- @node: tailDeathVariation_lintegral_eq_reference
lemma tailDeathVariation_lintegral_eq_reference
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) (H : ℝ → ℝ) (hH : Measurable H) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ s : Fin n → ObsHistory, ENNReal.ofReal (tailDeathVariation a s T 1 H)
      ∂sampleLaw P n) = ENNReal.ofReal (n : ℝ) *
      (∫⁻ x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n,
        ∑ i : Fin n, ENNReal.ofReal
          (if T < (x i).2 ∧ (x i).2 ≤ 1 ∧ (x i).2 < (x i).1 then
            H (x i).2 ^ 2 * Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk (x i).2 x ^ 2
          else 0)
        ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a)) := by
  classical
  let F := fun x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n =>
    ∑ i : Fin n, ENNReal.ofReal
      (if T < (x i).2 ∧ (x i).2 ≤ 1 ∧ (x i).2 < (x i).1 then
        H (x i).2 ^ 2 * Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk (x i).2 x ^ 2
      else 0)
  have hF : Measurable F := by
    apply Finset.measurable_fun_sum
    intro i _
    apply Measurable.ennreal_ofReal
    apply Measurable.ite
    · have hfst : Measurable (fun x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n =>
          (x i).1) := by fun_prop
      have hsnd : Measurable (fun x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n =>
          (x i).2) := by fun_prop
      exact (measurableSet_lt measurable_const hsnd).inter
        ((measurableSet_le hsnd measurable_const).inter (measurableSet_lt hsnd hfst))
    · exact ((hH.comp (by fun_prop)).pow_const 2).mul
        ((Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
          ((show Measurable (fun x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n =>
            (x i).2) by fun_prop).prodMk measurable_id)).pow_const 2)
    · exact measurable_const
  have hm : Measurable (observedDeathSample a (n := n)) := by
    exact measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have he (s : Fin n → ObsHistory) : ENNReal.ofReal (tailDeathVariation a s T 1 H) =
      ENNReal.ofReal (n : ℝ) * F (observedDeathSample a s) := by
    rw [tailDeathVariation_eq_observedDeathSample_marks a s hT H,
      ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_sum_of_nonneg]
    intro i _
    split_ifs <;> positivity
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_map hF hm,
    observedDeathSample_map_eq_reference P hP.deathHazard hP.randomAssignment
      hP.independentCensoring a,
    lintegral_map hF measurable_referenceStoppedSyntheticSample]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [DeathCP.referenceSample_regular_ae c P hP a n] with x hx
  exact DeathCP.terminal_referenceStoppedSyntheticSample_marks x hx.1 hx.2.1 hx.2.2 H T

/-- The observed deterministic terminal death envelope vanishes in extended
expectation, uniformly over all positive sample sizes. -/
-- @node: tailDeathVariation_envelope_lintegral_uniform_small
lemma tailDeathVariation_envelope_lintegral_uniform_small
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in nhdsWithin 1 (Icc (0 : ℝ) 1), ∀ n : ℕ, 0 < n →
      (∫⁻ s : Fin n → ObsHistory,
        ENNReal.ofReal (tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t)))
        ∂sampleLaw P n) < ENNReal.ofReal ε := by
  have h := DeathCP.reference_terminal_death_marks_uniform_small c P hP hk a
    (fun t => c.lambdaMax * (1 - t)) (by fun_prop) (by fun_prop) hε
  filter_upwards [self_mem_nhdsWithin, h] with T hT hs
  intro n hn
  rw [tailDeathVariation_lintegral_eq_reference c P hP a n _ (by fun_prop) hT.1]
  exact hs n hn

/-- Deterministic terminal death variation is measurable in the observed sample. -/
-- @node: measurable_tailDeathVariation
@[fun_prop]
lemma measurable_tailDeathVariation (a : Arm) (n : ℕ) (T U : ℝ)
    (H : ℝ → ℝ) (hH : Measurable H) :
    Measurable (fun s : Fin n → ObsHistory => tailDeathVariation a s T U H) := by
  unfold tailDeathVariation
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum
  intro i _
  apply Measurable.ite
  · have ht : Measurable (fun s : Fin n → ObsHistory => (s i).treatment) := by fun_prop
    have hd : Measurable (fun s : Fin n → ObsHistory => (s i).deathInd) := by fun_prop
    have he : Measurable (fun s : Fin n → ObsHistory => (s i).exit) := by fun_prop
    exact (measurableSet_eq_fun ht measurable_const).inter
      ((measurableSet_eq_fun hd measurable_const).inter
        ((measurableSet_lt measurable_const he).inter (measurableSet_le he measurable_const)))
  · fun_prop
  · exact measurable_const

/-- The bounded remaining-horizon envelope gives integrability of the actual
finite death sum at every sample size. -/
-- @node: tailDeathVariation_envelope_integrable
lemma tailDeathVariation_envelope_integrable (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun s : Fin n → ObsHistory =>
      tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t))) (sampleLaw P n) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply Integrable.of_bound (by fun_prop) ((n : ℝ) ^ 2 * c.lambdaMax ^ 2)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (tailDeathVariation_nonneg _ _ _ _ _)]
  have hL : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  unfold tailDeathVariation
  calc
    _ ≤ (n : ℝ) * ∑ _i : Fin n, c.lambdaMax ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · have hu0 : 0 ≤ (s i).exit := hT.trans hi.2.2.1.le
        have hu1 : (s i).exit ≤ 1 := hi.2.2.2
        have hb : 0 ≤ c.lambdaMax * (1 - (s i).exit) ∧
            c.lambdaMax * (1 - (s i).exit) ≤ c.lambdaMax := by
          constructor <;> nlinarith
        have hpow := pow_le_pow_left₀ hb.1 hb.2 2
        have hr := recurrence_invRisk_mem_Icc a s (s i).exit
        have hr2 : invRisk a s (s i).exit ^ 2 ≤ 1 := by
          nlinarith [hr.1, hr.2, sq_nonneg (1 - invRisk a s (s i).exit)]
        exact (mul_le_mul_of_nonneg_left hr2 (sq_nonneg _)).trans (by simpa using hpow)
      · positivity
    _ = _ := by simp; ring

/-- The actual terminal envelope has uniformly vanishing first moment,
with no independence assertion between the marks and empirical risk. -/
-- @node: tailDeathVariation_envelope_integral_uniform_small
lemma tailDeathVariation_envelope_integral_uniform_small
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in nhdsWithin 1 (Icc (0 : ℝ) 1), ∀ n : ℕ, 0 < n →
      (∫ s : Fin n → ObsHistory,
        tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t))
        ∂sampleLaw P n) < ε := by
  filter_upwards [self_mem_nhdsWithin,
    tailDeathVariation_envelope_lintegral_uniform_small c P hP hk a hε] with T hT hs
  intro n hn
  have hi := tailDeathVariation_envelope_integrable c P a n hT.1
  have hnn : ∀ᵐ s ∂sampleLaw P n,
      0 ≤ tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t)) := Eventually.of_forall (fun s : Fin n → ObsHistory =>
    tailDeathVariation_nonneg a s T 1 (fun t => c.lambdaMax * (1 - t)))
  have hb := hs n hn
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn] at hb
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hb

/-- Markov turns terminal-envelope expectation control into uniformly
vanishing tail probabilities as the localization horizon approaches one. -/
-- @node: tailDeathVariation_envelope_probability_uniform_small
lemma tailDeathVariation_envelope_probability_uniform_small
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ T in nhdsWithin 1 (Icc (0 : ℝ) 1), ∀ n : ℕ, 0 < n →
      (sampleLaw P n).real {s |
        ε < tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t))} < η := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  filter_upwards [self_mem_nhdsWithin,
    tailDeathVariation_envelope_integral_uniform_small c P hP hk a (mul_pos hη hε)] with T hT hs
  intro n hn
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s : Fin n → ObsHistory =>
      tailDeathVariation_nonneg a s T 1 (fun t => c.lambdaMax * (1 - t))))
    (tailDeathVariation_envelope_integrable c P a n hT.1) ε
  apply (mul_lt_mul_iff_right₀ hε).mp
  rw [mul_comm ε, mul_comm ε]
  apply (mul_le_mul_of_nonneg_right (measureReal_mono (show
    {s : Fin n → ObsHistory | ε < tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t))} ⊆
    {s | ε ≤ tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t))} from
      fun s (hs : ε < tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t))) => hs.le)
      (by finiteness)) hε.le).trans_lt
  rw [mul_comm] at hm
  exact hm.trans_lt (hs n hn)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
