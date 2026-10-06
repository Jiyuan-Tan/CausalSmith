module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LocalizedRecurrenceVariation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceSubcriticalRisk

/-!
# First moments for recurrence optional-variation tails

Roadmap (31)--(33): compensation conditional on the entire exposure array
centers the recurrence variation score. For nonnegative coefficients its
absolute first moment is at most twice its intensity mass. This permits
terminal-tail control without a bounded endpoint oracle or independence
between the empirical KM and inverse-risk factors.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Product exposure energy also supplies conditional centering of the score. -/
-- @node: recurrenceJointExposureScore_latent_mean_zero
lemma recurrenceJointExposureScore_latent_mean_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    (f : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      f p.1 i p.2))
    (hprod : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, f p.1 i p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a))) :
    Integrable (fun z : Fin n → LatentSubject => recurrenceJointExposureScore P a n f
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)) (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject, recurrenceJointExposureScore P a n f
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a) ∂Measure.pi (fun _ : Fin n => P.latent)) = 0 := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  obtain ⟨hi, he⟩ := recurrenceJointExposure_energy_conditions P a n f hf hprod
  exact recurrence_latent_exposure_mean_zero_of_integrable_sq P
    hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n f
    (fun e i => (hf i).comp (measurable_const.prodMk measurable_id)) hi
    (measurable_recurrenceJointExposureScore P a n f hf) he

/-- A bounded exposure coefficient has integrable product energy. The bound
is used for integrability only, allowing it to depend on sample size. -/
-- @node: recurrenceJointExposure_bounded_energy_integrable
lemma recurrenceJointExposure_bounded_energy_integrable
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (a : Arm) (n : ℕ)
    (f : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      f p.1 i p.2)) (B : ℝ) (hb : ∀ e i t, |f e i t| ≤ B) :
    Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, f p.1 i p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hPoisson a).2.2.1
  apply Integrable.of_bound
    (Finset.measurable_sum _ (fun i _ => (hf i).pow_const 2)).aestronglyMeasurable
    ((n : ℝ) * B ^ 2)
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  calc
    _ ≤ ∑ _i : Fin n, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb p.1 i p.2) 2
    _ = _ := by simp

/-- Conditional compensation bounds the absolute score of a nonnegative
coefficient by twice its expected compensator. All coefficient dependence
remains inside that expectation. -/
-- @node: recurrenceJointExposureScore_mean_abs_le_twice_compensator
lemma recurrenceJointExposureScore_mean_abs_le_twice_compensator
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    (f : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      f p.1 i p.2)) (B : ℝ) (hb : ∀ e i t, |f e i t| ≤ B)
    (hf0 : ∀ e i t, 0 ≤ f e i t) :
    (∫ z : Fin n → LatentSubject, |recurrenceJointExposureScore P a n f
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)| ∂Measure.pi (fun _ : Fin n => P.latent)) ≤
    2 * (∫ z : Fin n → LatentSubject, (∑ i : Fin n,
      ∫ t, f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
        ∂recurrenceIntensity P a) ∂Measure.pi (fun _ : Fin n => P.latent)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  let μ := Measure.pi (fun _ : Fin n => P.latent)
  let E := fun z : Fin n → LatentSubject =>
    fun j => ((z j).treatment, ((z j).death a, (z j).censor a))
  let F := fun z : Fin n → LatentSubject => recurrenceJointExposureScore P a n f
    (E z) (fun j => (z j).recur a)
  let D := fun z : Fin n → LatentSubject =>
    ∑ i : Fin n, ∫ t, f (E z) i t ∂recurrenceIntensity P a
  obtain ⟨hi, he⟩ := recurrenceJointExposureScore_latent_mean_zero c P hP a n f hf
    (recurrenceJointExposure_bounded_energy_integrable P hP.poissonRecurrence a n f hf B hb)
  have hD : Integrable D μ := by
    apply Integrable.of_bound (by
      dsimp [D, E]
      apply Measurable.aestronglyMeasurable
      apply Finset.measurable_sum _
      intro i _
      exact ((hf i).stronglyMeasurable.integral_prod_right'.measurable.comp
        (show Measurable E by fun_prop)))
      ((n : ℝ) * (B * (recurrenceIntensity P a).real univ))
    filter_upwards [] with z
    dsimp [D]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ =>
      integral_nonneg (hf0 (E z) i)))]
    calc
      _ ≤ ∑ _i : Fin n, B * (recurrenceIntensity P a).real univ := by
        apply Finset.sum_le_sum
        intro i _
        have hfi : Integrable (f (E z) i) (recurrenceIntensity P a) :=
          Integrable.of_bound
            ((hf i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
            (Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hb (E z) i t))
        calc
          _ ≤ ∫ _t, B ∂recurrenceIntensity P a := integral_mono hfi (integrable_const _)
            (fun t => (le_abs_self _).trans (hb (E z) i t))
          _ = _ := by simp [mul_comm]
      _ = _ := by simp
  have hpoint (z : Fin n → LatentSubject) : |F z| ≤ F z + 2 * D z := by
    have hnonneg : 0 ≤ F z + D z := by
      dsimp [F, D, recurrenceJointExposureScore]
      rw [Finset.sum_sub_distrib]
      simp only [sub_add_cancel]
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => hf0 _ _ _))
    have hd : 0 ≤ D z := Finset.sum_nonneg (fun i _ => integral_nonneg (hf0 _ i))
    rw [abs_le]
    constructor <;> linarith
  calc
    _ ≤ ∫ z, F z + 2 * D z ∂μ := integral_mono hi.abs
      (hi.add (hD.const_mul 2)) hpoint
    _ = _ := by rw [integral_add hi (hD.const_mul 2), integral_const_mul, he, zero_add]

/-- The terminal coefficient of the actual recurrence optional variation. -/
-- @node: terminalRecurrenceVariationWeight
noncomputable def terminalRecurrenceVariationWeight (c : ClassConstants) (a : Arm)
    {n : ℕ} (T : ℝ) (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) : ℝ :=
  if T < t ∧ t ≤ 1 then (n : ℝ) *
    recurrenceSubjectWeight c 0 a (fun j => recurrenceExposureHistory (e j)) i t ^ 2
  else 0

/-- Terminal variation coefficients are jointly exposure/time measurable. -/
-- @node: measurable_terminalRecurrenceVariationWeight
@[fun_prop] lemma measurable_terminalRecurrenceVariationWeight
    (c : ClassConstants) (a : Arm) {n : ℕ} (T : ℝ) (i : Fin n) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      terminalRecurrenceVariationWeight c a T p.1 i p.2) := by
  unfold terminalRecurrenceVariationWeight
  apply Measurable.ite ?_ (by fun_prop) measurable_const
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_const)

/-- The terminal coefficient is nonnegative, as required by Campbell's
first-moment tail bound. -/
-- @node: terminalRecurrenceVariationWeight_nonneg
lemma terminalRecurrenceVariationWeight_nonneg (c : ClassConstants) (a : Arm)
    {n : ℕ} (T : ℝ) (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) :
    0 ≤ terminalRecurrenceVariationWeight c a T e i t := by
  unfold terminalRecurrenceVariationWeight
  split_ifs <;> positivity

/-- A finite-sample envelope gives integrability, without bounding the
endpoint oracle or using this coarse envelope in the asymptotic tail rate. -/
-- @node: terminalRecurrenceVariationWeight_abs_le
lemma terminalRecurrenceVariationWeight_abs_le (c : ClassConstants) (a : Arm)
    {n : ℕ} (T : ℝ) (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) :
    |terminalRecurrenceVariationWeight c a T e i t| ≤ (n : ℝ) * weightEnvelope c ^ 2 := by
  unfold terminalRecurrenceVariationWeight
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (recurrenceSubjectWeight_abs_le_of_nonneg c (by norm_num) a _ i t) 2
  · simp only [abs_zero]; positivity

/-- The actual terminal variation score admits a first-moment bound by its
conditional intensity integral. This is the compensation step of (33), with
neither independence of KM and risk nor predictability of future marks. -/
-- @node: terminalRecurrenceVariationScore_mean_abs_le_twice_compensator
lemma terminalRecurrenceVariationScore_mean_abs_le_twice_compensator
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) (T : ℝ) :
    (∫ z : Fin n → LatentSubject, |recurrenceJointExposureScore P a n
      (terminalRecurrenceVariationWeight c a T)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)| ∂Measure.pi (fun _ : Fin n => P.latent)) ≤
    2 * (∫ z : Fin n → LatentSubject, (∑ i : Fin n,
      ∫ t, terminalRecurrenceVariationWeight c a T
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
        ∂recurrenceIntensity P a) ∂Measure.pi (fun _ : Fin n => P.latent)) := by
  exact recurrenceJointExposureScore_mean_abs_le_twice_compensator c P hP a n
    (terminalRecurrenceVariationWeight c a T)
    (measurable_terminalRecurrenceVariationWeight c a T)
    ((n : ℝ) * weightEnvelope c ^ 2)
    (terminalRecurrenceVariationWeight_abs_le c a T)
    (terminalRecurrenceVariationWeight_nonneg c a T)

/-- The terminal intensity restriction is precisely the Lebesgue interval
integral, including totalized coefficients. -/
-- @node: recurrenceIntensity_integral_terminal
lemma recurrenceIntensity_integral_terminal (P : SubjectLaw)
    (hP : PoissonRecurrence P) (a : Arm) (f : ℝ → ℝ) {T : ℝ}
    (hT : T ∈ Icc (0 : ℝ) 1) :
    (∫ t, (if T < t ∧ t ≤ 1 then f t else 0) ∂recurrenceIntensity P a) =
      ∫ t in T..1, f t * P.lam a t := by
  unfold recurrenceIntensity
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hP a).1.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (∫ t in Ioc (0 : ℝ) 1,
      (ENNReal.ofReal (P.lam a t)).toReal • (if T < t ∧ t ≤ 1 then f t else 0)) =
      ∫ t in Ioc (0 : ℝ) 1, (Ioc T 1).indicator (fun t => f t * P.lam a t) t := by
    apply integral_congr_ae
    filter_upwards [(hP a).2.1] with t ht
    simp only [ENNReal.toReal_ofReal ht, smul_eq_mul, indicator_apply, mem_Ioc]
    split_ifs <;> ring
  rw [heq, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hset : Ioc T 1 ∩ Ioc (0 : ℝ) 1 = Ioc T 1 :=
    inter_eq_left.mpr (Ioc_subset_Ioc_left hT.1)
  rw [hset, intervalIntegral.integral_of_le hT.2]

/-- The conditional terminal compensator is the actual KM/inverse-risk
time integral. Summing subject weights retains exactly one inverse risk. -/
-- @node: terminalRecurrenceVariationWeight_compensator_eq
lemma terminalRecurrenceVariationWeight_compensator_eq
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1)
    (e : Fin n → Arm × (ℝ × ENNReal)) :
    (∑ i : Fin n, ∫ t, terminalRecurrenceVariationWeight c a T e i t
      ∂recurrenceIntensity P a) =
      (n : ℝ) * ∫ t in T..1,
        deathKMLeft a (fun j => recurrenceExposureHistory (e j)) t ^ 2 *
        invRisk a (fun j => recurrenceExposureHistory (e j)) t * P.lam a t := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  have hi (i : Fin n) : Integrable (fun t => terminalRecurrenceVariationWeight c a T e i t)
      (recurrenceIntensity P a) := by
    apply Integrable.of_bound
      ((measurable_terminalRecurrenceVariationWeight c a T i).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ((n : ℝ) * weightEnvelope c ^ 2)
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs, Function.comp_def, id_eq] using terminalRecurrenceVariationWeight_abs_le c a T e i t
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  have heq (t : ℝ) : (∑ i : Fin n, terminalRecurrenceVariationWeight c a T e i t) =
      if T < t ∧ t ≤ 1 then (n : ℝ) *
        deathKMLeft a (fun j => recurrenceExposureHistory (e j)) t ^ 2 *
        invRisk a (fun j => recurrenceExposureHistory (e j)) t else 0 := by
    unfold terminalRecurrenceVariationWeight
    split_ifs
    · rw [← Finset.mul_sum, recurrenceSubjectWeight_sum_sq]
      simp [continuationWeight, mul_assoc]
    · simp only [Finset.sum_const_zero]
  simp_rw [heq]
  rw [recurrenceIntensity_integral_terminal P hP.poissonRecurrence a _ hT]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]

/-- The marginal scaled inverse-risk density has the integrable envelope
needed for the terminal first-moment bound in (33). -/
-- @node: observed_scaledInvRisk_mean_le_invRetention
lemma observed_scaledInvRisk_mean_le_invRetention
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫ s : Fin n → ObsHistory, (n : ℝ) * invRisk a s t ∂sampleLaw P n) ≤
      (2 * Real.exp c.dMax / c.pMin) * (retention P a t)⁻¹ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 < P.p a := c.pMin_pos.trans_le (hP.treatmentOverlap a)
  have hg : 0 < retention P a t := retention_pos_of_modelClass c P hP a t ht0.le ht1
  have hs : 0 < survival P a t := Real.exp_pos _
  have hslo := (survival_bounds_of_deathBounds c P hP.deathBounds a
    ⟨ht0.le, ht1.le⟩).1
  rw [integral_const_mul]
  calc
    _ ≤ (n : ℝ) * (2 / ((n : ℝ) * (P.p a * retention P a t * survival P a t))) :=
      mul_le_mul_of_nonneg_left
        (recurrence_integral_invRisk_le_arm_tail c P hP a hn ht0 ht1) hnR.le
    _ ≤ (n : ℝ) * (2 / ((n : ℝ) *
        (c.pMin * retention P a t * Real.exp (-c.dMax)))) := by
      gcongr
      · exact mul_pos hnR (mul_pos (mul_pos c.pMin_pos hg) (Real.exp_pos _))
      · exact hP.treatmentOverlap a
    _ = _ := by rw [Real.exp_neg]; field_simp

/-- Time-integrated expected scaled inverse risk has a uniform terminal
bound. The exact endpoint integrability comes from the subcritical model. -/
-- @node: subcritical_scaledInvRisk_expected_tail_le
lemma subcritical_scaledInvRisk_expected_tail_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) :
    (∫ t in T..1, ∫ s : Fin n → ObsHistory,
      (n : ℝ) * invRisk a s t ∂sampleLaw P n) ≤
      (2 * Real.exp c.dMax / c.pMin) * ∫ t in T..1, (retention P a t)⁻¹ := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let r := fun t => ∫ s : Fin n → ObsHistory, (n : ℝ) * invRisk a s t ∂sampleLaw P n
  have hm : Measurable r :=
    (measurable_const.mul (measurable_recurrenceInvRisk_joint a)).stronglyMeasurable.integral_prod_left'.measurable
  have hb (t : ℝ) : ‖r t‖ ≤ (n : ℝ) := by
    have hi : Integrable (fun s : Fin n → ObsHistory => (n : ℝ) * invRisk a s t)
        (sampleLaw P n) := Integrable.of_bound (by fun_prop) n
      (Eventually.of_forall (fun s => by
        rw [Real.norm_of_nonneg (DeathCP.scaledInvRisk_mem_Icc a s t).1]
        exact (DeathCP.scaledInvRisk_mem_Icc a s t).2))
    rw [Real.norm_of_nonneg (integral_nonneg (fun s =>
      (DeathCP.scaledInvRisk_mem_Icc a s t).1))]
    simpa using integral_mono hi (integrable_const (n : ℝ))
      (fun s => (DeathCP.scaledInvRisk_mem_Icc a s t).2)
  have hi : IntegrableOn r (Ioo T 1) := Integrable.of_bound
    hm.aestronglyMeasurable.restrict n (Eventually.of_forall hb)
  have hg : IntegrableOn (fun t => (retention P a t)⁻¹) (Ioo T 1) := by
    have hg := inv_retention_intervalIntegrable_subcritical c P hP hk a
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hg
    exact hg.mono_set (fun t ht => ⟨hT.1.trans ht.1.le, ht.2.le⟩)
  rw [intervalIntegral.integral_of_le hT.2, intervalIntegral.integral_of_le hT.2,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  apply integral_mono_ae hi (hg.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact observed_scaledInvRisk_mean_le_invRetention c P hP a hn
    (hT.1.trans_lt ht.1) ht.2

/-- The terminal first-moment envelope vanishes as the localization horizon
approaches one, uniformly in the positive sample size. -/
-- @node: subcritical_scaledInvRisk_tail_envelope_tendsto_zero
lemma subcritical_scaledInvRisk_tail_envelope_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) :
    Tendsto (fun T : ℝ => (2 * Real.exp c.dMax / c.pMin) *
      ∫ t in T..1, (retention P a t)⁻¹)
      (nhdsWithin 1 (Icc (0 : ℝ) 1)) (nhds 0) := by
  simpa only [mul_zero] using
    (studyWindow_integral_tail_tendsto_zero _
      (inv_retention_intervalIntegrable_subcritical c P hP hk a)).const_mul
        (2 * Real.exp c.dMax / c.pMin)

/-- The terminal score's conditional compensator has a uniform integrable
tail envelope. Tonelli/Fubini is applied before the exact binomial risk bound;
the empirical KM factor is bounded pathwise, never factorized. -/
-- @node: terminalRecurrenceVariation_compensator_mean_le
lemma terminalRecurrenceVariation_compensator_mean_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) :
    (∫ z : Fin n → LatentSubject, (∑ i : Fin n,
      ∫ t, terminalRecurrenceVariationWeight c a T
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
        ∂recurrenceIntensity P a) ∂Measure.pi (fun _ : Fin n => P.latent)) ≤
      c.lambdaMax * (2 * Real.exp c.dMax / c.pMin) *
        ∫ t in T..1, (retention P a t)⁻¹ := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  let μ := Measure.pi (fun _ : Fin n => P.latent)
  let E := fun z : Fin n → LatentSubject =>
    fun j => ((z j).treatment, ((z j).death a, (z j).censor a))
  let s := fun z : Fin n → LatentSubject => fun j => recurrenceExposureHistory (E z j)
  let U := fun (z : Fin n → LatentSubject) t =>
    if T < t ∧ t ≤ 1 then (n : ℝ) * invRisk a (s z) t else 0
  have hm : Measurable (fun p : (Fin n → LatentSubject) × ℝ => U p.1 p.2) := by
    dsimp [U, s, E]
    apply Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) (by fun_prop) measurable_const
  have hb (z : Fin n → LatentSubject) (t : ℝ) : ‖U z t‖ ≤ (n : ℝ) := by
    dsimp [U]
    split_ifs
    · rw [abs_of_nonneg (DeathCP.scaledInvRisk_mem_Icc a (s z) t).1]
      exact (DeathCP.scaledInvRisk_mem_Icc a (s z) t).2
    · simp
  have hp : Integrable (fun p : (Fin n → LatentSubject) × ℝ => U p.1 p.2)
      (μ.prod (recurrenceIntensity P a)) := Integrable.of_bound hm.aestronglyMeasurable n
        (Eventually.of_forall (fun p => hb p.1 p.2))
  have hslice (z : Fin n → LatentSubject) : Integrable (U z) (recurrenceIntensity P a) :=
    Integrable.of_bound (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable n
      (Eventually.of_forall (hb z))
  have hpoint (z : Fin n → LatentSubject) :
      (∑ i : Fin n, ∫ t, terminalRecurrenceVariationWeight c a T (E z) i t
        ∂recurrenceIntensity P a) ≤ ∫ t, U z t ∂recurrenceIntensity P a := by
    have hi (i : Fin n) : Integrable (fun t => terminalRecurrenceVariationWeight c a T (E z) i t)
        (recurrenceIntensity P a) := Integrable.of_bound
      ((measurable_terminalRecurrenceVariationWeight c a T i).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ((n : ℝ) * weightEnvelope c ^ 2) (Eventually.of_forall (fun t => by
        simpa only [Real.norm_eq_abs, Function.comp_def, id_eq] using
          terminalRecurrenceVariationWeight_abs_le c a T (E z) i t))
    rw [← integral_finsetSum _ (fun i _ => hi i)]
    apply integral_mono (integrable_finsetSum _ (fun i _ => hi i)) (hslice z)
    intro t
    dsimp [U]
    unfold terminalRecurrenceVariationWeight
    split_ifs
    · rw [← Finset.mul_sum, recurrenceSubjectWeight_sum_sq]
      simp only [continuationWeight, ↓reduceIte, one_pow, one_mul]
      have hkm := deathKMLeft_mem_Icc a (s z) t
      have hkm2 : deathKMLeft a (s z) t ^ 2 ≤ 1 := by nlinarith [hkm.1, hkm.2]
      simpa only [one_mul, mul_one, mul_assoc, s] using
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hkm2 (recurrence_invRisk_mem_Icc a (s z) t).1)
          (Nat.cast_nonneg n)
    · simp
  have ht (t : ℝ) : (∫ z, U z t ∂μ) =
      if T < t ∧ t ≤ 1 then
        (∫ o : Fin n → ObsHistory, (n : ℝ) * invRisk a o t ∂sampleLaw P n) else 0 := by
    dsimp [U]
    split_ifs
    · rw [recurrence_sampleLaw_eq_latent_map, integral_map
        (show Measurable (fun z : Fin n → LatentSubject => fun j => observe (z j)) by fun_prop).aemeasurable
        (show AEStronglyMeasurable (fun o : Fin n → ObsHistory => (n : ℝ) * invRisk a o t)
          ((Measure.pi (fun _ : Fin n => P.latent)).map (fun z => fun j => observe (z j))) by fun_prop)]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [invRisk, riskSet_observe_eq_recurrenceExposureHistory, s, E]
    · simp
  have hi : IntegrableOn (fun t => ∫ o : Fin n → ObsHistory,
      (n : ℝ) * invRisk a o t ∂sampleLaw P n) (Ioc T 1) := by
    apply Integrable.of_bound
      (measurable_const.mul (measurable_recurrenceInvRisk_joint a)).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable.restrict
      n
    filter_upwards [] with t
    change ‖∫ o : Fin n → ObsHistory, (n : ℝ) * invRisk a o t ∂sampleLaw P n‖ ≤ (n : ℝ)
    rw [Real.norm_of_nonneg (integral_nonneg (fun o => (DeathCP.scaledInvRisk_mem_Icc a o t).1))]
    have hj : Integrable (fun o : Fin n → ObsHistory => (n : ℝ) * invRisk a o t)
        (sampleLaw P n) := Integrable.of_bound (by fun_prop) n
      (Eventually.of_forall (fun o => by
        rw [Real.norm_of_nonneg (DeathCP.scaledInvRisk_mem_Icc a o t).1]
        exact (DeathCP.scaledInvRisk_mem_Icc a o t).2))
    simpa using integral_mono hj (integrable_const (n : ℝ))
      (fun o => (DeathCP.scaledInvRisk_mem_Icc a o t).2)
  calc
    _ ≤ ∫ z, (∫ t, U z t ∂recurrenceIntensity P a) ∂μ :=
      integral_mono_of_nonneg
        (Eventually.of_forall (fun z => Finset.sum_nonneg (fun i _ =>
          integral_nonneg (terminalRecurrenceVariationWeight_nonneg c a T (E z) i))))
        hp.integral_prod_left (Eventually.of_forall hpoint)
    _ = ∫ t in T..1, (∫ o : Fin n → ObsHistory,
        (n : ℝ) * invRisk a o t ∂sampleLaw P n) * P.lam a t := by
      rw [integral_integral_swap hp]
      simp_rw [ht]
      exact recurrenceIntensity_integral_terminal P hP.poissonRecurrence a _ hT
    _ ≤ c.lambdaMax * ∫ t in T..1, ∫ o : Fin n → ObsHistory,
        (n : ℝ) * invRisk a o t ∂sampleLaw P n := by
      rw [intervalIntegral.integral_of_le hT.2, intervalIntegral.integral_of_le hT.2,
        ← integral_const_mul]
      apply integral_mono_of_nonneg
        (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            exact mul_nonneg (integral_nonneg (fun o => (DeathCP.scaledInvRisk_mem_Icc a o t).1))
              (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ⟨hT.1.trans ht.1.le, ht.2⟩).1))
        (hi.const_mul c.lambdaMax)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (hP.recurrenceBounds a t ⟨hT.1.trans ht.1.le, ht.2⟩).2
        (integral_nonneg (fun o => (DeathCP.scaledInvRisk_mem_Icc a o t).1))
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (subcritical_scaledInvRisk_expected_tail_le c P hP hk a hn hT)
        (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)

/-- The terminal compensated variation has an explicit uniform first-moment
bound using the subcritical inverse-retention tail, rather than a fourth
moment of an endpoint oracle coefficient. -/
-- @node: terminalRecurrenceVariationScore_mean_abs_le
lemma terminalRecurrenceVariationScore_mean_abs_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) :
    (∫ z : Fin n → LatentSubject, |recurrenceJointExposureScore P a n
      (terminalRecurrenceVariationWeight c a T)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)| ∂Measure.pi (fun _ : Fin n => P.latent)) ≤
      (4 * c.lambdaMax * Real.exp c.dMax / c.pMin) *
        ∫ t in T..1, (retention P a t)⁻¹ := by
  apply (terminalRecurrenceVariationScore_mean_abs_le_twice_compensator c P hP a n T).trans
  have h := mul_le_mul_of_nonneg_left
    (terminalRecurrenceVariation_compensator_mean_le c P hP hk a hn hT)
    (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1 <;> ring

/-- Markov's inequality turns the conditional-compensation tail bound into
an actual probability bound, uniform over all positive sample sizes. -/
-- @node: terminalRecurrenceVariationScore_probability_le
lemma terminalRecurrenceVariationScore_probability_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |recurrenceJointExposureScore P a n (terminalRecurrenceVariationWeight c a T)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|} ≤
      ((4 * c.lambdaMax * Real.exp c.dMax / c.pMin) *
        ∫ t in T..1, (retention P a t)⁻¹) / ε := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let F := fun z : Fin n → LatentSubject => recurrenceJointExposureScore P a n
    (terminalRecurrenceVariationWeight c a T)
    (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
    (fun j => (z j).recur a)
  have hi := (recurrenceJointExposureScore_latent_mean_zero c P hP a n
    (terminalRecurrenceVariationWeight c a T)
    (measurable_terminalRecurrenceVariationWeight c a T)
    (recurrenceJointExposure_bounded_energy_integrable P hP.poissonRecurrence a n
      (terminalRecurrenceVariationWeight c a T)
      (measurable_terminalRecurrenceVariationWeight c a T)
      ((n : ℝ) * weightEnvelope c ^ 2)
      (terminalRecurrenceVariationWeight_abs_le c a T))).1.abs
  have hm := mul_meas_ge_le_integral_of_nonneg
    (f := fun z => |F z|) (Eventually.of_forall (fun z => abs_nonneg _)) hi ε
  have hsub : (Measure.pi (fun _ : Fin n => P.latent)).real {z | ε < |F z|} ≤
      (Measure.pi (fun _ : Fin n => P.latent)).real {z | ε ≤ |F z|} :=
    measureReal_mono (fun z (hz : ε < |F z|) => hz.le) (by finiteness)
  apply (le_div_iff₀ hε).2
  exact ((mul_le_mul_of_nonneg_right hsub hε.le).trans
    (by simpa only [mul_comm] using hm)).trans
      (terminalRecurrenceVariationScore_mean_abs_le c P hP hk a hn hT)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
