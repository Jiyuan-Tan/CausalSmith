module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceVariationFirstMoment
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FullHorizonDeathPlugin
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalEmpiricalCompensator

/-!
# Full-horizon recurrence optional-variation remainder

Roadmap (31)--(34): split the compensated recurrence variation at a strict
horizon. The localized score vanishes in probability and conditional
compensation controls its terminal tail by the integrable inverse retention.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: measurable_fixedRecurrenceVariationWeight
@[fun_prop] lemma measurable_fixedRecurrenceVariationWeight
    (c : ClassConstants) (a : Arm) {n : ℕ} (T : ℝ) (i : Fin n) :
    Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      fixedRecurrenceVariationWeight c a T p.1 i p.2) := by
  unfold fixedRecurrenceVariationWeight
  exact Measurable.ite (measurableSet_le measurable_snd measurable_const)
    (by fun_prop) measurable_const

-- @node: fixedRecurrenceVariationWeight_abs_le
lemma fixedRecurrenceVariationWeight_abs_le
    (c : ClassConstants) (a : Arm) {n : ℕ} (T : ℝ)
    (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) :
    |fixedRecurrenceVariationWeight c a T e i t| ≤
      (n : ℝ) * weightEnvelope c ^ 2 := by
  unfold fixedRecurrenceVariationWeight
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (recurrenceSubjectWeight_abs_le_of_nonneg c (by norm_num) a _ i t) 2
  · simp only [abs_zero]; positivity

-- @node: fixedRecurrenceVariationScore_split
lemma fixedRecurrenceVariationScore_split
    (c : ClassConstants) (P : SubjectLaw) (hP : PoissonRecurrence P)
    (a : Arm) (n : ℕ) {T : ℝ} (hT : T ≤ 1)
    (e : Fin n → Arm × (ℝ × ENNReal)) (r : Fin n → RecurConfig) :
    recurrenceJointExposureScore P a n (fixedRecurrenceVariationWeight c a 1) e r =
      recurrenceJointExposureScore P a n (fixedRecurrenceVariationWeight c a T) e r +
      recurrenceJointExposureScore P a n (terminalRecurrenceVariationWeight c a T) e r := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP a).2.2.1
  have heq : fixedRecurrenceVariationWeight c a (n := n) 1 =
      fun e i t => fixedRecurrenceVariationWeight c a T e i t +
        terminalRecurrenceVariationWeight c a T e i t := by
    funext e i t
    unfold fixedRecurrenceVariationWeight terminalRecurrenceVariationWeight
    by_cases ht : t ≤ T
    · simp [ht, ht.trans hT, not_lt.mpr ht]
    · simp [ht, lt_of_not_ge ht]
  have hi (i : Fin n) : Integrable (fixedRecurrenceVariationWeight c a T e i)
      (recurrenceIntensity P a) := by
    apply Integrable.of_bound
      ((measurable_fixedRecurrenceVariationWeight c a T i).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ((n : ℝ) * weightEnvelope c ^ 2)
    exact Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using fixedRecurrenceVariationWeight_abs_le c a T e i t)
  have hj (i : Fin n) : Integrable (terminalRecurrenceVariationWeight c a T e i)
      (recurrenceIntensity P a) := by
    apply Integrable.of_bound
      ((measurable_terminalRecurrenceVariationWeight c a T i).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ((n : ℝ) * weightEnvelope c ^ 2)
    exact Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using terminalRecurrenceVariationWeight_abs_le c a T e i t)
  unfold recurrenceJointExposureScore
  rw [heq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_add_distrib, integral_add (hi i) (hj i)]
  ring

-- @node: fullRecurrenceVariationScore_probability_tendsto_zero
lemma fullRecurrenceVariationScore_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |recurrenceJointExposureScore P a n (fixedRecurrenceVariationWeight c a 1)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have htail : Tendsto (fun T : ℝ =>
      ((4 * c.lambdaMax * Real.exp c.dMax / c.pMin) *
        ∫ t in T..1, (retention P a t)⁻¹) / (ε / 2))
      (nhdsWithin 1 (Icc (0 : ℝ) 1)) (nhds 0) := by
    simpa only [mul_zero, zero_div] using
      ((studyWindow_integral_tail_tendsto_zero _
        (inv_retention_intervalIntegrable_subcritical c P hP hk a)).const_mul
          (4 * c.lambdaMax * Real.exp c.dMax / c.pMin)).div_const (ε / 2)
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun _ => hl.trans_le measureReal_nonneg)
  · intro η hη
    obtain ⟨T, hT0, hT1, hsmall⟩ := exists_strict_study_horizon_of_eventually
      (htail.eventually (gt_mem_nhds (half_pos hη)))
    have hlocal := (fixedRecurrenceVariationScore_probability_tendsto_zero c P hP a
      ⟨hT0, hT1⟩ (half_pos hε)).eventually (gt_mem_nhds (half_pos hη))
    filter_upwards [hlocal, eventually_ge_atTop 1] with n hn hn1
    have ht := terminalRecurrenceVariationScore_probability_le c P hP hk a
      (show 0 < n by omega) ⟨hT0, hT1.le⟩ (half_pos hε)
    have hb : (Measure.pi (fun _ : Fin n => P.latent)).real {z |
        ε < |recurrenceJointExposureScore P a n (fixedRecurrenceVariationWeight c a 1)
          (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
          (fun j => (z j).recur a)|} ≤
        (Measure.pi (fun _ : Fin n => P.latent)).real {z |
          ε / 2 < |recurrenceJointExposureScore P a n (fixedRecurrenceVariationWeight c a T)
            (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
            (fun j => (z j).recur a)|} +
        (Measure.pi (fun _ : Fin n => P.latent)).real {z |
          ε / 2 < |recurrenceJointExposureScore P a n (terminalRecurrenceVariationWeight c a T)
            (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
            (fun j => (z j).recur a)|} := by
      apply (measureReal_mono ?_ (by finiteness)).trans (measureReal_union_le _ _)
      intro z hz
      rw [mem_setOf_eq, fixedRecurrenceVariationScore_split c P hP.poissonRecurrence a n hT1.le] at hz
      by_contra h
      simp only [mem_union, mem_setOf_eq, not_or, not_lt] at h
      have ha := abs_add_le
        (recurrenceJointExposureScore P a n (fixedRecurrenceVariationWeight c a T)
          (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) (fun j => (z j).recur a))
        (recurrenceJointExposureScore P a n (terminalRecurrenceVariationWeight c a T)
          (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) (fun j => (z j).recur a))
      linarith
    exact hb.trans_lt (by linarith)

/-- Measurability of the actual optional-variation remainder for any horizon. -/
-- @node: measurable_fixedRecurrenceVariationRemainder
@[fun_prop] lemma measurable_fixedRecurrenceVariationRemainder
    (c : ClassConstants) (P : SubjectLaw) (hP : PoissonRecurrence P)
    (a : Arm) (n : ℕ) (T : ℝ) :
    Measurable (fixedRecurrenceVariationRemainder c P a (n := n) T) := by
  have hm : Measurable (fixedRecurrenceVariationRemainder c P a (n := n) T) := by
    letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP a).2.2.1
    unfold fixedRecurrenceVariationRemainder
    apply Measurable.sub
    · apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i _
      apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      · have hpoint : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
          if p.2 ≤ T then deathKMLeft a p.1 p.2 ^ 2 * invRisk a p.1 p.2 ^ 2 else 0) :=
          Measurable.ite (measurableSet_le measurable_snd measurable_const) (by fun_prop)
            measurable_const
        have heq : (fun s : Fin n → ObsHistory =>
            Multiset.sum (((s i).recur.times.filter (fun t => t ≤ T)).map
              (fun t => deathKMLeft a s t ^ 2 * invRisk a s t ^ 2))) =
            fun s => ∑ k : Fin (s i).recur.1, if (((s i).recur).2 k).1 ≤ T then
              deathKMLeft a s (((s i).recur).2 k).1 ^ 2 *
                invRisk a s (((s i).recur).2 k).1 ^ 2 else 0 := by
          funext s
          exact recurrence_times_filtered_sum _ _ _
        rw [heq]
        have hsum := measurable_recurrence_param_point_sum
          (fun (s : Fin n → ObsHistory) (x : ℝ × ℝ) =>
            if x.1 ≤ T then deathKMLeft a s x.1 ^ 2 * invRisk a s x.1 ^ 2 else 0)
          (hpoint.comp (show Measurable (fun p : (Fin n → ObsHistory) × (ℝ × ℝ) =>
            (p.1, p.2.1)) by fun_prop))
        exact hsum.comp (show Measurable (fun s : Fin n → ObsHistory =>
          (s, (s i).recur)) by fun_prop)
      · exact measurable_const
    · apply Finset.measurable_sum
      intro i _
      have hi : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
          if p.2 ≤ T then (n : ℝ) * recurrenceSubjectWeight c 0 a p.1 i p.2 ^ 2 else 0) :=
        Measurable.ite (measurableSet_le measurable_snd measurable_const) (by fun_prop)
          measurable_const
      exact hi.stronglyMeasurable.integral_prod_right'.measurable
  exact hm

/-- The full-horizon recurrence remainder vanishes under the observed law. -/
-- @node: fullRecurrenceVariationRemainder_probability_tendsto_zero
lemma fullRecurrenceVariationRemainder_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |fixedRecurrenceVariationRemainder c P a 1 s|}) atTop (nhds 0) := by
  have ht := fullRecurrenceVariationScore_probability_tendsto_zero c P hP hk a hε
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  have hm := measurable_fixedRecurrenceVariationRemainder c P hP.poissonRecurrence a n 1
  dsimp only
  rw [recurrence_sampleLaw_eq_latent_map]
  simp only [measureReal_def]
  rw [Measure.map_apply
    (show Measurable (fun z : Fin n → LatentSubject => fun j => observe (z j)) by fun_prop)
    (measurableSet_lt measurable_const hm.abs)]
  congr 1
  congr 1
  ext z
  simp only [mem_setOf_eq, mem_preimage, fixedRecurrenceVariationRemainder_eq_latent_score]

/-- Summing conditional subject intensities recovers the observed recurrence
variance drift, retaining all dependence in KM and the risk set. -/
-- @node: fullRecurrenceVariation_compensator_eq
lemma fullRecurrenceVariation_compensator_eq
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) :
    (∑ i : Fin n, ∫ t, (if t ≤ 1 then
      (n : ℝ) * recurrenceSubjectWeight c 0 a s i t ^ 2 else 0)
        ∂recurrenceIntensity P a) =
      (n : ℝ) * ∫ t in Ioo (0 : ℝ) 1,
        deathKMLeft a s t ^ 2 * invRisk a s t * P.lam a t := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hP.poissonRecurrence a).2.2.1
  have hi (i : Fin n) : Integrable (fun t => if t ≤ 1 then
      (n : ℝ) * recurrenceSubjectWeight c 0 a s i t ^ 2 else 0)
      (recurrenceIntensity P a) := by
    have hm : Measurable (fun t => if t ≤ 1 then
        (n : ℝ) * recurrenceSubjectWeight c 0 a s i t ^ 2 else 0) :=
      Measurable.ite (measurableSet_le measurable_id measurable_const)
        (by fun_prop) measurable_const
    apply Integrable.of_bound hm.aestronglyMeasurable ((n : ℝ) * weightEnvelope c ^ 2)
    filter_upwards [] with t
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (recurrenceSubjectWeight_abs_le_of_nonneg c (by norm_num) a s i t) 2
    · simp only [norm_zero]; positivity
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  have heq (t : ℝ) : (∑ i : Fin n, if t ≤ 1 then
      (n : ℝ) * recurrenceSubjectWeight c 0 a s i t ^ 2 else 0) =
      if t ≤ 1 then (n : ℝ) * deathKMLeft a s t ^ 2 * invRisk a s t else 0 := by
    split_ifs
    · rw [← Finset.mul_sum, recurrenceSubjectWeight_sum_sq]
      simp [continuationWeight, mul_assoc]
    · simp only [Finset.sum_const_zero]
  simp_rw [heq]
  unfold recurrenceIntensity
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hP.poissonRecurrence a).1.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (∫ t in Ioc (0 : ℝ) 1,
      (ENNReal.ofReal (P.lam a t)).toReal •
        (if t ≤ 1 then (n : ℝ) * deathKMLeft a s t ^ 2 * invRisk a s t else 0)) =
      ∫ t in Ioc (0 : ℝ) 1,
        (n : ℝ) * (deathKMLeft a s t ^ 2 * invRisk a s t * P.lam a t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc, (hP.poissonRecurrence a).2.1] with t ht hl
    simp only [if_pos ht.2, ENNReal.toReal_ofReal hl, smul_eq_mul]
    ring
  rw [he, integral_Ioc_eq_integral_Ioo, integral_const_mul]

/-- The actual recurrence contribution to the observable variance statistic
converges to the recurrence term of the influence variance (roadmap (34)). -/
-- @node: subcritical_recurrenceVariation_probability_tendsto_limit
lemma subcritical_recurrenceVariation_probability_tendsto_limit
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |(n : ℝ) * (∑ i : Fin n, if (s i).treatment = a then
        Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1)).map
          (fun t => deathKMLeft a s t ^ 2 * invRisk a s t ^ 2)) else 0) -
        (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
          survival P a t * P.lam a t / retention P a t|}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  have hr := fullRecurrenceVariationRemainder_probability_tendsto_zero c P hP hk a (half_pos hε)
  have hc := subcritical_recurrence_actual_compensator_probability_tendsto_zero
    c P hP hk a (half_pos hε)
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa only [add_zero] using hr.add hc)
  intro n
  apply (measureReal_mono ?_ (by finiteness)).trans (measureReal_union_le _ _)
  intro s hs
  by_contra h
  simp only [mem_union, mem_setOf_eq, not_or, not_lt] at h
  have he : (n : ℝ) * (∑ i : Fin n, if (s i).treatment = a then
      Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1)).map
        (fun t => deathKMLeft a s t ^ 2 * invRisk a s t ^ 2)) else 0) -
      (P.p a)⁻¹ * (∫ t in (0 : ℝ)..1, survival P a t * P.lam a t / retention P a t) =
      fixedRecurrenceVariationRemainder c P a 1 s +
      ((n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
        deathKMLeft a s t ^ 2 * invRisk a s t * P.lam a t) -
        (P.p a)⁻¹ * (∫ t in (0 : ℝ)..1, survival P a t * P.lam a t / retention P a t)) := by
    unfold fixedRecurrenceVariationRemainder
    rw [fullRecurrenceVariation_compensator_eq c P hP a s]
    ring
  rw [mem_setOf_eq, he] at hs
  have ha := abs_add_le (fixedRecurrenceVariationRemainder c P a 1 s)
    ((n : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
      deathKMLeft a s t ^ 2 * invRisk a s t * P.lam a t) -
      (P.p a)⁻¹ * (∫ t in (0 : ℝ)..1, survival P a t * P.lam a t / retention P a t))
  linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
