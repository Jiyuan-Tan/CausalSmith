module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessExplicitRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceSecondMoment

/-!
# Finite-sample recurrence risk

The exact weighted Poisson energy is bounded by expected time-dependent inverse
risk. The verified binomial reciprocal-count bound and retention envelope give
the declared variance factor without an endpoint inverse-risk substitution.
-/

public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Synthetic stopping preserves the reference risk count through the horizon. -/
-- @node: recurrence_referenceStoppedSyntheticSample_riskSet
lemma recurrence_referenceStoppedSyntheticSample_riskSet {n : ℕ}
    (x : DeathCP.Sample n) {t : ℝ} (ht : t ≤ 1) :
    Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t
      (referenceStoppedSyntheticSample x) =
      Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t x := by
  classical
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskSet
  apply Finset.sum_congr rfl
  intro i _
  have heq : (0 ≤ t ∧ t ≤ (referenceStoppedSyntheticSample x i).1 ∧
      t ≤ (referenceStoppedSyntheticSample x i).2) ↔
      (0 ≤ t ∧ t ≤ (x i).1 ∧ t ≤ (x i).2) := by
    unfold referenceStoppedSyntheticSample stoppedSyntheticDeathPair
    split_ifs <;> constructor
    · rintro ⟨h0, _, h2⟩
      exact ⟨h0, h2.trans (min_le_left _ _),
        h2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    · rintro ⟨h0, h1, h2⟩
      have hm := le_min h1 (le_min h2 ht)
      exact ⟨h0, by linarith, hm⟩
    · rintro ⟨h0, h1, _⟩
      exact ⟨h0, h1.trans (min_le_left _ _),
        h1.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    · rintro ⟨h0, h1, h2⟩
      have hm := le_min h1 (le_min h2 ht)
      exact ⟨h0, hm, by linarith⟩
  simp only [heq]

/-- The observed reciprocal risk inherits the verified reference binomial bound. -/
-- @node: recurrence_integral_invRisk_le_arm_tail
lemma recurrence_integral_invRisk_le_arm_tail (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫ s : Fin n → ObsHistory, invRisk a s t ∂sampleLaw P n) ≤
      2 / ((n : ℝ) * (P.p a * retention P a t * survival P a t)) := by
  let f := fun x : DeathCP.Sample n =>
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
  have hf : Measurable f :=
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
      (measurable_const.prodMk measurable_id)
  have hobs : Measurable (observedDeathSample a (n := n)) := by
    exact measurable_pi_lambda _ (fun i =>
      (measurable_observedDeathPair a).comp (measurable_pi_apply i))
  have heq (x : DeathCP.Sample n) : f (referenceStoppedSyntheticSample x) = f x := by
    unfold f Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk
    rw [recurrence_referenceStoppedSyntheticSample_riskSet x ht1.le]
  calc
    _ = ∫ s : Fin n → ObsHistory, f (observedDeathSample a s) ∂sampleLaw P n := by
      apply integral_congr_ae
      filter_upwards [] with s
      exact (observedDeathSample_inverseRisk a s ht0).symm
    _ = ∫ x, f x ∂(sampleLaw P n).map (observedDeathSample a) :=
      (integral_map hobs.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ x, f (referenceStoppedSyntheticSample x)
        ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a) := by
      rw [observedDeathSample_map_eq_reference P hP.deathHazard
        hP.randomAssignment hP.independentCensoring a,
        integral_map measurable_referenceStoppedSyntheticSample.aemeasurable
          hf.aestronglyMeasurable]
    _ = ∫ x, f x ∂Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
          (armDeathFailureLaw P a) (referenceDeathLaw P a) := by simp_rw [heq]
    _ ≤ _ := DeathCP.integral_inverseRisk_le_arm_tail c P hP a hn ht0 ht1

/-- The recurrence second moment is controlled by expected inverse risk averaged
in time. Integrability is obtained from bounded inverse risk before Fubini. -/
-- @node: recurrenceError_secondMoment_le_expectedInverseRisk
lemma recurrenceError_secondMoment_le_expectedInverseRisk
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s h ^ 2 ∂sampleLaw P n) ≤
      weightEnvelope c ^ 2 * c.lambdaMax *
        ∫ t in (0 : ℝ)..(1 - h), ∫ s : Fin n → ObsHistory,
          invRisk a s t ∂sampleLaw P n := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let ν := volume.restrict (Ioc (0 : ℝ) (1 - h))
  let K := weightEnvelope c ^ 2 * c.lambdaMax
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _)
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
  have hi : Integrable (fun p : (Fin n → ObsHistory) × ℝ => invRisk a p.1 p.2)
      ((sampleLaw P n).prod ν) := by
    apply Integrable.of_bound (measurable_recurrenceInvRisk_joint a).aestronglyMeasurable 1
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (recurrence_invRisk_mem_Icc a p.1 p.2).1]
    exact (recurrence_invRisk_mem_Icc a p.1 p.2).2
  have heMeas : Measurable (fun s : Fin n → ObsHistory => ∑ i : Fin n,
      ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) :=
    Finset.measurable_sum _ (fun i _ =>
      measurable_recurrenceWeightIntegral c P hP.poissonRecurrence a i hh.le hh1 2)
  have heInt : Integrable (fun s : Fin n → ObsHistory => ∑ i : Fin n,
      ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t)
      (sampleLaw P n) := by
    apply Integrable.of_bound heMeas.aestronglyMeasurable (n * K)
    filter_upwards [] with s
    rw [Real.norm_eq_abs]
    exact recurrence_integrated_energy_abs_le c P hP a s hh hh1
  rw [recurrenceError_secondMoment_eq_subject_energy c P hP a n hh hh1]
  calc
    _ ≤ ∫ s : Fin n → ObsHistory, K * ∫ t, invRisk a s t ∂ν ∂sampleLaw P n := by
      apply integral_mono heInt (hi.integral_prod_left.const_mul K)
      intro s
      simpa only [ν, intervalIntegral.integral_of_le (by linarith : 0 ≤ 1 - h)] using
        recurrenceSubjectWeight_integrated_energy_le c P hP a s hh hh1
    _ = K * ∫ t, ∫ s : Fin n → ObsHistory, invRisk a s t ∂sampleLaw P n ∂ν := by
      rw [integral_const_mul, integral_integral_swap hi]
    _ = _ := by rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ 1 - h)]

/-- The recurrence error has the finite-sample variance bound declared in the
paper, with the full endpoint variance factor and the stated constants. -/
-- @node: recurrenceError_secondMoment_le_explicit
lemma recurrenceError_secondMoment_le_explicit
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (hhx : h ≤ c.x0) :
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s h ^ 2 ∂sampleLaw P n) ≤
      2 * reciprocalRetentionEnvelope c * weightEnvelope c ^ 2 / c.pMin *
        c.lambdaMax * Real.exp c.dMax * (n : ℝ)⁻¹ * varianceFactor c h := by
  have hh1 : h ≤ 1 := hhx.trans c.x0_le |>.trans (by norm_num)
  have hT : 0 ≤ 1 - h := by linarith
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let ν := volume.restrict (Ioc (0 : ℝ) (1 - h))
  let r := fun t => ∫ s : Fin n → ObsHistory, invRisk a s t ∂sampleLaw P n
  let K := weightEnvelope c ^ 2 * c.lambdaMax
  let C := 2 * Real.exp c.dMax / ((n : ℝ) * c.pMin)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _)
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
  have hC : 0 ≤ C := div_nonneg
    (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (mul_nonneg hnR.le c.pMin_pos.le)
  have hrMeas : Measurable r :=
    (measurable_recurrenceInvRisk_joint a).stronglyMeasurable.integral_prod_left'.measurable
  have hrBound (t : ℝ) : |r t| ≤ 1 := by
    have hi : Integrable (fun s : Fin n → ObsHistory => invRisk a s t) (sampleLaw P n) := by
      apply Integrable.of_bound
        ((measurable_recurrenceInvRisk_joint a).comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
      filter_upwards [] with s
      change |invRisk a s t| ≤ 1
      rw [abs_of_nonneg (recurrence_invRisk_mem_Icc a s t).1]
      exact (recurrence_invRisk_mem_Icc a s t).2
    rw [abs_of_nonneg (integral_nonneg (fun s => (recurrence_invRisk_mem_Icc a s t).1))]
    simpa using integral_mono hi (integrable_const 1)
      (fun s => (recurrence_invRisk_mem_Icc a s t).2)
  have hrInt : Integrable r ν := Integrable.of_bound hrMeas.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hrBound t))
  have hretInt : Integrable (fun t => (retention P a t)⁻¹) ν :=
    (inv_retention_integrableOn c P hP a hT (by linarith)).mono_set Ioc_subset_Icc_self
  have hpoint : ∀ᵐ t ∂ν, r t ≤ C * (retention P a t)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : t < 1 := by linarith [ht.2]
    have hp : 0 < P.p a := c.pMin_pos.trans_le (hP.treatmentOverlap a)
    have hr : 0 < retention P a t :=
      retention_pos_of_modelClass c P hP a t ht.1.le ht1
    have hs : 0 < survival P a t := Real.exp_pos _
    have hsurv := (survival_bounds_of_deathBounds c P hP.deathBounds a
      ⟨ht.1.le, ht1.le⟩).1
    calc
      r t ≤ 2 / ((n : ℝ) * (P.p a * retention P a t * survival P a t)) :=
        recurrence_integral_invRisk_le_arm_tail c P hP a hn ht.1 ht1
      _ ≤ 2 / ((n : ℝ) * (c.pMin * retention P a t * Real.exp (-c.dMax))) := by
        apply div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hnR (mul_pos (mul_pos c.pMin_pos hr) (Real.exp_pos _)))
        gcongr
        exact hP.treatmentOverlap a
      _ = C * (retention P a t)⁻¹ := by
        dsimp [C]
        rw [Real.exp_neg]
        field_simp
  have hrate : (∫ t, r t ∂ν) ≤ C *
      (reciprocalRetentionEnvelope c * varianceFactor c h) := by
    calc
      _ ≤ ∫ t, C * (retention P a t)⁻¹ ∂ν :=
        integral_mono_ae hrInt (hretInt.const_mul C) hpoint
      _ = C * ∫ t, (retention P a t)⁻¹ ∂ν := by rw [integral_const_mul]
      _ ≤ C * (reciprocalRetentionEnvelope c * varianceFactor c h) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa only [ν, integral_Icc_eq_integral_Ioc] using
          reciprocal_retention_integral_le c P hP a hh hhx
  calc
    _ ≤ K * ∫ t, r t ∂ν := by
      simpa only [K, r, ν, intervalIntegral.integral_of_le hT] using
        recurrenceError_secondMoment_le_expectedInverseRisk c P hP a n hh hh1
    _ ≤ K * (C * (reciprocalRetentionEnvelope c * varianceFactor c h)) :=
      mul_le_mul_of_nonneg_left hrate hK
    _ = _ := by
      dsimp [K, C]
      field_simp

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
