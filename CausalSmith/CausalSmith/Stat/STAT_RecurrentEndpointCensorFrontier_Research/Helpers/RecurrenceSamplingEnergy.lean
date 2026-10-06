module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceFiniteRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleTails

/-!
# Full-horizon recurrence energy under sampling assumptions

Roadmap (2), (6), (19), and (23): the concrete exposure-dependent recurrence
score has exact Poisson energy even at cutoff zero. Nonnegative cutoffs retain
the bounded continuation envelope; Fubini and the binomial reciprocal-risk
bound therefore also apply to the ordinary estimator. No endpoint bound on
inverse retention and no independence between KM and risk are imposed.
-/

public section

open MeasureTheory Set ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The continuation envelope includes the ordinary unit weight. -/
-- @node: continuationWeight_abs_le_envelope_of_nonneg
lemma continuationWeight_abs_le_envelope_of_nonneg (c : ClassConstants)
    {h t : ℝ} (hh : 0 ≤ h) :
    |continuationWeight (holderOrder c) h t| ≤ weightEnvelope c := by
  rcases eq_or_lt_of_le hh with he | hp
  · rw [← he]
    simp only [continuationWeight, ↓reduceIte, abs_one]
    unfold weightEnvelope continuationNorm
    exact le_add_of_nonneg_right (by positivity)
  · exact continuationWeight_abs_le_coeffSum (holderOrder c) hp

/-- Exposure-dependent subject scores obey the continuation envelope, including cutoff zero. -/
-- @node: recurrenceSubjectWeight_abs_le_of_nonneg
lemma recurrenceSubjectWeight_abs_le_of_nonneg (c : ClassConstants) {h : ℝ}
    (hh : 0 ≤ h) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (i : Fin n) (t : ℝ) :
    |recurrenceSubjectWeight c h a s i t| ≤ weightEnvelope c := by
  have hW : 0 ≤ weightEnvelope c := by
    unfold weightEnvelope continuationNorm
    positivity
  unfold recurrenceSubjectWeight
  split_ifs
  · rw [abs_mul, abs_mul, abs_of_nonneg (deathKMLeft_mem_Icc a s t).1,
      abs_of_nonneg (recurrence_invRisk_mem_Icc a s t).1]
    calc
      _ ≤ weightEnvelope c * 1 * 1 := by
        gcongr
        · exact (recurrence_invRisk_mem_Icc a s t).1
        · exact (deathKMLeft_mem_Icc a s t).1
        · exact continuationWeight_abs_le_envelope_of_nonneg c hh
        · exact (deathKMLeft_mem_Icc a s t).2
        · exact (recurrence_invRisk_mem_Icc a s t).2
      _ = _ := by ring
  · simpa using hW

/-- Every finite power of the bounded subject score times the recurrence intensity is integrable through the full horizon. -/
-- @node: recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable_of_nonneg_of_assumptions
lemma recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable_of_nonneg_of_assumptions (c :
  ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (i : Fin n) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (k : ℕ) :
    IntervalIntegrable (fun t => recurrenceSubjectWeight c h a s i t ^ k *
      P.lam a t) volume 0 (1 - h) := by
  have hT : 0 ≤ 1 - h := by linarith
  have hlam : IntervalIntegrable (P.lam a) volume 0 (1 - h) :=
    (poissonRecurrence_intervalIntegrable P hPoisson a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT]
      exact Set.Icc_subset_Icc le_rfl (by linarith))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hlam ⊢
  apply hlam.bdd_mul (c := weightEnvelope c ^ k)
    ((measurable_recurrenceSubjectWeight c h a s i).pow_const k
      |>.aestronglyMeasurable.restrict)
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (recurrenceSubjectWeight_abs_le_of_nonneg c hh a s i t) k

/-- The diagonal recurrence energy is bounded by time-dependent inverse risk at every study time. -/
-- @node: recurrenceSubjectWeight_energy_density_le_of_nonneg_of_assumptions
lemma recurrenceSubjectWeight_energy_density_le_of_nonneg_of_assumptions (c : ClassConstants)
    (P : SubjectLaw) (hBounds : RecurrenceBounds c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h t : ℝ} (hh : 0 ≤ h)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i : Fin n, recurrenceSubjectWeight c h a s i t ^ 2) * P.lam a t ≤
      weightEnvelope c ^ 2 * c.lambdaMax * invRisk a s t := by
  have hw : |continuationWeight (holderOrder c) h t| ≤ weightEnvelope c :=
    continuationWeight_abs_le_envelope_of_nonneg c hh
  have hW : 0 ≤ weightEnvelope c := by
    unfold weightEnvelope continuationNorm
    positivity
  have hw2 : continuationWeight (holderOrder c) h t ^ 2 ≤ weightEnvelope c ^ 2 :=
    by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hW).2 hw
  have hk := deathKMLeft_mem_Icc a s t
  have hk2 : deathKMLeft a s t ^ 2 ≤ 1 := by nlinarith [hk.1, hk.2]
  have hi : 0 ≤ invRisk a s t := by
    unfold invRisk
    split_ifs <;> positivity
  have hl := hBounds a t ht
  have hl0 : 0 ≤ P.lam a t := c.lambdaMin_pos.le.trans hl.1
  rw [recurrenceSubjectWeight_sum_sq]
  calc
    _ ≤ weightEnvelope c ^ 2 * 1 * invRisk a s t * P.lam a t := by
      gcongr
    _ ≤ weightEnvelope c ^ 2 * c.lambdaMax * invRisk a s t := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (weightEnvelope c)) hi)
        (sub_nonneg.mpr hl.2)]

/-- Summing the subject intensity integrals gives the observed aggregate recurrence compensator even with zero cutoff. -/
-- @node: recurrenceSubjectWeight_compensator_eq_of_nonneg_of_assumptions
lemma recurrenceSubjectWeight_compensator_eq_of_nonneg_of_assumptions (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t * P.lam a t) =
    ∫ t in (0 : ℝ)..(1 - h),
      continuationWeight (holderOrder c) h t * deathKMLeft a s t *
        (if riskSet a s t = 0 then 0 else P.lam a t) := by
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← Finset.sum_mul, recurrenceSubjectWeight_sum]
    split_ifs <;> ring
  · intro i _
    simpa only [pow_one] using
      recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable_of_nonneg_of_assumptions c P hPoisson
        a s i hh hh1 1

/-- The actual recurrence error is the observed point payoff minus the sum of its subject compensators. -/
-- @node: recurrenceError_eq_subject_compensators_of_nonneg_of_assumptions
lemma recurrenceError_eq_subject_compensators_of_nonneg_of_assumptions (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    recurrenceError c P a s h = muTildeAt c h a s -
      ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t * P.lam a t := by
  rw [recurrenceSubjectWeight_compensator_eq_of_nonneg_of_assumptions c P hPoisson a s hh hh1]
  rfl

/-- The integrated subject energy is controlled by the time integral of inverse risk, retaining the risk factor inside the integral. -/
-- @node: recurrenceSubjectWeight_integrated_energy_le_of_nonneg_of_assumptions
lemma recurrenceSubjectWeight_integrated_energy_le_of_nonneg_of_assumptions (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hBounds : RecurrenceBounds c P) (a : Arm)
      {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) ≤
    weightEnvelope c ^ 2 * c.lambdaMax *
      ∫ t in (0 : ℝ)..(1 - h), invRisk a s t := by
  have hT : 0 ≤ 1 - h := by linarith
  have hi (i : Fin n) :=
    recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable_of_nonneg_of_assumptions c P hPoisson a
      s i hh hh1 2
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i),
    ← intervalIntegral.integral_const_mul]
  have hsum : IntervalIntegrable (fun t => ∑ i : Fin n,
      recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) volume 0 (1 - h) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact integrable_finsetSum Finset.univ (fun i _ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (hi i))
  apply intervalIntegral.integral_mono_on hT hsum
    ((recurrenceInvRisk_intervalIntegrable a s hT).const_mul
      (weightEnvelope c ^ 2 * c.lambdaMax))
  intro t ht
  rw [← Finset.sum_mul]
  exact recurrenceSubjectWeight_energy_density_le_of_nonneg_of_assumptions c P hBounds a s hh
    ⟨ht.1, ht.2.trans (by linarith)⟩

/-- The observed recurrence error agrees pathwise with its latent compensated Poisson scores through the full horizon. -/
-- @node: recurrenceError_eq_latent_compensated_scores_of_nonneg_of_assumptions
lemma recurrenceError_eq_latent_compensated_scores_of_nonneg_of_assumptions (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (a : Arm) {n : ℕ}
    (z : Fin n → LatentSubject) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    recurrenceError c P a (fun i => observe (z i)) h =
      ∑ i : Fin n,
        ((∑ k : Fin ((z i).recur a).1,
          if (((z i).recur a).2 k).1 ≤ 1 - h then
            recurrenceSubjectWeight c h a (fun j => observe (z j)) i
              (((z i).recur a).2 k).1 else 0) -
        ∫ t in (0 : ℝ)..(1 - h),
          recurrenceSubjectWeight c h a (fun j => observe (z j)) i t * P.lam a t) := by
  rw [recurrenceError_eq_subject_compensators_of_nonneg_of_assumptions c P hPoisson a _ hh hh1,
    recurrence_muTilde_eq_latent_point_scores, Finset.sum_sub_distrib]

/-- Exposure replacement preserves the actual recurrence error at any nonnegative cutoff. -/
-- @node: recurrenceError_eq_concreteExposureScore_of_nonneg_of_assumptions
lemma recurrenceError_eq_concreteExposureScore_of_nonneg_of_assumptions (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (a : Arm) {n : ℕ}
    (z : Fin n → LatentSubject) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    recurrenceError c P a (fun i => observe (z i)) h =
      recurrenceConcreteExposureScore c P a n h
        (fun i => ((z i).treatment, ((z i).death a, (z i).censor a)))
        (fun i => (z i).recur a) := by
  rw [recurrenceError_eq_latent_compensated_scores_of_nonneg_of_assumptions c P hPoisson a z hh hh1]
  unfold recurrenceConcreteExposureScore
  simp_rw [recurrenceSubjectWeight_eq_exposureHistory]

/-- The actual recurrence error is measurable also for the ordinary zero-cutoff estimator. -/
-- @node: measurable_recurrenceError_of_nonneg_of_assumptions
@[fun_prop] lemma measurable_recurrenceError_of_nonneg_of_assumptions (c : ClassConstants) (P :
  SubjectLaw)
    (hPoisson : PoissonRecurrence P) (a : Arm) (n : ℕ) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Measurable (fun s : Fin n → ObsHistory => recurrenceError c P a s h) := by
  have heq : (fun s : Fin n → ObsHistory => recurrenceError c P a s h) =
      fun s => muTildeAt c h a s - ∑ i : Fin n,
        ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t * P.lam a t := by
    funext s
    exact recurrenceError_eq_subject_compensators_of_nonneg_of_assumptions c P hPoisson a s hh hh1
  rw [heq]
  apply (measurable_recurrenceMuTildeAt c h a n).sub
  apply Finset.measurable_sum
  intro i _
  simpa only [pow_one] using
    measurable_recurrenceWeightIntegral c P hPoisson a i hh hh1 1

/-- Conditioning on the full exposure array gives the exact Poisson second moment through the ordinary horizon. -/
-- @node: recurrenceConcreteExposureScore_conditional_second_moment_of_nonneg_of_assumptions
lemma recurrenceConcreteExposureScore_conditional_second_moment_of_nonneg_of_assumptions
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (e : Fin n → Arm × (ℝ × ENNReal)) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun r => recurrenceConcreteExposureScore c P a n h e r ^ 2)
      (Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a)) ∧
    (∫ r, recurrenceConcreteExposureScore c P a n h e r ^ 2
      ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a)) =
      ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
          P.lam a t := by
  let w := fun i => recurrenceSubjectWeight c h a
    (fun j => recurrenceExposureHistory (e j)) i
  let f := fun i t => if t ≤ 1 - h then w i t else 0
  have hf (i : Fin n) : Measurable (f i) := by
    apply Measurable.ite (measurableSet_le measurable_id measurable_const)
    · exact measurable_recurrenceSubjectWeight c h a _ i
    · exact measurable_const
  have hK (i : Fin n) (t : ℝ) : |f i t| ≤ weightEnvelope c := by
    dsimp [f]
    split_ifs
    · exact recurrenceSubjectWeight_abs_le_of_nonneg c hh a _ i t
    · simp only [abs_zero]
      unfold weightEnvelope continuationNorm
      positivity
  have hm := recurrence_canonical_iid_second_moment (recurrenceIntensity P a) n f hf hK
  have hmean (i : Fin n) : (∫ t, f i t ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..(1 - h), w i t * P.lam a t :=
    recurrenceIntensity_integral_truncated P hPoisson a (w i)
      (by linarith) (by linarith)
  have henergy (i : Fin n) : (∫ t, f i t ^ 2 ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..(1 - h), w i t ^ 2 * P.lam a t := by
    have hp : (fun t => f i t ^ 2) = fun t => if t ≤ 1 - h then w i t ^ 2 else 0 := by
      funext t
      dsimp [f]
      split_ifs <;> simp
    rw [hp]
    exact recurrenceIntensity_integral_truncated P hPoisson a
      (fun t => w i t ^ 2) (by linarith) (by linarith)
  simp_rw [hmean, henergy] at hm
  exact hm

/-- A bounded deterministic envelope establishes integrability of the subject energy before averaging over exposures. -/
-- @node: recurrence_integrated_energy_abs_le_of_nonneg_of_assumptions
lemma recurrence_integrated_energy_abs_le_of_nonneg_of_assumptions (c : ClassConstants) (P :
  SubjectLaw)
    (hBounds : RecurrenceBounds c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    |∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t| ≤
      n * (weightEnvelope c ^ 2 * c.lambdaMax) := by
  have hK : 0 ≤ weightEnvelope c ^ 2 * c.lambdaMax :=
    mul_nonneg (sq_nonneg _) (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
  have hb (i : Fin n) :
      ‖∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t‖ ≤
        weightEnvelope c ^ 2 * c.lambdaMax := by
    have hbound : ∀ t ∈ uIoc (0 : ℝ) (1 - h),
        ‖recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t‖ ≤
          weightEnvelope c ^ 2 * c.lambdaMax := by
      intro t ht
      rw [uIoc_of_le (by linarith : 0 ≤ 1 - h)] at ht
      have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, by linarith [ht.2]⟩
      have hl0 := c.lambdaMin_pos.le.trans (hBounds a t ht01).1
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _)
        (recurrenceSubjectWeight_abs_le_of_nonneg c hh a s i t) 2)
        (hBounds a t ht01).2 hl0 (sq_nonneg _)
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have hlen : |(1 - h) - (0 : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact hb.trans (by nlinarith)
  calc
    _ = ‖∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑ i : Fin n, ‖∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, weightEnvelope c ^ 2 * c.lambdaMax :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp

/-- Fubini averages the conditional Poisson energy on the exposure and recurrence product law, including zero cutoff. -/
-- @node: recurrenceConcreteExposureScore_product_second_moment_of_nonneg_of_assumptions
lemma recurrenceConcreteExposureScore_product_second_moment_of_nonneg_of_assumptions
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hBounds :
      RecurrenceBounds c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (Q : Measure (Fin n → Arm × (ℝ × ENNReal))) [IsFiniteMeasure Q]
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig) =>
      recurrenceConcreteExposureScore c P a n h p.1 p.2 ^ 2)
      (Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a))) ∧
    (∫ p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig),
      recurrenceConcreteExposureScore c P a n h p.1 p.2 ^ 2
      ∂Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a))) =
      ∫ e, (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
          P.lam a t) ∂Q := by
  let : IsProbabilityMeasure (canonicalRecurrenceLaw P a) := by
    unfold canonicalRecurrenceLaw canonicalRecurrenceLawOf
    infer_instance
  let R := Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a)
  let energy := fun e : Fin n → Arm × (ℝ × ENNReal) =>
    ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a
      (fun j => recurrenceExposureHistory (e j)) i t ^ 2 * P.lam a t
  have heMeas : Measurable energy := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_recurrenceWeightIntegral c P hPoisson a i hh hh1 2).comp
      (show Measurable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
        fun j => recurrenceExposureHistory (e j)) by fun_prop)
  have heInt : Integrable energy Q := by
    apply (integrable_const (n * (weightEnvelope c ^ 2 * c.lambdaMax))).mono'
      heMeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro e
    rw [Real.norm_eq_abs]
    exact recurrence_integrated_energy_abs_le_of_nonneg_of_assumptions c P hBounds a _ hh hh1
  have hs := (measurable_recurrenceConcreteExposureScore c P hPoisson
    a n hh hh1).pow_const 2
  have hc (e) := recurrenceConcreteExposureScore_conditional_second_moment_of_nonneg_of_assumptions
    c P hPoisson a n e hh hh1
  have hi : Integrable (fun p => recurrenceConcreteExposureScore c P a n h p.1 p.2 ^ 2)
      (Q.prod R) := by
    apply (integrable_prod_iff hs.aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall (fun e => (hc e).1), ?_⟩
    have he (e) : (∫ r, (‖recurrenceConcreteExposureScore c P a n h e r ^ 2‖) ∂ R) =
        energy e := by
      simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (hc e).2
    simp_rw [he]
    exact heInt
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun e => (hc e).2))

/-- Transport of the canonical product law supplies square integrability and the exact actual observed recurrence second moment. -/
-- @node: recurrenceError_secondMoment_eq_exposure_energy_of_nonneg_of_assumptions
lemma recurrenceError_secondMoment_eq_exposure_energy_of_nonneg_of_assumptions
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hBounds :
      RecurrenceBounds c P) (hRandom : RandomAssignment P) (hRecurDeath :
      RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun s : Fin n → ObsHistory => recurrenceError c P a s h ^ 2)
      (sampleLaw P n) ∧
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s h ^ 2 ∂sampleLaw P n) =
      ∫ e, (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
          P.lam a t)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  obtain ⟨hν, hpair⟩ := iid_exposure_recurrence_map_eq_canonical_prod P
    hRandom hRecurDeath hCensor
    hPoisson a n
  let : IsFiniteMeasure (recurrenceIntensity P a) := hν
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let E := P.latent.map (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))
  let : IsProbabilityMeasure E := Measure.isProbabilityMeasure_map (by fun_prop)
  let μ := Measure.pi (fun _ : Fin n => P.latent)
  let pair := fun z : Fin n → LatentSubject =>
    ((fun i => ((z i).treatment, ((z i).death a, (z i).censor a))),
      (fun i => (z i).recur a))
  have hp : Measurable pair := by fun_prop
  have hs := (measurable_recurrenceConcreteExposureScore c P hPoisson
    a n hh hh1).pow_const 2
  have hm := recurrenceConcreteExposureScore_product_second_moment_of_nonneg_of_assumptions
    c P hPoisson hBounds a n (Measure.pi (fun _ : Fin n => E)) hh hh1
  rw [← hpair] at hm
  have hobs : Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) := by
    fun_prop
  have herr := (measurable_recurrenceError_of_nonneg_of_assumptions c P hPoisson a n hh
    hh1).pow_const 2
  have heq : (fun z : Fin n → LatentSubject =>
      recurrenceError c P a (fun i => observe (z i)) h ^ 2) =
      fun z => recurrenceConcreteExposureScore c P a n h (pair z).1 (pair z).2 ^ 2 := by
    funext z
    rw [recurrenceError_eq_concreteExposureScore_of_nonneg_of_assumptions c P hPoisson a z hh hh1]
  have hiLat := (integrable_map_measure hs.aestronglyMeasurable hp.aemeasurable).1 hm.1
  constructor
  · rw [recurrence_sampleLaw_eq_latent_map]
    apply (integrable_map_measure herr.aestronglyMeasurable hobs.aemeasurable).2
    simp only [Function.comp_def]
    rw [heq]
    exact hiLat
  · rw [recurrence_sampleLaw_eq_latent_map,
      integral_map hobs.aemeasurable herr.aestronglyMeasurable]
    rw [heq]
    rw [← integral_map hp.aemeasurable hs.aestronglyMeasurable]
    exact hm.2

/-- The exposure-averaged recurrence second moment equals the subject energy under the observed iid sample law. -/
-- @node: recurrenceError_secondMoment_eq_subject_energy_of_nonneg_of_assumptions
lemma recurrenceError_secondMoment_eq_subject_energy_of_nonneg_of_assumptions
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hBounds :
      RecurrenceBounds c P) (hRandom : RandomAssignment P) (hRecurDeath :
      RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s h ^ 2 ∂sampleLaw P n) =
      ∫ s : Fin n → ObsHistory, (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) ∂sampleLaw P n := by
  let energy := fun s : Fin n → ObsHistory => ∑ i : Fin n,
    ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t
  have he : Measurable energy := Finset.measurable_sum _ (fun i _ =>
    measurable_recurrenceWeightIntegral c P hPoisson a i hh hh1 2)
  have hE : Measurable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
      energy (fun j => recurrenceExposureHistory (e j))) :=
    he.comp (by fun_prop)
  let exposure := fun z : Fin n → LatentSubject =>
    fun i => ((z i).treatment, ((z i).death a, (z i).censor a))
  have hmap : (Measure.pi (fun _ : Fin n => P.latent)).map exposure =
      Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    by
      let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
      exact Measure.pi_map_pi (fun _ =>
        (show Measurable (fun z : LatentSubject =>
          (z.treatment, (z.death a, z.censor a))) by fun_prop).aemeasurable)
  rw [(recurrenceError_secondMoment_eq_exposure_energy_of_nonneg_of_assumptions c P hPoisson
    hBounds hRandom hRecurDeath hCensor a n hh hh1).2]
  change (∫ e, energy (fun j => recurrenceExposureHistory (e j))
    ∂Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
    ∫ s, energy s ∂sampleLaw P n
  rw [← hmap, integral_map (show Measurable exposure by fun_prop).aemeasurable
    hE.aestronglyMeasurable, recurrence_sampleLaw_eq_latent_map,
    integral_map (show Measurable (fun z : Fin n → LatentSubject =>
      fun i => observe (z i)) by fun_prop).aemeasurable he.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  unfold energy exposure
  simp_rw [recurrenceSubjectWeight_eq_exposureHistory]

/-- The actual recurrence second moment is bounded by inverse risk averaged over both time and the observed sample. -/
-- @node: recurrenceError_secondMoment_le_expectedInverseRisk_of_nonneg_of_assumptions
lemma recurrenceError_secondMoment_le_expectedInverseRisk_of_nonneg_of_assumptions
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P) (hBounds :
      RecurrenceBounds c P) (hRandom : RandomAssignment P) (hRecurDeath :
      RecurrenceDeathIndependence P) (hCensor : IndependentCensoring P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
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
      measurable_recurrenceWeightIntegral c P hPoisson a i hh hh1 2)
  have heInt : Integrable (fun s : Fin n → ObsHistory => ∑ i : Fin n,
      ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t)
      (sampleLaw P n) := by
    apply Integrable.of_bound heMeas.aestronglyMeasurable (n * K)
    filter_upwards [] with s
    rw [Real.norm_eq_abs]
    exact recurrence_integrated_energy_abs_le_of_nonneg_of_assumptions c P hBounds a s hh hh1
  rw [recurrenceError_secondMoment_eq_subject_energy_of_nonneg_of_assumptions c P hPoisson hBounds
    hRandom hRecurDeath hCensor a n hh hh1]
  calc
    _ ≤ ∫ s : Fin n → ObsHistory, K * ∫ t, invRisk a s t ∂ν ∂sampleLaw P n := by
      apply integral_mono heInt (hi.integral_prod_left.const_mul K)
      intro s
      simpa only [ν, intervalIntegral.integral_of_le (by linarith : 0 ≤ 1 - h)] using
        recurrenceSubjectWeight_integrated_energy_le_of_nonneg_of_assumptions c P hPoisson hBounds
          a s hh hh1
    _ = K * ∫ t, ∫ s : Fin n → ObsHistory, invRisk a s t ∂sampleLaw P n ∂ν := by
      rw [integral_const_mul, integral_integral_swap hi]
    _ = _ := by rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ 1 - h)]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
