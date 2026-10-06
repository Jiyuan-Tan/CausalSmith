module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceSamplingEnergy

/-!
# Full-horizon recurrence energy in the endpoint model

The model-class interface specializes the sampling-only energy identities.
The underlying proofs require no endpoint smoothness or tail condition.
-/

public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Every finite power of the bounded subject score times the recurrence intensity is integrable through the full horizon. -/
-- @node: recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable_of_nonneg
lemma recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable_of_nonneg (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (i : Fin n) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (k : ℕ) :
    IntervalIntegrable (fun t => recurrenceSubjectWeight c h a s i t ^ k *
      P.lam a t) volume 0 (1 - h) := by
  exact recurrenceSubjectWeight_pow_mul_lam_intervalIntegrable_of_nonneg_of_assumptions c P
    hP.poissonRecurrence a s i hh hh1 k

/-- The diagonal recurrence energy is bounded by time-dependent inverse risk at every study time. -/
-- @node: recurrenceSubjectWeight_energy_density_le_of_nonneg
lemma recurrenceSubjectWeight_energy_density_le_of_nonneg (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h t : ℝ} (hh : 0 ≤ h)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i : Fin n, recurrenceSubjectWeight c h a s i t ^ 2) * P.lam a t ≤
      weightEnvelope c ^ 2 * c.lambdaMax * invRisk a s t := by
  exact recurrenceSubjectWeight_energy_density_le_of_nonneg_of_assumptions c P hP.recurrenceBounds
    a s hh ht

/-- Summing the subject intensity integrals gives the observed aggregate recurrence compensator even with zero cutoff. -/
-- @node: recurrenceSubjectWeight_compensator_eq_of_nonneg
lemma recurrenceSubjectWeight_compensator_eq_of_nonneg (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t * P.lam a t) =
    ∫ t in (0 : ℝ)..(1 - h),
      continuationWeight (holderOrder c) h t * deathKMLeft a s t *
        (if riskSet a s t = 0 then 0 else P.lam a t) := by
  exact recurrenceSubjectWeight_compensator_eq_of_nonneg_of_assumptions c P hP.poissonRecurrence a
    s hh hh1

/-- The actual recurrence error is the observed point payoff minus the sum of its subject compensators. -/
-- @node: recurrenceError_eq_subject_compensators_of_nonneg
lemma recurrenceError_eq_subject_compensators_of_nonneg (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    recurrenceError c P a s h = muTildeAt c h a s -
      ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t * P.lam a t := by
  exact recurrenceError_eq_subject_compensators_of_nonneg_of_assumptions c P hP.poissonRecurrence
    a s hh hh1

/-- The integrated subject energy is controlled by the time integral of inverse risk, retaining the risk factor inside the integral. -/
-- @node: recurrenceSubjectWeight_integrated_energy_le_of_nonneg
lemma recurrenceSubjectWeight_integrated_energy_le_of_nonneg (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) ≤
    weightEnvelope c ^ 2 * c.lambdaMax *
      ∫ t in (0 : ℝ)..(1 - h), invRisk a s t := by
  exact recurrenceSubjectWeight_integrated_energy_le_of_nonneg_of_assumptions c P
    hP.poissonRecurrence hP.recurrenceBounds a s hh hh1

/-- The observed recurrence error agrees pathwise with its latent compensated Poisson scores through the full horizon. -/
-- @node: recurrenceError_eq_latent_compensated_scores_of_nonneg
lemma recurrenceError_eq_latent_compensated_scores_of_nonneg (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (z : Fin n → LatentSubject) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    recurrenceError c P a (fun i => observe (z i)) h =
      ∑ i : Fin n,
        ((∑ k : Fin ((z i).recur a).1,
          if (((z i).recur a).2 k).1 ≤ 1 - h then
            recurrenceSubjectWeight c h a (fun j => observe (z j)) i
              (((z i).recur a).2 k).1 else 0) -
        ∫ t in (0 : ℝ)..(1 - h),
          recurrenceSubjectWeight c h a (fun j => observe (z j)) i t * P.lam a t) := by
  exact recurrenceError_eq_latent_compensated_scores_of_nonneg_of_assumptions c P
    hP.poissonRecurrence a z hh hh1

/-- Exposure replacement preserves the actual recurrence error at any nonnegative cutoff. -/
-- @node: recurrenceError_eq_concreteExposureScore_of_nonneg
lemma recurrenceError_eq_concreteExposureScore_of_nonneg (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (z : Fin n → LatentSubject) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    recurrenceError c P a (fun i => observe (z i)) h =
      recurrenceConcreteExposureScore c P a n h
        (fun i => ((z i).treatment, ((z i).death a, (z i).censor a)))
        (fun i => (z i).recur a) := by
  exact recurrenceError_eq_concreteExposureScore_of_nonneg_of_assumptions c P hP.poissonRecurrence
    a z hh hh1

/-- The actual recurrence error is measurable also for the ordinary zero-cutoff estimator. -/
-- @node: measurable_recurrenceError_of_nonneg
lemma measurable_recurrenceError_of_nonneg (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Measurable (fun s : Fin n → ObsHistory => recurrenceError c P a s h) := by
  exact measurable_recurrenceError_of_nonneg_of_assumptions c P hP.poissonRecurrence a n hh hh1

/-- Conditioning on the full exposure array gives the exact Poisson second moment through the ordinary horizon. -/
-- @node: recurrenceConcreteExposureScore_conditional_second_moment_of_nonneg
lemma recurrenceConcreteExposureScore_conditional_second_moment_of_nonneg
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (e : Fin n → Arm × (ℝ × ENNReal)) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun r => recurrenceConcreteExposureScore c P a n h e r ^ 2)
      (Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a)) ∧
    (∫ r, recurrenceConcreteExposureScore c P a n h e r ^ 2
      ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a)) =
      ∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
          P.lam a t := by
  exact recurrenceConcreteExposureScore_conditional_second_moment_of_nonneg_of_assumptions c P
    hP.poissonRecurrence a n e hh hh1

/-- A bounded deterministic envelope establishes integrability of the subject energy before averaging over exposures. -/
-- @node: recurrence_integrated_energy_abs_le_of_nonneg
lemma recurrence_integrated_energy_abs_le_of_nonneg (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    |∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
      recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t| ≤
      n * (weightEnvelope c ^ 2 * c.lambdaMax) := by
  exact recurrence_integrated_energy_abs_le_of_nonneg_of_assumptions c P hP.recurrenceBounds a s
    hh hh1

/-- Fubini averages the conditional Poisson energy on the exposure and recurrence product law, including zero cutoff. -/
-- @node: recurrenceConcreteExposureScore_product_second_moment_of_nonneg
lemma recurrenceConcreteExposureScore_product_second_moment_of_nonneg
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
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
  exact recurrenceConcreteExposureScore_product_second_moment_of_nonneg_of_assumptions c P
    hP.poissonRecurrence hP.recurrenceBounds a n Q hh hh1

/-- Transport of the canonical product law supplies square integrability and the exact actual observed recurrence second moment. -/
-- @node: recurrenceError_secondMoment_eq_exposure_energy_of_nonneg
lemma recurrenceError_secondMoment_eq_exposure_energy_of_nonneg
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun s : Fin n → ObsHistory => recurrenceError c P a s h ^ 2)
      (sampleLaw P n) ∧
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s h ^ 2 ∂sampleLaw P n) =
      ∫ e, (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
          P.lam a t)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  exact recurrenceError_secondMoment_eq_exposure_energy_of_nonneg_of_assumptions c P
    hP.poissonRecurrence hP.recurrenceBounds hP.randomAssignment hP.recurrenceDeathIndependence
    hP.independentCensoring a n hh hh1

/-- The exposure-averaged recurrence second moment equals the subject energy under the observed iid sample law. -/
-- @node: recurrenceError_secondMoment_eq_subject_energy_of_nonneg
lemma recurrenceError_secondMoment_eq_subject_energy_of_nonneg
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s h ^ 2 ∂sampleLaw P n) =
      ∫ s : Fin n → ObsHistory, (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) ∂sampleLaw P n := by
  exact recurrenceError_secondMoment_eq_subject_energy_of_nonneg_of_assumptions c P
    hP.poissonRecurrence hP.recurrenceBounds hP.randomAssignment hP.recurrenceDeathIndependence
    hP.independentCensoring a n hh hh1

/-- The actual recurrence second moment is bounded by inverse risk averaged over both time and the observed sample. -/
-- @node: recurrenceError_secondMoment_le_expectedInverseRisk_of_nonneg
lemma recurrenceError_secondMoment_le_expectedInverseRisk_of_nonneg
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s h ^ 2 ∂sampleLaw P n) ≤
      weightEnvelope c ^ 2 * c.lambdaMax *
        ∫ t in (0 : ℝ)..(1 - h), ∫ s : Fin n → ObsHistory,
          invRisk a s t ∂sampleLaw P n := by
  exact recurrenceError_secondMoment_le_expectedInverseRisk_of_nonneg_of_assumptions c P
    hP.poissonRecurrence hP.recurrenceBounds hP.randomAssignment hP.recurrenceDeathIndependence
    hP.independentCensoring a n hh hh1


end CausalSmith.Stat.RecurrentEndpointCensorFrontier
