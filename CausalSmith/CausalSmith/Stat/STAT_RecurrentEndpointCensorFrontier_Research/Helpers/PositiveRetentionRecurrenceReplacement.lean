module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.OrdinaryRecurrenceOracleReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionOracleMeanEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionOracleMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceOracleTransport

/-! # Positive-retention recurrence oracle replacement

Roadmap (23), (26)--(27): the empirical-minus-oracle coefficient is a single
conditional Poisson score. Bounded horizon retention supplies its integrability;
the proved observable mean-energy limit and Chebyshev make the normalized
latent score negligible. No endpoint Holder or power-tail assumption is used.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Positive horizon retention bounds the entire normalized recurrence
coefficient, so its exposure/time energy is integrable at each sample size. -/
-- @node: positiveRetention_recurrenceOracleDifferenceWeight_energy_integrable_prod
lemma positiveRetention_recurrenceOracleDifferenceWeight_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n : ℕ) :
    Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, recurrenceOracleDifferenceWeight c P a p.1 i p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a)) := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hPoisson a).2.2.1
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let B := Real.sqrt n * weightEnvelope c + c.Ghor⁻¹ / |P.p a * Real.sqrt n|
  have hB : 0 ≤ B := by
    dsimp [B]
    have hW : 0 ≤ weightEnvelope c := by
      unfold weightEnvelope continuationNorm
      positivity
    have hG := c.Ghor_pos.le
    positivity
  apply Integrable.of_bound (by fun_prop) ((n : ℝ) * B ^ 2)
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  calc
    _ ≤ ∑ i : Fin n, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hb : |recurrenceOracleDifferenceWeight c P a p.1 i p.2| ≤ B := by
        unfold recurrenceOracleDifferenceWeight
        apply (abs_sub _ _).trans
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_div]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (remainingRecurrenceWeight_abs_le c a 0 p.1 i p.2) (Real.sqrt_nonneg _)
        · exact div_le_div_of_nonneg_right
            (observedRecurrenceTimeWeight_abs_le a 1 _ (inv_nonneg.mpr c.Ghor_pos.le)
              (positiveRetention_inv_retention_abs_le_horizon c P hHorizon a) _ _)
            (abs_nonneg _)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 hb
    _ = _ := by simp

/-- The normalized latent difference score has its exact conditional Poisson
second moment, retaining the dependence of empirical coefficients on exposure. -/
-- @node: positiveRetention_recurrenceOracleDifferenceScore_latent_secondMoment
lemma positiveRetention_recurrenceOracleDifferenceScore_latent_secondMoment
    (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (fun z : Fin n → LatentSubject =>
      recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) ^ 2) (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject,
      recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) =
      ∫ e, (∑ i : Fin n, ∫ t, recurrenceOracleDifferenceWeight c P a e i t ^ 2
        ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hPoisson a).2.2.1
  obtain ⟨hi, he⟩ := recurrenceJointExposure_energy_conditions P a n
    (recurrenceOracleDifferenceWeight c P a)
    (measurable_recurrenceOracleDifferenceWeight c P a)
    (positiveRetention_recurrenceOracleDifferenceWeight_energy_integrable_prod
      c P hPoisson hHorizon a n)
  exact recurrence_latent_exposure_second_moment_of_integrable_sq P
    hRandom hRD hCensor hPoisson a n (recurrenceOracleDifferenceWeight c P a)
    (fun e i => (measurable_recurrenceOracleDifferenceWeight c P a i).comp
      (measurable_const.prodMk measurable_id)) hi
    (measurable_recurrenceJointExposureScore P a n _
      (measurable_recurrenceOracleDifferenceWeight c P a)) he

/-- Chebyshev bounds the latent normalized difference probability by the
averaged exposure energy divided by the squared threshold. -/
-- @node: positiveRetention_recurrenceOracleDifferenceScore_probability_le_energy
lemma positiveRetention_recurrenceOracleDifferenceScore_probability_le_energy
    (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|} ≤
      (∫ e, (∑ i : Fin n, ∫ t, recurrenceOracleDifferenceWeight c P a e i t ^ 2
        ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) / ε ^ 2 := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let F := fun z : Fin n → LatentSubject =>
    recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)
  obtain ⟨hi, he⟩ := positiveRetention_recurrenceOracleDifferenceScore_latent_secondMoment c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a hn
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun z => sq_nonneg (F z))) hi (ε ^ 2)
  have hsub : {z | ε < |F z|} ⊆ {z | ε ^ 2 ≤ F z ^ 2} := by
    intro z hz
    change ε < |F z| at hz
    change ε ^ 2 ≤ F z ^ 2
    nlinarith [sq_abs (F z)]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  rw [← he]
  simpa only [mul_comm, F] using
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub (by finiteness))
      (sq_nonneg ε)).trans hm

/-- Averaged exposure energy equals observed subject energy by the two
iid pushforward laws and almost-sure integrability of each subject square. -/
-- @node: positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_eq_observed
lemma positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_eq_observed
    (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ e, (∑ i : Fin n, ∫ t, recurrenceOracleDifferenceWeight c P a e i t ^ 2
      ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
    ∫ s : Fin n → ObsHistory, (∫ t, ∑ i : Fin n,
      observedRecurrenceOracleDifferenceWeight c P a s i t ^ 2
      ∂recurrenceIntensity P a) ∂sampleLaw P n := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hPoisson a).2.2.1
  have hi := (recurrenceJointExposure_energy_conditions P a n
    (recurrenceOracleDifferenceWeight c P a)
    (measurable_recurrenceOracleDifferenceWeight c P a)
    (positiveRetention_recurrenceOracleDifferenceWeight_energy_integrable_prod c P hPoisson hHorizon a n)).1
  have hs : (∫ e, (∑ i : Fin n, ∫ t,
      recurrenceOracleDifferenceWeight c P a e i t ^ 2 ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
      ∫ e, (∫ t, ∑ i : Fin n, recurrenceOracleDifferenceWeight c P a e i t ^ 2
        ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
    apply integral_congr_ae
    filter_upwards [hi] with e he
    exact (integral_finsetSum Finset.univ (fun i _ => he i)).symm
  rw [hs]
  let F := fun e : Fin n → Arm × (ℝ × ENNReal) =>
    ∫ t, ∑ i : Fin n, recurrenceOracleDifferenceWeight c P a e i t ^ 2
      ∂recurrenceIntensity P a
  let G := fun s : Fin n → ObsHistory =>
    ∫ t, ∑ i : Fin n, observedRecurrenceOracleDifferenceWeight c P a s i t ^ 2
      ∂recurrenceIntensity P a
  have hF : Measurable F :=
    (Finset.measurable_sum _ (fun i _ =>
      (measurable_recurrenceOracleDifferenceWeight c P a i).pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hG : Measurable G :=
    (Finset.measurable_sum _ (fun i _ =>
      (measurable_observedRecurrenceOracleDifferenceWeight c P a i).pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  let exposure := fun z : Fin n → LatentSubject =>
    fun i => ((z i).treatment, ((z i).death a, (z i).censor a))
  have hmap : (Measure.pi (fun _ : Fin n => P.latent)).map exposure =
      Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.pi_map_pi (fun _ => (show Measurable (fun z : LatentSubject =>
      (z.treatment, (z.death a, z.censor a))) by fun_prop).aemeasurable)
  change (∫ e, F e ∂_) = ∫ s, G s ∂_
  rw [← hmap, integral_map (show Measurable exposure by fun_prop).aemeasurable
    hF.aestronglyMeasurable, recurrence_sampleLaw_eq_latent_map,
    integral_map (show Measurable (fun z : Fin n → LatentSubject =>
      fun i => observe (z i)) by fun_prop).aemeasurable hG.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  dsimp [F, G, exposure]
  simp_rw [observedRecurrenceOracleDifferenceWeight_eq_exposure]

/-- Absolute continuity of recurrence intensity and risk-count cancellation
identify conditional Poisson energy with the observable intensity-weighted energy. -/
-- @node: positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_eq_time
lemma positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_eq_time
    (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ e, (∑ i : Fin n, ∫ t, recurrenceOracleDifferenceWeight c P a e i t ^ 2
      ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
    ∫ s : Fin n → ObsHistory, (∫ t in Icc (0 : ℝ) 1,
      P.lam a t * (((riskSet a s t : ℝ) / n) *
        ((n : ℝ) * deathKMLeft a s t * invRisk a s t -
          1 / (P.p a * retention P a t)) ^ 2)) ∂sampleLaw P n := by
  rw [positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_eq_observed c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a hn]
  apply integral_congr_ae
  filter_upwards [] with s
  unfold recurrenceIntensity
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hPoisson a).1.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [(hPoisson a).2.1,
    ae_restrict_mem measurableSet_Ioc] with t hnonneg ht
  rw [ENNReal.toReal_ofReal hnonneg, smul_eq_mul,
    observedRecurrenceOracleDifferenceWeight_sum_sq c P a hn s ⟨ht.1.le, ht.2⟩]

/-- The averaged conditional Poisson difference energy vanishes by the
proved positive-retention observable mean-energy convergence. -/
-- @node: positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_tendsto_zero
lemma positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ e, (∑ i : Fin n, ∫ t,
      recurrenceOracleDifferenceWeight c P a e i t ^ 2 ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))))
      atTop (nhds 0) := by
  apply (DeathCP.positiveRetention_recurrenceOracleCoefficient_energy_tendsto_zero
    c P hRandom hAssignment hOverlap hDeath hCensor hRecurBounds hDeathBounds hHorizon a).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_eq_time c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a
    (by omega)).symm

/-- The exact conditional Poisson isometry transfers vanishing mean energy
to vanishing second moment of the normalized latent difference score. -/
-- @node: positiveRetention_recurrenceOracleDifferenceScore_latent_secondMoment_tendsto_zero
lemma positiveRetention_recurrenceOracleDifferenceScore_latent_secondMoment_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) :
    Tendsto (fun n : ℕ => ∫ z : Fin n → LatentSubject,
      recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent))
      atTop (nhds 0) := by
  apply (positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_tendsto_zero c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (positiveRetention_recurrenceOracleDifferenceScore_latent_secondMoment c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a (by omega)).2.symm

/-- The root-n latent recurrence replacement error is negligible in
probability, using Chebyshev and the proved mean-energy limit. -/
-- @node: positiveRetention_recurrenceOracleDifferenceScore_latent_probability_tendsto_zero
lemma positiveRetention_recurrenceOracleDifferenceScore_latent_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => P.latent)).real {z |
      ε < |recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a)|}) atTop (nhds 0) := by
  have hlim := (positiveRetention_recurrenceOracleDifferenceWeight_expected_energy_tendsto_zero
    c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a).div_const (ε ^ 2)
  simp only [zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact positiveRetention_recurrenceOracleDifferenceScore_probability_le_energy c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a (by omega) hε

/-- The lower cutoff in the full-window coefficient is immaterial to its
intensity integral, since the intensity is supported on positive study times. -/
-- @node: positiveRetention_remainingRecurrenceWeight_zero_integral_eq
lemma positiveRetention_remainingRecurrenceWeight_zero_integral_eq
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (a : Arm) {n : ℕ} (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) :
    (∫ t, remainingRecurrenceWeight c a 0 e i t ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..1,
        recurrenceSubjectWeight c 0 a (fun j => recurrenceExposureHistory (e j)) i t *
          P.lam a t := by
  unfold recurrenceIntensity
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hPoisson a).1.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [(hPoisson a).2.1, ae_restrict_mem measurableSet_Ioc] with t ht0 ht
  rw [ENNReal.toReal_ofReal ht0, smul_eq_mul]
  simp only [remainingRecurrenceWeight]
  rw [if_pos (show 0 ≤ t ∧ t ≤ 1 from ⟨ht.1.le, ht.2⟩)]
  ring

/-- The actual ordinary recurrence error is the full-window joint exposure
score almost surely. Canonical Poisson points have nonnegative times. -/
-- @node: positiveRetention_recurrenceError_zero_eq_jointExposureScore_ae
lemma positiveRetention_recurrenceError_zero_eq_jointExposureScore_ae
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (a : Arm) (n : ℕ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      recurrenceError c P a (fun i => observe (z i)) 0 =
        recurrenceJointExposureScore P a n (remainingRecurrenceWeight c a 0)
          (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
          (fun j => (z j).recur a) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have hi : ∀ i : Fin n, ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      ∀ k : Fin ((z i).recur a).1, 0 ≤ (((z i).recur a).2 k).1 := by
    intro i
    exact (measurePreserving_eval (μ := fun _ : Fin n => P.latent) i).quasiMeasurePreserving.ae
      (recurrence_latent_ae_nonneg_time P hPoisson a)
  filter_upwards [ae_all_iff.mpr hi] with z hz
  rw [recurrenceError_eq_latent_compensated_scores_of_nonneg_of_assumptions
    c P hPoisson a z (by norm_num) (by norm_num)]
  simp only [sub_zero]
  unfold recurrenceJointExposureScore
  apply Finset.sum_congr rfl
  intro i _
  rw [positiveRetention_remainingRecurrenceWeight_zero_integral_eq c P hPoisson a]
  simp_rw [recurrenceSubjectWeight_eq_exposureHistory]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp [remainingRecurrenceWeight, hz i k]

/-- Linearity of the conditional Poisson score identifies the actual
root-n recurrence error minus its full-horizon oracle. All coefficients are
integrable because horizon retention bounds the oracle. -/
-- @node: positiveRetention_recurrenceError_zero_oracle_difference_eq_latent_score_ae
lemma positiveRetention_recurrenceError_zero_oracle_difference_eq_latent_score_ae
    (c : ClassConstants) (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hHorizon : PositiveHorizonRetention c P) (a : Arm) (n : ℕ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      Real.sqrt n * recurrenceError c P a (fun j => observe (z j)) 0 -
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
          (fun j => observe (z j)) / (P.p a * Real.sqrt n) =
      recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
        (fun j => (z j).recur a) := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hPoisson a).2.2.1
  filter_upwards [positiveRetention_recurrenceError_zero_eq_jointExposureScore_ae
    c P hPoisson a n] with z hz
  rw [hz, observedRecurrenceScore_eq_latent]
  symm
  have hemp (i : Fin n) : Integrable
      (remainingRecurrenceWeight c a 0
        (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i)
      (recurrenceIntensity P a) := by
    apply Integrable.of_bound (by fun_prop) (weightEnvelope c)
    filter_upwards [] with t
    exact remainingRecurrenceWeight_abs_le c a 0 _ i t
  have hor (i : Fin n) : Integrable (fun t => observedRecurrenceTimeWeight a 1
      (fun u => (retention P a u)⁻¹)
      (recurrenceExposureHistory ((z i).treatment, ((z i).death a, (z i).censor a))) t)
      (recurrenceIntensity P a) := by
    refine Integrable.of_bound ?_ c.Ghor⁻¹ ?_
    · exact ((measurable_observedRecurrenceTimeWeight a 1 _
        (measurable_retention P a).inv).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [] with t
      exact observedRecurrenceTimeWeight_abs_le a 1 _ (inv_nonneg.mpr c.Ghor_pos.le)
        (positiveRetention_inv_retention_abs_le_horizon c P hHorizon a) _ t
  simpa only [recurrenceOracleDifferenceWeight, div_eq_mul_inv, mul_comm,
    recurrenceJointExposureScore] using
    recurrenceJointExposureScore_linear_combination P a n
    (remainingRecurrenceWeight c a 0)
    (fun e i t => observedRecurrenceTimeWeight a 1 (fun u => (retention P a u)⁻¹)
      (recurrenceExposureHistory (e i)) t)
    _ (fun j => (z j).recur a) (Real.sqrt n) ((P.p a * Real.sqrt n)⁻¹) hemp hor

/-- The ordinary recurrence martingale has a negligible root-n oracle
replacement error under the benchmark assumptions alone (roadmap (26)). -/
-- @node: positiveRetention_recurrenceError_zero_oracle_difference_probability_tendsto_zero
lemma positiveRetention_recurrenceError_zero_oracle_difference_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * recurrenceError c P a s 0 -
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s /
          (P.p a * Real.sqrt n)|}) atTop (nhds 0) := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hPoisson a).2.2.1
  apply (positiveRetention_recurrenceOracleDifferenceScore_latent_probability_tendsto_zero
    c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a hε).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hm : Measurable (fun s : Fin n → ObsHistory =>
      Real.sqrt n * recurrenceError c P a s 0 -
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s /
          (P.p a * Real.sqrt n)) := by
    have herr := measurable_recurrenceError_of_nonneg_of_assumptions
      c P hPoisson a n (h := 0) (by norm_num) (by norm_num)
    have hor := measurable_observedRecurrenceScore P a n 1 _ (measurable_retention P a).inv
    exact (measurable_const.mul herr).sub (hor.div_const _)
  rw [recurrence_sampleLaw_eq_latent_map]
  simp only [measureReal_def]
  rw [Measure.map_apply
    (show Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) by fun_prop)
    (measurableSet_lt measurable_const hm.abs)]
  congr 1
  apply measure_congr
  filter_upwards [positiveRetention_recurrenceError_zero_oracle_difference_eq_latent_score_ae
    c P hPoisson hHorizon a n] with z hz
  apply propext
  change (ε < |recurrenceJointExposureScore P a n (recurrenceOracleDifferenceWeight c P a)
      (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))
      (fun j => (z j).recur a)|) ↔ _
  rw [← hz]
  rfl


end CausalSmith.Stat.RecurrentEndpointCensorFrontier
