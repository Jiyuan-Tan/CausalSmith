module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedRecurrenceEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRiskSet
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceExposureOrthogonality

/-!
# Full-horizon recurrence oracle moments for the benchmark

Roadmap (25)--(28): bounded inverse retention supplies conditional Poisson
centering and square integrability at time one. Averaging exposure energy
uses the actual randomized risk marginal and yields the recurrence variance.
-/

public section

open MeasureTheory Set
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The observed risk fraction has its exact marginal expectation. -/
-- @node: positiveRetention_integral_riskFraction_eq
lemma positiveRetention_integral_riskFraction_eq
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s : Fin n → ObsHistory, (riskSet a s t : ℝ) / n ∂sampleLaw P n) =
      P.p a * survival P a t * retention P a t := by
  classical
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let A : Set ObsHistory := {o | o.treatment = a ∧ t ≤ o.exit}
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurableSet_le measurable_const measurable_obsHistory_exit)
  have heq := DeathCP.integral_eventCount_eq_binomial (observedLaw P) A hA n
    (fun k => (k : ℝ) / n)
  have hr : (∫ s : Fin n → ObsHistory, (riskSet a s t : ℝ) / n ∂sampleLaw P n) =
      (∑ k ∈ Finset.range (n + 1), binomialWeight n ((observedLaw P).real A) k *
        ((k : ℝ) / n)) := by
    simpa only [sampleLaw, riskSet, A, Set.mem_setOf_eq] using heq
  rw [hr]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, DeathCP.binomial_first_moment]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [mul_div_cancel_left₀ _ hnR]
  exact positiveRetention_observed_arm_risk_probability P hRandom hAssignment hDeath hCensor a ht

/-- The expected observed energy is its deterministic arm-risk integral. -/
-- @node: positiveRetention_observedRecurrence_expected_energy
lemma positiveRetention_observedRecurrence_expected_energy
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P)
    (hCensor : IndependentCensoring P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] {n : ℕ} (hn : 0 < n)
    (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, t ≤ T → |w t| ≤ K) :
    (∫ s : Fin n → ObsHistory, (∑ i : Fin n, ∫ t,
      observedRecurrenceTimeWeight a T w (s i) t ^ 2 ∂recurrenceIntensity P a)
        ∂sampleLaw P n) =
      ∫ t, (if t ≤ T then (n : ℝ) * (P.p a * survival P a t * retention P a t) *
        w t ^ 2 else 0) ∂recurrenceIntensity P a := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hi (s : Fin n → ObsHistory) (i : Fin n) : Integrable
      (fun t => observedRecurrenceTimeWeight a T w (s i) t ^ 2) (recurrenceIntensity P a) := by
    have hm : Measurable (fun t => observedRecurrenceTimeWeight a T w (s i) t) :=
      (measurable_observedRecurrenceTimeWeight a T w hw).comp
      ((measurable_const (a := s i)).prodMk measurable_id)
    apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (K ^ 2)
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2
      (observedRecurrenceTimeWeight_abs_le a T w hK hb _ t)
  have hsum (s : Fin n → ObsHistory) :
      (∑ i : Fin n, ∫ t, observedRecurrenceTimeWeight a T w (s i) t ^ 2
        ∂recurrenceIntensity P a) =
      ∫ t, (if t ≤ T then (riskSet a s t : ℝ) * w t ^ 2 else 0)
        ∂recurrenceIntensity P a := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hi s i)]
    simp_rw [observedRecurrenceTimeWeight_sum_sq]
  simp_rw [hsum]
  rw [integral_integral_swap (observedRecurrence_risk_energy_integrable_prod
    P a n T w hw hK hb)]
  have htν : ∀ᵐ t ∂recurrenceIntensity P a, t ∈ Ioc (0 : ℝ) 1 := by
    have hm : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), t ∈ Ioc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Ioc
    exact (withDensity_absolutelyContinuous _ _).ae_le hm
  apply integral_congr_ae
  filter_upwards [htν] with t ht
  by_cases htT : t ≤ T
  · simp only [htT, if_pos]
    rw [integral_mul_const]
    have hr := positiveRetention_integral_riskFraction_eq P hRandom hAssignment hDeath hCensor a hn ⟨ht.1.le, ht.2⟩
    rw [integral_div] at hr
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [div_eq_iff hnR] at hr
    rw [hr]
    ring
  · simp [htT]

/-- The actual observed localized score is centered and has exact conditional
Poisson energy, with every analytic condition derived from localization. -/
-- @node: positiveRetention_observedRecurrenceScore_moments_of_bound
lemma positiveRetention_observedRecurrenceScore_moments_of_bound
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hRD : RecurrenceDeathIndependence P) (hC : IndependentCensoring P)
    (hPoisson : PoissonRecurrence P) (a : Arm)
    (n : ℕ) (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, t ≤ T → |w t| ≤ K) :
    Integrable (observedRecurrenceScore P a n T w) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T w s ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => observedRecurrenceScore P a n T w s ^ 2) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T w s ^ 2 ∂sampleLaw P n) =
      ∫ e, (∑ i : Fin n, ∫ t, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2 ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  obtain ⟨hν, _⟩ := (hPoisson a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  obtain ⟨hi, he⟩ := observedRecurrenceScore_energy_integrable_of_bound P a n T w hw hK hb
  obtain ⟨hm1, hm0⟩ := observedRecurrenceScore_mean_zero_of_integrable_energy
    P hRandom hRD hC
    hPoisson a n T w hw (Filter.Eventually.of_forall hi) he
  obtain ⟨hm2, he2⟩ := observedRecurrenceScore_second_moment_of_integrable_energy
    P hRandom hRD hC
    hPoisson a n T w hw (Filter.Eventually.of_forall hi) he
  exact ⟨hm1, hm0, hm2, he2⟩


/-- Horizon positivity and antitonicity bound the inverse weight even at
negative times, as needed by the conditional Poisson energy theorem. -/
-- @node: positiveRetention_inv_retention_abs_le_horizon
lemma positiveRetention_inv_retention_abs_le_horizon (c : ClassConstants)
    (P : SubjectLaw) (hHorizon : PositiveHorizonRetention c P) (a : Arm)
    (t : ℝ) (ht : t ≤ 1) : |(retention P a t)⁻¹| ≤ c.Ghor⁻¹ := by
  have hg : c.Ghor ≤ retention P a t :=
    (hHorizon a 1 (by norm_num)).trans (retention_antitone P a ht)
  have hp := c.Ghor_pos.trans_le hg
  rw [abs_of_nonneg (inv_nonneg.mpr hp.le)]
  exact (inv_le_inv₀ hp c.Ghor_pos).2 hg

/-- The full-horizon recurrence oracle is centered and square integrable
under the benchmark assumptions, without smoothness or endpoint-tail premises. -/
-- @node: positiveRetention_recurrenceOracle_full_moments
lemma positiveRetention_recurrenceOracle_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hRD : RecurrenceDeathIndependence P) (hC : IndependentCensoring P)
    (hPoisson : PoissonRecurrence P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (n : ℕ) :
    Integrable (observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹))
      (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s
      ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => observedRecurrenceScore P a n 1
      (fun t => (retention P a t)⁻¹) s ^ 2) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s ^ 2
      ∂sampleLaw P n) =
      ∫ e, (∑ i : Fin n, ∫ t, observedRecurrenceTimeWeight a 1
        (fun t => (retention P a t)⁻¹) (recurrenceExposureHistory (e i)) t ^ 2
          ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  exact positiveRetention_observedRecurrenceScore_moments_of_bound P hRandom hRD hC
    hPoisson a n 1 _ (measurable_retention P a).inv (inv_nonneg.mpr c.Ghor_pos.le)
    (positiveRetention_inv_retention_abs_le_horizon c P hHorizon a)

/-- Averaging the conditional Poisson energy gives the exact recurrence
contribution in roadmap (28), with the observed risk marginal inside Fubini. -/
-- @node: positiveRetention_recurrenceOracle_full_secondMoment
lemma positiveRetention_recurrenceOracle_full_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hAssignment : AssignmentLaw P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (hC : IndependentCensoring P)
    (hPoisson : PoissonRecurrence P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s, observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s ^ 2
      ∂sampleLaw P n) =
      (n : ℝ) * P.p a * ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t := by
  letI : IsFiniteMeasure (recurrenceIntensity P a) := (hPoisson a).2.2.1
  rw [(positiveRetention_recurrenceOracle_full_moments c P hRandom hRD hC hPoisson
    hHorizon a n).2.2.2,
    observedRecurrence_exposure_energy_eq_observed P a n 1 (fun t => (retention P a t)⁻¹) (measurable_retention P a).inv,
    positiveRetention_observedRecurrence_expected_energy P hRandom hAssignment hDeath
      hC a hn 1 (fun t => (retention P a t)⁻¹) (measurable_retention P a).inv (inv_nonneg.mpr c.Ghor_pos.le)
      (positiveRetention_inv_retention_abs_le_horizon c P hHorizon a),
    recurrenceIntensity_integral_truncated P hPoisson a _ (by norm_num) (by norm_num)]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have hg : retention P a t ≠ 0 := (c.Ghor_pos.trans_le (hHorizon a t ht)).ne'
  dsimp only
  field_simp
  <;> ring

/-- The full endpoint inverse-retention recurrence oracle is orthogonal to any
square-integrable exposure coefficient under positive horizon retention. The recurrence
energy hypotheses are derived from the model, not imposed on the oracle. -/
-- @node: positiveRetention_recurrenceOracle_exposure_orthogonal
lemma positiveRetention_recurrenceOracle_exposure_orthogonal
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hRD : RecurrenceDeathIndependence P) (hC : IndependentCensoring P)
    (hPoisson : PoissonRecurrence P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (n : ℕ)
    (g : (Fin n → Arm × (ℝ × ENNReal)) → ℝ) (hg : Measurable g)
    (hg2 : Integrable (fun e => g e ^ 2)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))))) :
    Integrable (fun z : Fin n → LatentSubject =>
      g (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) *
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
          (fun i => observe (z i)))
      (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject,
      g (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) *
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
          (fun i => observe (z i)) ∂Measure.pi (fun _ : Fin n => P.latent)) = 0 := by
  obtain ⟨hν, _⟩ := (hPoisson a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  let w : ℝ → ℝ := fun t => (retention P a t)⁻¹
  have hw : Measurable w := (measurable_retention P a).inv
  let f := fun (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) =>
    observedRecurrenceTimeWeight a 1 w (recurrenceExposureHistory (e i)) t
  have hf (e) (i : Fin n) : Measurable (f e i) :=
    (measurable_observedRecurrenceTimeWeight a 1 w hw).comp
      (measurable_const.prodMk measurable_id)
  obtain ⟨hi, he⟩ := observedRecurrenceScore_energy_integrable_of_bound
    P a n 1 w hw (inv_nonneg.mpr c.Ghor_pos.le)
    (positiveRetention_inv_retention_abs_le_horizon c P hHorizon a)
  have hm := recurrence_latent_exposure_orthogonal_of_integrable_sq
    P hRandom hRD hC
    hPoisson a n f hf (Filter.Eventually.of_forall hi)
    (measurable_observedRecurrenceExposureScore P a n 1 w hw) he g hg hg2
  simpa only [observedRecurrenceScore_eq_latent, f, w] using hm

/-- An observed exposure-only coefficient inherits full-horizon recurrence
orthogonality. Almost-sure factorization accommodates exceptional tied histories. -/
-- @node: positiveRetention_recurrenceOracle_orthogonal_of_exposure
lemma positiveRetention_recurrenceOracle_orthogonal_of_exposure
    (c : ClassConstants) (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hRD : RecurrenceDeathIndependence P) (hC : IndependentCensoring P)
    (hPoisson : PoissonRecurrence P) (hHorizon : PositiveHorizonRetention c P)
    (a : Arm) (n : ℕ)
    (g : (Fin n → Arm × (ℝ × ENNReal)) → ℝ) (hg : Measurable g)
    (hg2 : Integrable (fun e => g e ^ 2)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))))
    (F : (Fin n → ObsHistory) → ℝ) (hF : Measurable F)
    (hfactor : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => P.latent),
      F (fun i => observe (z i)) =
        g (fun j => ((z j).treatment, ((z j).death a, (z j).censor a)))) :
    Integrable (fun s => F s * observedRecurrenceScore P a n 1
      (fun t => (retention P a t)⁻¹) s) (sampleLaw P n) ∧
    (∫ s, F s * observedRecurrenceScore P a n 1
      (fun t => (retention P a t)⁻¹) s ∂sampleLaw P n) = 0 := by
  obtain ⟨hν, _⟩ := (hPoisson a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  obtain ⟨hi, hz⟩ := positiveRetention_recurrenceOracle_exposure_orthogonal
    c P hRandom hRD hC hPoisson hHorizon a n g hg hg2
  have hm := hF.mul (measurable_observedRecurrenceScore P a n 1 _
    (measurable_retention P a).inv)
  have ho : Measurable (fun z : Fin n → LatentSubject =>
      fun i => observe (z i)) := by fun_prop
  have heq : (fun z : Fin n → LatentSubject =>
      g (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) *
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
          (fun i => observe (z i))) =ᵐ[Measure.pi (fun _ : Fin n => P.latent)]
      (fun z => F (fun i => observe (z i)) *
        observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹)
          (fun i => observe (z i))) := by
    filter_upwards [hfactor] with z hz
    rw [hz]
  constructor
  · rw [recurrence_sampleLaw_eq_latent_map]
    exact (integrable_map_measure hm.aestronglyMeasurable ho.aemeasurable).2
      (hi.congr heq)
  · rw [recurrence_sampleLaw_eq_latent_map]
    exact (integral_map ho.aemeasurable hm.aestronglyMeasurable).trans
      ((integral_congr_ae heq.symm).trans hz)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
