module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedRecurrenceMoments
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalCoefficientEnergy

/-!
# Localized observed recurrence variance

The observed subject-weight energy cancels to the risk count. Fubini and the
exact arm risk marginal then identify the deterministic variance integral.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Summing exposed squared deterministic weights gives the actual risk count,
with the localization cutoff retained. -/
-- @node: observedRecurrenceTimeWeight_sum_sq
lemma observedRecurrenceTimeWeight_sum_sq (a : Arm) (T : ℝ) (w : ℝ → ℝ)
    {n : ℕ} (s : Fin n → ObsHistory) (t : ℝ) :
    (∑ i : Fin n, observedRecurrenceTimeWeight a T w (s i) t ^ 2) =
      if t ≤ T then (riskSet a s t : ℝ) * w t ^ 2 else 0 := by
  classical
  by_cases ht : t ≤ T
  · simp only [observedRecurrenceTimeWeight, ht, and_true, if_pos]
    simp only [ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
    rw [← Finset.sum_filter]
    simp [riskSet]
  · simp [observedRecurrenceTimeWeight, ht]

/-- Exposure-only and observed subject-weight energies agree under their
respective iid laws. This is transport, not an independence assertion. -/
-- @node: observedRecurrence_exposure_energy_eq_observed
lemma observedRecurrence_exposure_energy_eq_observed
    (P : SubjectLaw) (a : Arm) [IsFiniteMeasure (recurrenceIntensity P a)]
    (n : ℕ) (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w) :
    (∫ e, (∑ i : Fin n, ∫ t, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2 ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
      ∫ s : Fin n → ObsHistory, (∑ i : Fin n, ∫ t,
        observedRecurrenceTimeWeight a T w (s i) t ^ 2 ∂recurrenceIntensity P a)
        ∂sampleLaw P n := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let energy := fun s : Fin n → ObsHistory => ∑ i : Fin n,
    ∫ t, observedRecurrenceTimeWeight a T w (s i) t ^ 2 ∂recurrenceIntensity P a
  have hi : Measurable (fun o =>
      ∫ t, observedRecurrenceTimeWeight a T w o t ^ 2 ∂recurrenceIntensity P a) :=
    ((measurable_observedRecurrenceTimeWeight a T w hw).pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  have he : Measurable energy := Finset.measurable_sum _ (fun i _ =>
    hi.comp (measurable_pi_apply i))
  have hE : Measurable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
      energy (fun j => recurrenceExposureHistory (e j))) := by fun_prop
  let exposure := fun z : Fin n → LatentSubject =>
    fun i => ((z i).treatment, ((z i).death a, (z i).censor a))
  have hmap : (Measure.pi (fun _ : Fin n => P.latent)).map exposure =
      Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.pi_map_pi (fun _ => (show Measurable (fun z : LatentSubject =>
      (z.treatment, (z.death a, z.censor a))) by fun_prop).aemeasurable)
  change (∫ e : Fin n → Arm × (ℝ × ENNReal), energy (fun j => recurrenceExposureHistory (e j)) ∂_) = ∫ s, energy s ∂_
  rw [← hmap, integral_map (show Measurable exposure by fun_prop).aemeasurable
    hE.aestronglyMeasurable, recurrence_sampleLaw_eq_latent_map,
    integral_map (show Measurable (fun z : Fin n → LatentSubject =>
      fun i => observe (z i)) by fun_prop).aemeasurable he.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ha : (z i).treatment = a <;>
    simp [observedRecurrenceTimeWeight, exposure, recurrenceExposureHistory, observe,
      censorHorizon, ha]

/-- For bounded localization, the risk-count energy is integrable on the
sample/time product measure. This justifies swapping the two integrals. -/
-- @node: observedRecurrence_risk_energy_integrable_prod
lemma observedRecurrence_risk_energy_integrable_prod
    (P : SubjectLaw) (a : Arm) [IsFiniteMeasure (recurrenceIntensity P a)]
    (n : ℕ) (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, t ≤ T → |w t| ≤ K) :
    Integrable (fun p : (Fin n → ObsHistory) × ℝ =>
      if p.2 ≤ T then (riskSet a p.1 p.2 : ℝ) * w p.2 ^ 2 else 0)
      ((sampleLaw P n).prod (recurrenceIntensity P a)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hm : Measurable (fun p : (Fin n → ObsHistory) × ℝ =>
      if p.2 ≤ T then (riskSet a p.1 p.2 : ℝ) * w p.2 ^ 2 else 0) := by
    apply Measurable.ite (measurableSet_le measurable_snd measurable_const)
    · have hr : Measurable (fun p : (Fin n → ObsHistory) × ℝ => (riskSet a p.1 p.2 : ℝ)) := by fun_prop
      exact hr.mul ((hw.comp measurable_snd).pow_const 2)
    · exact measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable ((n : ℝ) * K ^ 2)
  filter_upwards [] with p
  by_cases ht : p.2 ≤ T
  · rw [if_pos ht, Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul
    · have hr : riskSet a p.1 p.2 ≤ n := by
        unfold riskSet
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
      exact_mod_cast hr
    · simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 (hb p.2 ht)
    · positivity
    · positivity
  · rw [if_neg ht, norm_zero]
    positivity

/-- The expected observed energy is its deterministic arm-risk integral. -/
-- @node: observedRecurrence_expected_energy
lemma observedRecurrence_expected_energy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
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
    have hr := DeathCP.observed_integral_riskFraction_eq c P hP a hn ⟨ht.1.le, ht.2⟩
    rw [integral_div] at hr
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [div_eq_iff hnR] at hr
    rw [hr]
    ring
  · simp [htT]

/-- Exact observed recurrence energy reduces to the deterministic risk
integral, with the original time-dependent weight inside the integral. -/
-- @node: observedRecurrenceScore_secondMoment_eq_risk_integral
lemma observedRecurrenceScore_secondMoment_eq_risk_integral
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (w : ℝ → ℝ) (hw : Measurable w)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, t ≤ T → |w t| ≤ K) :
    (∫ s, observedRecurrenceScore P a n T w s ^ 2 ∂sampleLaw P n) =
      (n : ℝ) * P.p a * ∫ t in (0 : ℝ)..T,
        survival P a t * retention P a t * w t ^ 2 * P.lam a t := by
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  rw [(observedRecurrenceScore_moments_of_bound c P hP a n T w hw hK hb).2.2.2,
    observedRecurrence_exposure_energy_eq_observed P a n T w hw,
    observedRecurrence_expected_energy c P hP a hn T w hw hK hb,
    recurrenceIntensity_integral_truncated P hP.poissonRecurrence a _ hT0 hT1]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-- The localized inverse-retention recurrence oracle has exactly the
recurrence contribution in roadmap (24), before endpoint passage. -/
-- @node: observedRecurrenceScore_invRetention_secondMoment
lemma observedRecurrenceScore_invRetention_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    (∫ s, observedRecurrenceScore P a n T (fun t => (retention P a t)⁻¹) s ^ 2
      ∂sampleLaw P n) =
      (n : ℝ) * P.p a * ∫ t in (0 : ℝ)..T,
        survival P a t * P.lam a t / retention P a t := by
  have hg : 0 < retention P a T := retention_pos_of_modelClass c P hP a T hT0 hT1
  have hb : ∀ t, t ≤ T → |(retention P a t)⁻¹| ≤ (retention P a T)⁻¹ := by
    intro t ht
    rw [abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ retention P a t from measureReal_nonneg))]
    exact (inv_le_inv₀ (hg.trans_le (retention_antitone P a ht)) hg).2
      (retention_antitone P a ht)
  rw [observedRecurrenceScore_secondMoment_eq_risk_integral c P hP a hn hT0 hT1.le
    (fun t => (retention P a t)⁻¹) (measurable_retention P a).inv (inv_nonneg.mpr hg.le) hb]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT0] at ht
  have hgt : retention P a t ≠ 0 :=
    (retention_pos_of_modelClass c P hP a t ht.1 (ht.2.trans_lt hT1)).ne'
  dsimp
  field_simp

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
