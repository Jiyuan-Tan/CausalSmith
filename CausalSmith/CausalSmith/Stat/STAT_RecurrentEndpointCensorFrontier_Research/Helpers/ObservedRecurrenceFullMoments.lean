module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedRecurrenceEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalOracleEnergy

/-!
# Observed recurrence moments from integrable exposure energy

Roadmap (2), (6), and (24): Fubini supplies conditional square integrability
and averaged energy for unbounded deterministic oracle weights. No independent
factorization of exposure and the recurrence score is used.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Product energy supplies the two analytic conditions of the unbounded
Poisson transport theorem, even without a uniform bound on the time weight. -/
-- @node: observedRecurrenceScore_energy_conditions_of_integrable_prod
lemma observedRecurrenceScore_energy_conditions_of_integrable_prod
    (P : SubjectLaw) (a : Arm) [IsFiniteMeasure (recurrenceIntensity P a)]
    (n : ℕ) (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hprod : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (p.1 i)) p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a))) :
    (∀ᵐ e ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))),
      ∀ i, Integrable (fun t => observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2) (recurrenceIntensity P a)) ∧
    Integrable (fun e => ∑ i : Fin n, ∫ t,
        observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e i)) t ^ 2
          ∂recurrenceIntensity P a)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsFiniteMeasure (Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) := by
    infer_instance
  letI : SigmaFinite (Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) :=
    IsFiniteMeasure.toSigmaFinite _
  have hslice := hprod.prod_right_ae
  have hi : ∀ᵐ e ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))),
      ∀ i, Integrable (fun t => observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2) (recurrenceIntensity P a) := by
    filter_upwards [hslice] with e he
    intro i
    apply he.mono' (by fun_prop)
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun j _ => sq_nonneg
      (observedRecurrenceTimeWeight a T w (recurrenceExposureHistory (e j)) t))
      (Finset.mem_univ i)
  refine ⟨hi, hprod.integral_prod_left.congr ?_⟩
  filter_upwards [hi] with e he
  exact integral_finsetSum Finset.univ (fun i _ => he i)

/-- Integrable exposure energy gives actual observed centering and second
moments for arbitrary measurable deterministic time weights. -/
-- @node: observedRecurrenceScore_moments_of_integrable_prod
lemma observedRecurrenceScore_moments_of_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    (n : ℕ) (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hprod : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (p.1 i)) p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a))) :
    Integrable (observedRecurrenceScore P a n T w) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T w s ∂sampleLaw P n) = 0 ∧
    Integrable (fun s => observedRecurrenceScore P a n T w s ^ 2) (sampleLaw P n) ∧
    (∫ s, observedRecurrenceScore P a n T w s ^ 2 ∂sampleLaw P n) =
      ∫ e, (∑ i : Fin n, ∫ t, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2 ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  obtain ⟨hi, he⟩ := observedRecurrenceScore_energy_conditions_of_integrable_prod
    P a n T w hw hprod
  obtain ⟨hm1, hm0⟩ := observedRecurrenceScore_mean_zero_of_integrable_energy
    P hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n T w hw hi he
  obtain ⟨hm2, he2⟩ := observedRecurrenceScore_second_moment_of_integrable_energy
    P hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n T w hw hi he
  exact ⟨hm1, hm0, hm2, he2⟩

/-- The exposure energy at a fixed time equals its observed risk marginal.
This is a pushforward identity and does not factor random coefficients. -/
-- @node: observedRecurrence_exposure_energy_marginal
lemma observedRecurrence_exposure_energy_marginal
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (T : ℝ) (w : ℝ → ℝ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ e, (∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
      if t ≤ T then (n : ℝ) * (P.p a * survival P a t * retention P a t) *
        w t ^ 2 else 0 := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let exposure := fun z : Fin n → LatentSubject =>
    fun i => ((z i).treatment, ((z i).death a, (z i).censor a))
  have hmap : (Measure.pi (fun _ : Fin n => P.latent)).map exposure =
      Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.pi_map_pi (fun _ => (show Measurable (fun z : LatentSubject =>
      (z.treatment, (z.death a, z.censor a))) by fun_prop).aemeasurable)
  have hm : Measurable (fun s : Fin n → ObsHistory =>
      ∑ i : Fin n, observedRecurrenceTimeWeight a T w (s i) t ^ 2) := by
    apply Finset.measurable_sum
    intro i _
    have hconst : Measurable (fun s : Fin n → ObsHistory =>
        observedRecurrenceTimeWeight a T (fun _ => w t) (s i) t) :=
      (measurable_observedRecurrenceTimeWeight a T (fun _ => w t)
        measurable_const).comp (show Measurable (fun s : Fin n → ObsHistory => (s i, t)) from
          (measurable_pi_apply i).prodMk measurable_const)
    simpa only [observedRecurrenceTimeWeight] using hconst.pow_const 2
  have he : Measurable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
      ∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2) := by
    exact hm.comp (by fun_prop)
  have heq : (∫ e, (∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
      ∫ s : Fin n → ObsHistory,
        (∑ i : Fin n, observedRecurrenceTimeWeight a T w (s i) t ^ 2)
          ∂sampleLaw P n := by
    rw [← hmap, integral_map (show Measurable exposure by fun_prop).aemeasurable
      he.aestronglyMeasurable, recurrence_sampleLaw_eq_latent_map,
      integral_map (show Measurable (fun z : Fin n → LatentSubject =>
        fun i => observe (z i)) by fun_prop).aemeasurable hm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with z
    apply Finset.sum_congr rfl
    intro i _
    by_cases ha : (z i).treatment = a <;>
      simp [observedRecurrenceTimeWeight, exposure, recurrenceExposureHistory,
        observe, censorHorizon, ha]
  rw [heq]
  simp_rw [observedRecurrenceTimeWeight_sum_sq]
  by_cases hT : t ≤ T
  · simp only [hT, if_pos]
    rw [integral_mul_const]
    have hr := DeathCP.observed_integral_riskFraction_eq c P hP a hn ht
    rw [integral_div, div_eq_iff (Nat.cast_ne_zero.mpr hn.ne')] at hr
    rw [hr]
    ring
  · simp [hT]

/-- Integrability of the deterministic marginal supplies product exposure
energy. At each time the sample slice is bounded; no uniform time bound is used. -/
-- @node: observedRecurrence_exposure_energy_integrable_prod_of_marginal
lemma observedRecurrence_exposure_energy_integrable_prod_of_marginal
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] {n : ℕ} (hn : 0 < n)
    (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hmarg : Integrable (fun t => if t ≤ T then
      (n : ℝ) * (P.p a * survival P a t * retention P a t) * w t ^ 2 else 0)
      (recurrenceIntensity P a)) :
    Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (p.1 i)) p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsFiniteMeasure (Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) := by
    infer_instance
  letI : SigmaFinite (Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) :=
    IsFiniteMeasure.toSigmaFinite _
  have hm : Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (p.1 i)) p.2 ^ 2) := by fun_prop
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with t
    apply Integrable.of_bound
      ((hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      ((n : ℝ) * |w t| ^ 2)
    filter_upwards [] with e
    dsimp only [Function.comp_def, id_eq]
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    calc
      _ ≤ ∑ _i : Fin n, |w t| ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        unfold observedRecurrenceTimeWeight
        split_ifs <;> simp only [sq_abs, zero_pow (by norm_num : 2 ≠ 0)] <;> first | rfl | positivity
      _ = _ := by simp
  · apply hmarg.congr
    have htν : ∀ᵐ t ∂recurrenceIntensity P a, t ∈ Ioc (0 : ℝ) 1 :=
      (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [htν] with t ht
    simp_rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    exact (observedRecurrence_exposure_energy_marginal c P hP a hn T w t
      ⟨ht.1.le, ht.2⟩).symm

/-- Subcritical overlap makes the full endpoint recurrence marginal integrable.
One inverse-retention factor cancels before integration. -/
-- @node: observedRecurrence_invRetention_marginal_integrable
lemma observedRecurrence_invRetention_marginal_integrable
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) (n : ℕ) :
    Integrable (fun t => if t ≤ 1 then
      (n : ℝ) * (P.p a * survival P a t * retention P a t) *
        (retention P a t)⁻¹ ^ 2 else 0) (recurrenceIntensity P a) := by
  unfold recurrenceIntensity
  rw [integrable_withDensity_iff_integrable_smul₀'
    (hP.poissonRecurrence a).1.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hi := (subcritical_recurrence_energy_intervalIntegrable c P hP hk a).const_mul
    ((n : ℝ) * P.p a)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc, (hP.poissonRecurrence a).2.1]
    with t ht hLam
  simp only [ENNReal.toReal_ofReal hLam, smul_eq_mul, if_pos ht.2]
  by_cases hG : retention P a t = 0
  · simp [hG]
  · field_simp

/-- The unbounded endpoint oracle satisfies product exposure integrability
under the model's subcritical tail condition alone. -/
-- @node: observedRecurrence_invRetention_exposure_energy_integrable_prod
lemma observedRecurrence_invRetention_exposure_energy_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, observedRecurrenceTimeWeight a 1 (fun t => (retention P a t)⁻¹)
        (recurrenceExposureHistory (p.1 i)) p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a)) := by
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  exact observedRecurrence_exposure_energy_integrable_prod_of_marginal
    c P hP a hn 1 _ (measurable_retention P a).inv
    (observedRecurrence_invRetention_marginal_integrable c P hP hk a n)

/-- Full-horizon observed inverse-retention scores are centered and square
integrable. Conditional Poisson transport applies to the endpoint weight itself. -/
-- @node: observedRecurrenceScore_invRetention_full_moments
lemma observedRecurrenceScore_invRetention_full_moments
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
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
  exact observedRecurrenceScore_moments_of_integrable_prod c P hP a n 1 _
    (measurable_retention P a).inv
    (observedRecurrence_invRetention_exposure_energy_integrable_prod c P hP hk a hn)

/-- Integrable product energy permits Fubini for the unbounded exposure
weights, yielding the exact deterministic risk integral. -/
-- @node: observedRecurrence_exposure_expected_energy_of_integrable_prod
lemma observedRecurrence_exposure_expected_energy_of_integrable_prod
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] {n : ℕ} (hn : 0 < n)
    (T : ℝ) (w : ℝ → ℝ) (hw : Measurable w)
    (hprod : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × ℝ =>
      ∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (p.1 i)) p.2 ^ 2)
      ((Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
          (recurrenceIntensity P a))) :
    (∫ e, (∑ i : Fin n, ∫ t, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2 ∂recurrenceIntensity P a)
      ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) =
      ∫ t, (if t ≤ T then (n : ℝ) * (P.p a * survival P a t * retention P a t) *
        w t ^ 2 else 0) ∂recurrenceIntensity P a := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsFiniteMeasure (Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) := by
    infer_instance
  letI : SigmaFinite (Measure.pi (fun _ : Fin n => P.latent.map
      (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))) :=
    IsFiniteMeasure.toSigmaFinite _
  have hi := (observedRecurrenceScore_energy_conditions_of_integrable_prod
    P a n T w hw hprod).1
  calc
    _ = ∫ e, (∫ t, ∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2 ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
      apply integral_congr_ae
      filter_upwards [hi] with e he
      exact (integral_finsetSum Finset.univ (fun i _ => he i)).symm
    _ = ∫ t, (∫ e, ∑ i : Fin n, observedRecurrenceTimeWeight a T w
        (recurrenceExposureHistory (e i)) t ^ 2
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))))
        ∂recurrenceIntensity P a := integral_integral_swap hprod
    _ = _ := by
      have htν : ∀ᵐ t ∂recurrenceIntensity P a, t ∈ Ioc (0 : ℝ) 1 :=
        (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)
      apply integral_congr_ae
      filter_upwards [htν] with t ht
      exact observedRecurrence_exposure_energy_marginal c P hP a hn T w t ⟨ht.1.le, ht.2⟩

/-- The full observed endpoint recurrence oracle has exactly its variance
contribution, with the unbounded weight justified by subcritical overlap. -/
-- @node: observedRecurrenceScore_invRetention_full_secondMoment
lemma observedRecurrenceScore_invRetention_full_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    (∫ s, observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s ^ 2
      ∂sampleLaw P n) =
      (n : ℝ) * P.p a * ∫ t in (0 : ℝ)..1,
        survival P a t * P.lam a t / retention P a t := by
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  rw [(observedRecurrenceScore_invRetention_full_moments c P hP hk a hn).2.2.2,
    observedRecurrence_exposure_expected_energy_of_integrable_prod c P hP a hn 1
      (fun t => (retention P a t)⁻¹)
      (measurable_retention P a).inv
      (observedRecurrence_invRetention_exposure_energy_integrable_prod c P hP hk a hn),
    recurrenceIntensity_integral_truncated P hP.poissonRecurrence a _
      (by norm_num : (0 : ℝ) ≤ 1) le_rfl,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases hG : retention P a t = 0
  · simp [hG]
  · field_simp

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
