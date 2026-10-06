module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedLocalDensityIdentification

/-! # Full-horizon identification from compact interior intervals -/

public section

open MeasureTheory Set
open scoped ENNReal Interval
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

lemma RecurConfig.countLE_le_count_adapter (s : RecurConfig) (t : ℝ) :
    s.countLE t ≤ s.count := by
  have hsum :
      (∑ i : Fin s.count, if (s.points i).1 ≤ t then 1 else 0) ≤ s.count := by
    calc
      _ ≤ ∑ _i : Fin s.count, 1 :=
        Finset.sum_le_sum (fun i _ ↦ by split_ifs <;> omega)
      _ = s.count := by simp
  convert hsum using 1
  simp [RecurConfig.countLE, RecurConfig.paddedCountLE,
    finiteSamplePaddedStream]
  congr 1

lemma ModelClass.clinicalCount_integrable
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P) (a : Arm) :
    Integrable (fun z : LatentSubject ↦ (clinicalCount z a 1 : ℝ)) P.latent := by
  obtain ⟨_, _, hν, hdist⟩ := hP.poissonRecurrence a
  have hmap : Measure.map FiniteSample.count (@canonicalRecurrenceLaw P a hν) =
      ProbabilityTheory.poissonMeasure
        (finiteMeasureMass (recurrenceIntensity P a)) := by
    simpa [canonicalRecurrenceLaw, canonicalRecurrenceLawOf] using
      finiteMeasureMarkedPoissonLaw_map_count
        (recurrenceIntensity P a) (Measure.dirac 0) (Measure.dirac 0) 1
  have hpoisson :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two
      (finiteMeasureMass (recurrenceIntensity P a))).integrable_sq
  rw [← hmap] at hpoisson
  have hsq : Integrable (fun z : LatentSubject ↦ ((z.recur a).count : ℝ) ^ 2)
      P.latent := by
    have hconfig : Integrable (fun s : RecurConfig ↦ (s.count : ℝ) ^ 2)
        (@canonicalRecurrenceLaw P a hν) :=
      hpoisson.comp_measurable (by fun_prop)
    rw [← hdist] at hconfig
    exact hconfig.comp_measurable (measurable_latentSubject_recur a)
  have hcount : Measurable (fun z : LatentSubject ↦ clinicalCount z a 1) := by
    unfold clinicalCount
    exact RecurConfig.measurable_countLE.comp
      ((measurable_const.min (measurable_latentSubject_death a)).prodMk
        (measurable_latentSubject_recur a))
  apply hsq.mono' (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
    hcount).aestronglyMeasurable)
  filter_upwards with z
  have hleN : clinicalCount z a 1 ≤ (z.recur a).count :=
    RecurConfig.countLE_le_count_adapter _ _
  have hle : (clinicalCount z a 1 : ℝ) ≤ ((z.recur a).count : ℝ) :=
    Nat.cast_le.mpr hleN
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have hnat : ((z.recur a).count : ℝ) ≤ ((z.recur a).count : ℝ) ^ 2 := by
    by_cases hz : (z.recur a).count = 0
    · simp [hz]
    · have hone : (1 : ℝ) ≤ (z.recur a).count := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
      have hnonneg : (0 : ℝ) ≤ (z.recur a).count := by positivity
      nlinarith
  exact hle.trans hnat

/-- The paper armwise clinical-count expectation equals its
survival-weighted recurrence-intensity mean. -/
lemma ModelClass.integral_clinicalCount_eq_armMean
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P) (a : Arm) :
    (∫ z, (clinicalCount z a 1 : ℝ) ∂P.latent) = armMean P a := by
  let M := promotedArmModel P hP a
  letI := M.deathProb
  let F : ℝ → ℝ≥0∞ := fun t ↦
    M.deathLaw (Set.Ici t) * (M.intensity t : ℝ≥0∞)
  have hF : Measurable F := by
    apply Measurable.mul
    · exact Antitone.measurable
        (fun x y hxy ↦ measure_mono (Set.Ici_subset_Ici.mpr hxy))
    · exact M.measurable_intensity.coe_nnreal_ennreal
  have hFtop : ∀ᵐ t ∂volume.restrict (Set.Ico (0 : ℝ) 1), F t < ∞ :=
    Filter.Eventually.of_forall fun t ↦ ENNReal.mul_lt_top
      (measure_lt_top M.deathLaw (Set.Ici t)) ENNReal.coe_lt_top
  have htoReal :
      (∫ t in Set.Ico (0 : ℝ) 1, (F t).toReal ∂volume) =
        (∫⁻ t in Set.Ico (0 : ℝ) 1, F t ∂volume).toReal := by
    exact integral_toReal hF.aemeasurable.restrict hFtop
  have hpoint (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      (F t).toReal = survival P a t * P.lam a t := by
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have hd := hP.deathHazard.2.2.2.1 a t ht'
    have hdmap : M.deathLaw (Set.Ici t) =
        P.latent ((fun z : LatentSubject ↦ z.death a) ⁻¹' Set.Ici t) := by
      rw [promotedArmModel_deathLaw, Measure.map_apply
        (measurable_latentSubject_death a) measurableSet_Ici]
    have hdreal : (M.deathLaw (Set.Ici t)).toReal = survival P a t := by
      rw [hdmap]
      change (P.latent {z : LatentSubject | t ≤ z.death a}).toReal = _
      simpa only [measureReal_def] using hd
    dsimp only [F]
    rw [ENNReal.toReal_mul, hdreal]
    simp only [ENNReal.coe_toReal]
    rw [promotedArmModel_intensity, promotedArmIntensity_coe hP a ht']
  have hformula := hP.lintegral_clinicalCount_eq_promoted_formula a M
    (promotedArmModel_horizon P hP a) (promotedArmModel_time P hP a)
    (promotedArmModel_recurrenceLaw hP a)
    (promotedArmModel_deathLaw P hP a).symm
  have hcountMeas : Measurable
      (fun z : LatentSubject ↦ (clinicalCount z a 1 : ℝ≥0∞)) := by
    exact (measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).comp
      (by
        unfold clinicalCount
        exact RecurConfig.measurable_countLE.comp
          ((measurable_const.min (measurable_latentSubject_death a)).prodMk
            (measurable_latentSubject_recur a)))
  calc
    (∫ z, (clinicalCount z a 1 : ℝ) ∂P.latent) =
        (∫⁻ z, (clinicalCount z a 1 : ℝ≥0∞) ∂P.latent).toReal := by
      simpa using integral_toReal hcountMeas.aemeasurable
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.coe_lt_top)
    _ = (∫⁻ t in Set.Ico (0 : ℝ) 1, F t ∂volume).toReal := by
      rw [hformula]
    _ = ∫ t in Set.Ico (0 : ℝ) 1, (F t).toReal ∂volume := htoReal.symm
    _ = ∫ t in (0 : ℝ)..1, survival P a t * P.lam a t := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      rw [← restrict_Ico_eq_restrict_Ioc]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      exact hpoint t ht
    _ = armMean P a := rfl

lemma ModelClass.armMean_integrand_intervalIntegrable
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P) (a : Arm) :
    IntervalIntegrable (fun t ↦ survival P a t * P.lam a t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  let D : Measure ℝ := P.latent.map (fun z : LatentSubject ↦ z.death a)
  let g : ℝ → ℝ := fun t ↦ (D (Set.Ici t)).toReal * P.lam a t
  have htail : Measurable (fun t : ℝ ↦ (D (Set.Ici t)).toReal) :=
    (Antitone.measurable
      (fun x y hxy ↦ measure_mono (Set.Ici_subset_Ici.mpr hxy))).ennreal_toReal
  have hlam := (hP.poissonRecurrence a).1
  have hg : AEStronglyMeasurable g (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (htail.aemeasurable.mul hlam).aestronglyMeasurable
  have hae : (fun t ↦ survival P a t * P.lam a t) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hd := hP.deathHazard.2.2.2.1 a t ⟨ht.1.le, ht.2⟩
    have hD : (D (Set.Ici t)).toReal = survival P a t := by
      unfold D
      rw [Measure.map_apply (measurable_latentSubject_death a) measurableSet_Ici]
      change (P.latent {z : LatentSubject | t ≤ z.death a}).toReal = _
      simpa only [measureReal_def] using hd
    simp only [g, hD]
  have hconst : IntegrableOn (fun _ : ℝ ↦ c.lambdaMax)
      (Set.Ioc (0 : ℝ) 1) volume := by
    exact integrableOn_const (by simp [Real.volume_Ioc])
  apply hconst.mono' (hg.congr hae.symm)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hsnonneg : 0 ≤ survival P a t := by
    unfold survival
    positivity
  have hsle : survival P a t ≤ 1 := by
    letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
    have hd := hP.deathHazard.2.2.2.1 a t ht'
    rw [← hd]
    exact measureReal_le_one
  have hl := (hP.recurrenceBounds a t ht').1
  have hu := (hP.recurrenceBounds a t ht').2
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsnonneg
    (c.lambdaMin_pos.le.trans hl)),
    abs_of_nonneg (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)]
  calc
    survival P a t * P.lam a t ≤ 1 * P.lam a t :=
      mul_le_mul_of_nonneg_right hsle (c.lambdaMin_pos.le.trans hl)
    _ = P.lam a t := one_mul _
    _ ≤ c.lambdaMax := hu

lemma ModelClass.causalTarget_eq_survival_intensity_contrast
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P) :
    causalTarget P =
      ∫ t in (0 : ℝ)..1,
        (survival P true t * P.lam true t -
          survival P false t * P.lam false t) := by
  unfold causalTarget
  rw [integral_sub (hP.clinicalCount_integrable true)
    (hP.clinicalCount_integrable false),
    hP.integral_clinicalCount_eq_armMean true,
    hP.integral_clinicalCount_eq_armMean false]
  unfold armMean
  rw [intervalIntegral.integral_sub
    (hP.armMean_integrand_intervalIntegrable true)
    (hP.armMean_integrand_intervalIntegrable false)]

/-- Equality on every compact sub-horizon interval and continuity identify
both paper densities on the closed study horizon, including time one. -/
lemma ModelClass.densities_eqOn_horizon_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm) :
    Set.EqOn (P.hazard a) (Q.hazard a) (Set.Icc (0 : ℝ) 1) ∧
      Set.EqOn (P.lam a) (Q.lam a) (Set.Icc (0 : ℝ) 1) := by
  have hinterior :
      Set.EqOn (P.hazard a) (Q.hazard a) (Set.Ico (0 : ℝ) 1) ∧
        Set.EqOn (P.lam a) (Q.lam a) (Set.Ico (0 : ℝ) 1) := by
    constructor <;> intro t ht
    · let T := (t + 1) / 2
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t < 1 := ht.2
      have hT0 : 0 < T := by dsimp [T]; linarith
      have hT1 : T < 1 := by dsimp [T]; linarith
      have htT : t ∈ Set.Icc (0 : ℝ) T := by
        constructor
        · exact ht.1
        · dsimp [T]
          linarith
      exact (hP.densities_eqOn_of_observedLaw_eq hQ hobs a hT0 hT1).1 htT
    · let T := (t + 1) / 2
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t < 1 := ht.2
      have hT0 : 0 < T := by dsimp [T]; linarith
      have hT1 : T < 1 := by dsimp [T]; linarith
      have htT : t ∈ Set.Icc (0 : ℝ) T := by
        constructor
        · exact ht.1
        · dsimp [T]
          linarith
      exact (hP.densities_eqOn_of_observedLaw_eq hQ hobs a hT0 hT1).2 htT
  have hsub : Set.Ico (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := fun _ ht ↦ ⟨ht.1, ht.2.le⟩
  have hclosure : Set.Icc (0 : ℝ) 1 ⊆ closure (Set.Ico (0 : ℝ) 1) := by
    rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
  constructor
  · exact hinterior.1.of_subset_closure
      (hP.deathContinuousOn a) (hQ.deathContinuousOn a) hsub hclosure
  · exact hinterior.2.of_subset_closure
      (hP.recurrenceContinuousOn a) (hQ.recurrenceContinuousOn a) hsub hclosure

/-- Exact frozen identification conclusions concerning all interior points and
the endpoint, separated from the target-mean identity. -/
lemma ModelClass.frozen_density_identification_conjuncts
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) :
    ∀ P' : SubjectLaw, ModelClass c P' → observedLaw P = observedLaw P' →
      (∀ ε : ℝ, 0 < ε → ∀ a : Arm,
        ∀ t ∈ Set.Icc (0 : ℝ) (1 - ε),
          P.lam a t = P'.lam a t ∧ P.hazard a t = P'.hazard a t) ∧
      (∀ a : Arm, P.lam a 1 = P'.lam a 1 ∧
        P.hazard a 1 = P'.hazard a 1) := by
  intro P' hP' hobs
  have hfull (a : Arm) := hP.densities_eqOn_horizon_of_observedLaw_eq hP' hobs a
  constructor
  · intro ε hε a t ht
    by_cases htop : 1 - ε < 0
    · exfalso
      linarith [ht.1, ht.2]
    · have htH : t ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨ht.1, ht.2.trans (by linarith)⟩
      exact ⟨(hfull a).2 htH, (hfull a).1 htH⟩
  · intro a
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    exact ⟨(hfull a).2 h1, (hfull a).1 h1⟩

/-- Equal observed laws identify the causal target once the armwise density
fields have been identified on the closed horizon. -/
lemma ModelClass.causalTarget_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) :
    causalTarget P = causalTarget Q := by
  rw [hP.causalTarget_eq_survival_intensity_contrast,
    hQ.causalTarget_eq_survival_intensity_contrast]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have hfield (a : Arm) :=
    hP.densities_eqOn_horizon_of_observedLaw_eq hQ hobs a
  have hsurv (a : Arm) : survival P a t = survival Q a t := by
    unfold survival
    congr 2
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
      have hut : u ∈ Set.uIcc (0 : ℝ) t := hu
      rw [Set.uIcc_of_le ht'.1] at hut
      exact ⟨hut.1, hut.2.trans ht'.2⟩
    exact (hfield a).1 hu'
  change survival P true t * P.lam true t -
      survival P false t * P.lam false t =
    survival Q true t * Q.lam true t -
      survival Q false t * Q.lam false t
  rw [hsurv true, hsurv false, (hfield true).2 ht', (hfield false).2 ht']

/-- Exact adapter matching the frozen `causal_identification` theorem body. -/
theorem causal_identification_adapter (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) :
    causalTarget P =
      ∫ t in (0 : ℝ)..1,
        (survival P true t * P.lam true t -
          survival P false t * P.lam false t) ∧
    (∀ P' : SubjectLaw, ModelClass c P' →
      observedLaw P = observedLaw P' →
      (∀ ε : ℝ, 0 < ε → ∀ a : Arm,
        ∀ t ∈ Set.Icc (0 : ℝ) (1 - ε),
          P.lam a t = P'.lam a t ∧ P.hazard a t = P'.hazard a t) ∧
      (∀ a : Arm, P.lam a 1 = P'.lam a 1 ∧
        P.hazard a 1 = P'.hazard a 1) ∧
      causalTarget P = causalTarget P') := by
  refine ⟨hP.causalTarget_eq_survival_intensity_contrast, ?_⟩
  intro P' hP' hobs
  obtain ⟨hint, hend⟩ :=
    ModelClass.frozen_density_identification_conjuncts c P hP P' hP' hobs
  exact ⟨hint, hend, hP.causalTarget_eq_of_observedLaw_eq hP' hobs⟩


end CausalSmith.Stat.RecurrentEndpointCensorFrontier
