module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionProjection
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedFullIdentification

/-!
# Clinical target identification under benchmark assumptions

Campbell's formula for the canonical Poisson configuration and independence
of death identify the clinical count mean without endpoint smoothness or a
tail assumption. The non-strict count convention is retained throughout.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The canonical Poisson count through a fixed time has mean equal to the
primitive intensity of that time interval, including the boundary. -/
-- @node: canonicalRecurrenceLaw_lintegral_countLE
lemma canonicalRecurrenceLaw_lintegral_countLE (P : SubjectLaw) (a : Arm)
    [hν : IsFiniteMeasure (recurrenceIntensity P a)] (r : ℝ) :
    (∫⁻ s, (s.countLE r : ℝ≥0∞) ∂canonicalRecurrenceLaw P a) =
      recurrenceIntensity P a (Iic r) := by
  let ν := recurrenceIntensity P a
  let Q := normalizedFiniteMeasure ν (Measure.dirac (0 : ℝ))
  let rate := finiteMeasureMass ν
  letI : IsProbabilityMeasure (Measure.dirac (0 : ℝ)) := inferInstance
  letI : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  let f : ℝ → ℝ≥0∞ := (Iic r).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator measurableSet_Iic
  have hc := Causalean.Stat.RecurrentEvent.finitePoissonSample_lintegral_sum
    (Q.prod (Measure.dirac (0 : ℝ))) rate (fun x => f x.1) (hf.comp measurable_fst)
  have hmap : Measure.map Prod.fst
      ((rate : ℝ≥0∞) • Q.prod (Measure.dirac (0 : ℝ))) = ν := by
    rw [Measure.map_smul, Measure.map_fst_prod, measure_univ, one_smul,
      ← ENNReal.smul_def, normalizedFiniteMeasure_reconstruct]
  have hr : (∫⁻ x, f x.1 ∂((rate : ℝ≥0∞) • Q.prod (Measure.dirac (0 : ℝ)))) =
      ν (Iic r) := by
    rw [← lintegral_map hf measurable_fst, hmap, lintegral_indicator measurableSet_Iic]
    simp
  rw [show canonicalRecurrenceLaw P a =
      finitePoissonSampleLaw (Q.prod (Measure.dirac (0 : ℝ))) rate by
    unfold canonicalRecurrenceLaw canonicalRecurrenceLawOf
      finiteMeasureMarkedPoissonLaw finiteMarkedPoissonSampleLaw
    simp only [one_mul, Q, rate, ν]]
  convert hc.trans hr using 1
  apply lintegral_congr
  rintro ⟨k, x⟩
  simp only [RecurConfig.countLE, RecurConfig.paddedCountLE, finiteSamplePaddedStream]
  simp only [f, Set.indicator, Set.mem_Iic]
  norm_cast
  simp only [FiniteSample.count, FiniteSample.points]
  apply Finset.sum_congr rfl
  intro i _
  simp [FiniteSample.count, FiniteSample.points, i.isLt]

/-- Independent death turns the fixed-time Campbell mean into the
survival-weighted recurrence-intensity mean of the clinical horizon count. -/
-- @node: positiveRetention_lintegral_clinicalCount
lemma positiveRetention_lintegral_clinicalCount (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (hRD : RecurrenceDeathIndependence P) (a : Arm) :
    (∫⁻ z, (clinicalCount z a 1 : ℝ≥0∞) ∂P.latent) =
      ∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (P.lam a t) *
          (P.latent.map (fun z => z.death a)) (Ici t) := by
  obtain ⟨hlam, _, hν, hmarg⟩ := hPoisson a
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (canonicalRecurrenceLaw P a) := by
    rw [← hmarg]
    exact Measure.isProbabilityMeasure_map (measurable_latentSubject_recur a).aemeasurable
  let D := P.latent.map (fun z => z.death a)
  letI : IsProbabilityMeasure D :=
    Measure.isProbabilityMeasure_map (measurable_latentSubject_death a).aemeasurable
  let C : RecurConfig × ℝ → ℝ≥0∞ := fun q => (q.1.countLE (min 1 q.2) : ℝ≥0∞)
  have hC : Measurable C :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      (RecurConfig.measurable_countLE.comp
        ((measurable_const.min measurable_snd).prodMk measurable_fst))
  let f : ℝ × ℝ → ℝ≥0∞ := fun q => if q.2 ≤ min 1 q.1 then 1 else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_le measurable_snd (measurable_const.min measurable_fst))
    measurable_const measurable_const
  calc
    _ = ∫⁻ q, C q ∂(P.latent.map (fun z => (z.recur a, z.death a))) := by
      rw [lintegral_map hC ((measurable_latentSubject_recur a).prodMk
        (measurable_latentSubject_death a))]
      rfl
    _ = ∫⁻ q, C q ∂((canonicalRecurrenceLaw P a).prod D) := by
      rw [armRecurrenceDeath_joint_eq_prod P a hRD, hmarg]
    _ = ∫⁻ d, recurrenceIntensity P a (Iic (min 1 d)) ∂D := by
      rw [lintegral_prod_symm _ hC.aemeasurable]
      apply lintegral_congr
      intro d
      exact canonicalRecurrenceLaw_lintegral_countLE P a (min 1 d)
    _ = ∫⁻ d, ∫⁻ t, f (d, t) ∂recurrenceIntensity P a ∂D := by
      apply lintegral_congr
      intro d
      symm
      change (∫⁻ t, (Iic (min 1 d)).indicator (fun _ => (1 : ℝ≥0∞)) t
        ∂recurrenceIntensity P a) = _
      rw [lintegral_indicator measurableSet_Iic]
      simp
    _ = ∫⁻ t, ∫⁻ d, f (d, t) ∂D ∂recurrenceIntensity P a :=
      lintegral_lintegral_swap hf.aemeasurable
    _ = ∫⁻ t, (if t ≤ 1 then D (Ici t) else 0) ∂recurrenceIntensity P a := by
      apply lintegral_congr
      intro t
      by_cases ht : t ≤ 1
      · simp only [f, le_min_iff, ht, true_and, if_pos]
        change (∫⁻ d, (Ici t).indicator (fun _ => (1 : ℝ≥0∞)) d ∂D) = _
        rw [lintegral_indicator measurableSet_Ici]
        simp
      · simp [f, le_min_iff, ht]
    _ = _ := by
      unfold recurrenceIntensity
      rw [lintegral_withDensity_eq_lintegral_mul₀ hlam.ennreal_ofReal]
      · apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        simp only [Pi.mul_apply, if_pos ht.2]
        rfl
      · exact (Measurable.ite (measurableSet_le measurable_id measurable_const)
          (Antitone.measurable (fun x y h => measure_mono (Ici_subset_Ici.mpr h)))
          measurable_const).aemeasurable

/-- The clinical count is integrable by domination by the total Poisson count. -/
-- @node: positiveRetention_clinicalCount_integrable
lemma positiveRetention_clinicalCount_integrable (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (a : Arm) :
    Integrable (fun z : LatentSubject => (clinicalCount z a 1 : ℝ)) P.latent := by
  obtain ⟨_, _, hν, hdist⟩ := hPoisson a
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

/-- The benchmark clinical arm mean equals the survival-intensity arm mean,
with no endpoint tail or smoothness premise. -/
-- @node: positiveRetention_integral_clinicalCount_eq_armMean
lemma positiveRetention_integral_clinicalCount_eq_armMean (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) (a : Arm) :
    (∫ z, (clinicalCount z a 1 : ℝ) ∂P.latent) = armMean P a := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let D := P.latent.map (fun z => z.death a)
  letI : IsProbabilityMeasure D :=
    Measure.isProbabilityMeasure_map (measurable_latentSubject_death a).aemeasurable
  let F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (P.lam a t) * D (Ici t)
  have hF : AEMeasurable F (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hPoisson a).1.ennreal_ofReal.mul
      (Antitone.measurable (fun x y h => measure_mono (Ici_subset_Ici.mpr h))).aemeasurable
  have hFtop : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), F t < ∞ :=
    Eventually.of_forall (fun t => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (measure_lt_top D (Ici t)))
  have hcountMeas : Measurable (fun z : LatentSubject =>
      (clinicalCount z a 1 : ℝ≥0∞)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      (RecurConfig.measurable_countLE.comp
        ((measurable_const.min (measurable_latentSubject_death a)).prodMk
          (measurable_latentSubject_recur a)))
  calc
    _ = (∫⁻ z, (clinicalCount z a 1 : ℝ≥0∞) ∂P.latent).toReal := by
      simpa using integral_toReal hcountMeas.aemeasurable
        (Eventually.of_forall (fun _ => ENNReal.coe_lt_top))
    _ = (∫⁻ t in Ioc (0 : ℝ) 1, F t).toReal :=
      congrArg ENNReal.toReal (positiveRetention_lintegral_clinicalCount P hPoisson hRD a)
    _ = ∫ t in Ioc (0 : ℝ) 1, (F t).toReal := (integral_toReal hF hFtop).symm
    _ = armMean P a := by
      unfold armMean
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc, (hPoisson a).2.1] with t ht hnonneg
      have hd : (D (Ici t)).toReal = survival P a t := by
        rw [Measure.map_apply (measurable_latentSubject_death a) measurableSet_Ici]
        exact hDeath.2.2.2.1 a t ⟨ht.1.le, ht.2⟩
      simp only [F, ENNReal.toReal_mul, ENNReal.toReal_ofReal hnonneg, hd, mul_comm]

/-- Independent Poisson recurrence and death identify the clinical causal
contrast at the benchmark's stated level of generality. -/
-- @node: positiveRetention_causalTarget_eq_armMean_contrast
lemma positiveRetention_causalTarget_eq_armMean_contrast (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hRD : RecurrenceDeathIndependence P) :
    causalTarget P = armMean P true - armMean P false := by
  rw [causalTarget, integral_sub
    (positiveRetention_clinicalCount_integrable P hPoisson true)
    (positiveRetention_clinicalCount_integrable P hPoisson false),
    positiveRetention_integral_clinicalCount_eq_armMean P hPoisson hDeath hRD true,
    positiveRetention_integral_clinicalCount_eq_armMean P hPoisson hDeath hRD false]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
