module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceCanonicalEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceExposureProductLaw
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreMeasurability

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Second moment of the observed recurrence error

Average canonical conditional Poisson energy over the independent exposure
array and transport it to the observed iid sample. Every inverse risk remains
inside the time integral until the binomial risk-set bound is applied.
-/

public section

open MeasureTheory Set ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A crude bounded envelope establishes global integrability of the conditional
energy. It is used only for Fubini, not for the final finite-sample rate. -/
-- @node: recurrence_integrated_energy_abs_le
lemma recurrence_integrated_energy_abs_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
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
      have hl0 := c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht01).1
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _)
        (recurrenceSubjectWeight_abs_le c hh a s i t) 2)
        (hP.recurrenceBounds a t ht01).2 hl0 (sq_nonneg _)
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

/-- Averaging the concrete conditional energy gives an integrable full score and
an exact second moment on the canonical exposure/recurrence product law. -/
-- @node: recurrenceConcreteExposureScore_product_second_moment
lemma recurrenceConcreteExposureScore_product_second_moment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (Q : Measure (Fin n → Arm × (ℝ × ENNReal))) [IsFiniteMeasure Q]
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
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
    exact (measurable_recurrenceWeightIntegral c P hP.poissonRecurrence a i hh.le hh1 2).comp
      (show Measurable (fun e : Fin n → Arm × (ℝ × ENNReal) =>
        fun j => recurrenceExposureHistory (e j)) by fun_prop)
  have heInt : Integrable energy Q := by
    apply (integrable_const (n * (weightEnvelope c ^ 2 * c.lambdaMax))).mono'
      heMeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro e
    rw [Real.norm_eq_abs]
    exact recurrence_integrated_energy_abs_le c P hP a _ hh hh1
  have hs := (measurable_recurrenceConcreteExposureScore c P hP.poissonRecurrence
    a n hh.le hh1).pow_const 2
  have hc (e) := recurrenceConcreteExposureScore_conditional_second_moment
    c P hP a n e hh hh1
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

/-- The observed iid sample law is the pushforward of the iid latent sample. -/
-- @node: recurrence_sampleLaw_eq_latent_map
lemma recurrence_sampleLaw_eq_latent_map (P : SubjectLaw) (n : ℕ) :
    sampleLaw P n = (Measure.pi (fun _ : Fin n => P.latent)).map
      (fun z => fun i => observe (z i)) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  symm
  exact Measure.pi_map_pi (fun _ => measurable_observe.aemeasurable)

/-- The actual recurrence error has the exposure-averaged canonical energy as
its second moment, with global square-integrability proved rather than assumed. -/
-- @node: recurrenceError_secondMoment_eq_exposure_energy
lemma recurrenceError_secondMoment_eq_exposure_energy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    Integrable (fun s : Fin n → ObsHistory => recurrenceError c P a s h ^ 2)
      (sampleLaw P n) ∧
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s h ^ 2 ∂sampleLaw P n) =
      ∫ e, (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a (fun j => recurrenceExposureHistory (e j)) i t ^ 2 *
          P.lam a t)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  obtain ⟨hν, hpair⟩ := iid_exposure_recurrence_map_eq_canonical_prod P
    hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n
  let : IsFiniteMeasure (recurrenceIntensity P a) := hν
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let E := P.latent.map (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))
  let : IsProbabilityMeasure E := Measure.isProbabilityMeasure_map (by fun_prop)
  let μ := Measure.pi (fun _ : Fin n => P.latent)
  let pair := fun z : Fin n → LatentSubject =>
    ((fun i => ((z i).treatment, ((z i).death a, (z i).censor a))),
      (fun i => (z i).recur a))
  have hp : Measurable pair := by fun_prop
  have hs := (measurable_recurrenceConcreteExposureScore c P hP.poissonRecurrence
    a n hh.le hh1).pow_const 2
  have hm := recurrenceConcreteExposureScore_product_second_moment
    c P hP a n (Measure.pi (fun _ : Fin n => E)) hh hh1
  rw [← hpair] at hm
  have hobs : Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) := by
    fun_prop
  have herr := (measurable_recurrenceError c P hP a n hh hh1).pow_const 2
  have heq : (fun z : Fin n → LatentSubject =>
      recurrenceError c P a (fun i => observe (z i)) h ^ 2) =
      fun z => recurrenceConcreteExposureScore c P a n h (pair z).1 (pair z).2 ^ 2 := by
    funext z
    rw [recurrenceError_eq_concreteExposureScore c P hP a z hh hh1]
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

/-- The exposure-averaged energy equals the subject-score energy on the observed
sample, since every weight is unchanged by replacing histories by exposures. -/
-- @node: recurrenceError_secondMoment_eq_subject_energy
lemma recurrenceError_secondMoment_eq_subject_energy
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫ s : Fin n → ObsHistory, recurrenceError c P a s h ^ 2 ∂sampleLaw P n) =
      ∫ s : Fin n → ObsHistory, (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t) ∂sampleLaw P n := by
  let energy := fun s : Fin n → ObsHistory => ∑ i : Fin n,
    ∫ t in (0 : ℝ)..(1 - h), recurrenceSubjectWeight c h a s i t ^ 2 * P.lam a t
  have he : Measurable energy := Finset.measurable_sum _ (fun i _ =>
    measurable_recurrenceWeightIntegral c P hP.poissonRecurrence a i hh.le hh1 2)
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
  rw [(recurrenceError_secondMoment_eq_exposure_energy c P hP a n hh hh1).2]
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

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
