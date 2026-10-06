module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrencePoissonCharFun
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceSecondMoment

/-!
# Canonical and observed recurrence characteristic functions

Normalize the finite intensity and cancel the auxiliary mark in the Poisson
exponential formula. For each arm, average the fixed-exposure formula and
transport it through the proved exposure product law to the observed sample.
These identities supply the armwise part of roadmap (19).
-/

public section

open MeasureTheory Set ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Normalization and the deterministic auxiliary mark cancel for complex
integrands as well as for the real moment integrands. -/
-- @node: recurrence_normalized_marked_integral_complex
lemma recurrence_normalized_marked_integral_complex (ν : Measure ℝ) [IsFiniteMeasure ν]
    (f : ℝ → ℂ) :
    (finiteMeasureMass ν : ℂ) *
      (∫ x : ℝ × ℝ, f x.1
        ∂(normalizedFiniteMeasure ν (Measure.dirac 0)).prod (Measure.dirac 0)) =
      ∫ t, f t ∂ν := by
  rw [integral_fun_fst]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  calc
    _ = ∫ t, f t ∂(finiteMeasureMass ν • normalizedFiniteMeasure ν (Measure.dirac 0)) := by
      rw [integral_smul_nnreal_measure]
      change (finiteMeasureMass ν : ℂ) * (∫ t, f t ∂normalizedFiniteMeasure ν (Measure.dirac 0)) =
        (finiteMeasureMass ν : ℝ) • (∫ t, f t ∂normalizedFiniteMeasure ν (Measure.dirac 0))
      rw [Complex.real_smul]
    _ = _ := congrArg (fun μ => ∫ t, f t ∂μ) (recurrence_mass_smul_normalized ν)

/-- Bounded measurable subject scores under the canonical iid recurrence law
have the compensated Poisson characteristic exponent against the original
unnormalized intensity. -/
-- @node: recurrence_canonical_iid_charFun
lemma recurrence_canonical_iid_charFun (ν : Measure ℝ) [IsFiniteMeasure ν]
    (n : ℕ) (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    {K : ℝ} (hK : ∀ i t, |f i t| ≤ K) (u : ℝ) :
    (∫ r : Fin n → RecurConfig, Complex.exp (Complex.I *
      (u * ∑ i : Fin n, ((∑ k : Fin (r i).1, f i (((r i).2 k).1)) -
        ∫ t, f i t ∂ν) : ℝ))
      ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν)) =
      Complex.exp (∑ i : Fin n, ∫ t,
        (Complex.exp (Complex.I * (u * f i t : ℝ)) - 1 -
          Complex.I * (u * f i t : ℝ)) ∂ν) := by
  have hfi (i : Fin n) : Integrable (fun x : ℝ × ℝ => f i x.1)
      ((normalizedFiniteMeasure ν (Measure.dirac 0)).prod (Measure.dirac 0)) := by
    apply Integrable.of_bound ((hf i).comp measurable_fst).aestronglyMeasurable K
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hK i x.1)
  have hchar := recurrence_poisson_iid_compensated_charFun
    ((normalizedFiniteMeasure ν (Measure.dirac 0)).prod (Measure.dirac 0))
    (finiteMeasureMass ν) n (fun i x => f i x.1)
    (fun i => (hf i).comp measurable_fst) hfi u
  unfold recurrenceExposureScore at hchar
  simp_rw [recurrence_normalized_marked_integral ν] at hchar
  have he (i : Fin n) := recurrence_normalized_marked_integral_complex ν
    (fun t => Complex.exp (Complex.I * (u * f i t : ℝ)) - 1 -
      Complex.I * (u * f i t : ℝ))
  simp_rw [he] at hchar
  simpa only [canonicalRecurrenceLawOf, finiteMeasureMarkedPoissonLaw, one_mul,
    finiteMarkedPoissonSampleLaw] using hchar

/-- Truncating a complex integrand under the recurrence intensity gives its
intensity-weighted Lebesgue integral on the actual estimation horizon. -/
-- @node: recurrenceIntensity_integral_truncated_complex
lemma recurrenceIntensity_integral_truncated_complex (P : SubjectLaw)
    (hP : PoissonRecurrence P) (a : Arm) (f : ℝ → ℂ) {T : ℝ}
    (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ t, (if t ≤ T then f t else 0) ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..T, f t * (P.lam a t : ℂ) := by
  unfold recurrenceIntensity
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hP a).1.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (∫ t in Ioc (0 : ℝ) 1,
      (ENNReal.ofReal (P.lam a t)).toReal • (if t ≤ T then f t else 0)) =
      ∫ t in Ioc (0 : ℝ) 1,
        (Iic T).indicator (fun t => f t * (P.lam a t : ℂ)) t := by
    apply integral_congr_ae
    filter_upwards [(hP a).2.1] with t ht
    simp only [ENNReal.toReal_ofReal ht, Complex.real_smul,
      indicator_apply, mem_Iic]
    split_ifs <;> ring
  rw [heq, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic T ∩ Ioc (0 : ℝ) 1 = Ioc 0 T := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨htT, ht0, _⟩
      exact ⟨ht0, htT⟩
    · rintro ⟨ht0, htT⟩
      exact ⟨htT, ht0, htT.trans hT1⟩
  rw [hset, intervalIntegral.integral_of_le hT]

/-- The concrete same-arm score, conditional on the exposure array, has
exactly the horizon-truncated compensated Poisson characteristic exponent. -/
-- @node: recurrenceConcreteExposureScore_conditional_charFun
lemma recurrenceConcreteExposureScore_conditional_charFun
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (e : Fin n → Arm × (ℝ × ENNReal)) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : ℝ) :
    (∫ r, Complex.exp (Complex.I *
      (u * recurrenceConcreteExposureScore c P a n h e r : ℝ))
      ∂Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a)) =
      Complex.exp (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        (Complex.exp (Complex.I * (u * recurrenceSubjectWeight c h a
          (fun j => recurrenceExposureHistory (e j)) i t : ℝ)) - 1 -
          Complex.I * (u * recurrenceSubjectWeight c h a
            (fun j => recurrenceExposureHistory (e j)) i t : ℝ)) * (P.lam a t : ℂ)) := by
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
    · exact recurrenceSubjectWeight_abs_le c hh a _ i t
    · simp only [abs_zero]
      unfold weightEnvelope continuationNorm
      positivity
  have hc := recurrence_canonical_iid_charFun (recurrenceIntensity P a) n f hf hK u
  have hmean (i : Fin n) : (∫ t, f i t ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..(1 - h), w i t * P.lam a t :=
    recurrenceIntensity_integral_truncated P hP.poissonRecurrence a (w i)
      (by linarith) (by linarith)
  have hexp (i : Fin n) : (∫ t,
      (Complex.exp (Complex.I * (u * f i t : ℝ)) - 1 -
        Complex.I * (u * f i t : ℝ)) ∂recurrenceIntensity P a) =
      ∫ t in (0 : ℝ)..(1 - h),
        (Complex.exp (Complex.I * (u * w i t : ℝ)) - 1 -
          Complex.I * (u * w i t : ℝ)) * (P.lam a t : ℂ) := by
    have he : (fun t => Complex.exp (Complex.I * (u * f i t : ℝ)) - 1 -
        Complex.I * (u * f i t : ℝ)) = fun t => if t ≤ 1 - h then
          Complex.exp (Complex.I * (u * w i t : ℝ)) - 1 -
            Complex.I * (u * w i t : ℝ) else 0 := by
      funext t
      dsimp [f]
      split_ifs <;> simp
    rw [he]
    exact recurrenceIntensity_integral_truncated_complex P hP.poissonRecurrence a _
      (by linarith) (by linarith)
  simp_rw [hmean, hexp] at hc
  exact hc

/-- Averaging over any finite exposure law preserves the conditional
characteristic-function identity. Unit modulus justifies Fubini globally. -/
-- @node: recurrenceConcreteExposureScore_product_charFun
lemma recurrenceConcreteExposureScore_product_charFun
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (Q : Measure (Fin n → Arm × (ℝ × ENNReal))) [IsFiniteMeasure Q]
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : ℝ) :
    (∫ p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig),
      Complex.exp (Complex.I *
        (u * recurrenceConcreteExposureScore c P a n h p.1 p.2 : ℝ))
      ∂Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a))) =
      ∫ e, Complex.exp (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        (Complex.exp (Complex.I * (u * recurrenceSubjectWeight c h a
          (fun j => recurrenceExposureHistory (e j)) i t : ℝ)) - 1 -
          Complex.I * (u * recurrenceSubjectWeight c h a
            (fun j => recurrenceExposureHistory (e j)) i t : ℝ)) * (P.lam a t : ℂ)) ∂Q := by
  let : IsProbabilityMeasure (canonicalRecurrenceLaw P a) := by
    unfold canonicalRecurrenceLaw canonicalRecurrenceLawOf
    infer_instance
  have hs := measurable_recurrenceConcreteExposureScore c P hP.poissonRecurrence
    a n hh.le hh1
  have hi : Integrable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig) =>
      Complex.exp (Complex.I *
        (u * recurrenceConcreteExposureScore c P a n h p.1 p.2 : ℝ)))
      (Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLaw P a))) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun p => by
      simp [Complex.norm_exp, Complex.mul_re])
  rw [integral_prod _ hi]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun e =>
    recurrenceConcreteExposureScore_conditional_charFun c P hP a n e hh hh1 u))

/-- The observed same-arm recurrence error has the exposure-averaged Poisson
characteristic function. The proof uses the actual sample pushforward and
recurrence/exposure independence, with no conditional-law premise. -/
-- @node: recurrenceError_charFun_eq_exposure_exponent
lemma recurrenceError_charFun_eq_exposure_exponent
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : ℝ) :
    (∫ s : Fin n → ObsHistory, Complex.exp (Complex.I *
      (u * recurrenceError c P a s h : ℝ)) ∂sampleLaw P n) =
      ∫ e, Complex.exp (∑ i : Fin n, ∫ t in (0 : ℝ)..(1 - h),
        (Complex.exp (Complex.I * (u * recurrenceSubjectWeight c h a
          (fun j => recurrenceExposureHistory (e j)) i t : ℝ)) - 1 -
          Complex.I * (u * recurrenceSubjectWeight c h a
            (fun j => recurrenceExposureHistory (e j)) i t : ℝ)) * (P.lam a t : ℂ))
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
  obtain ⟨hν, hpair⟩ := iid_exposure_recurrence_map_eq_canonical_prod P
    hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n
  let : IsFiniteMeasure (recurrenceIntensity P a) := hν
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let E := P.latent.map (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))
  let : IsProbabilityMeasure E := Measure.isProbabilityMeasure_map (by fun_prop)
  let pair := fun z : Fin n → LatentSubject =>
    ((fun i => ((z i).treatment, ((z i).death a, (z i).censor a))),
      (fun i => (z i).recur a))
  have hp : Measurable pair := by fun_prop
  have hs := measurable_recurrenceConcreteExposureScore c P hP.poissonRecurrence
    a n hh.le hh1
  have hexp : Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) × (Fin n → RecurConfig) =>
      Complex.exp (Complex.I *
        (u * recurrenceConcreteExposureScore c P a n h p.1 p.2 : ℝ))) := by fun_prop
  have hm := recurrenceConcreteExposureScore_product_charFun
    c P hP a n (Measure.pi (fun _ : Fin n => E)) hh hh1 u
  rw [← hpair] at hm
  have hobs : Measurable (fun z : Fin n → LatentSubject => fun i => observe (z i)) := by
    fun_prop
  have herr := measurable_recurrenceError c P hP a n hh hh1
  have he : Measurable (fun s : Fin n → ObsHistory => Complex.exp (Complex.I *
      (u * recurrenceError c P a s h : ℝ))) := by fun_prop
  rw [recurrence_sampleLaw_eq_latent_map,
    integral_map hobs.aemeasurable he.aestronglyMeasurable]
  simp_rw [recurrenceError_eq_concreteExposureScore c P hP a _ hh hh1]
  rw [← integral_map hp.aemeasurable hexp.aestronglyMeasurable]
  exact hm

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
