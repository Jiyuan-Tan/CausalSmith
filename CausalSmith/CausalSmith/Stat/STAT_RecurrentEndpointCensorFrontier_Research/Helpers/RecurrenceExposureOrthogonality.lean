module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedRecurrenceFullMoments

/-!
# Recurrence orthogonality conditional on exposure

Roadmap (24): conditional Poisson centering annihilates an exposure-measurable
multiplier. Square integrability supplies Fubini for unbounded multipliers;
no independence of a death coefficient and its exposure is asserted.
-/

public section

open MeasureTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Conditional centering annihilates an integrable exposure-weighted score. -/
-- @node: recurrence_canonical_exposure_cross_mean_zero
lemma recurrence_canonical_exposure_cross_mean_zero
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [SFinite Q]
    (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) (f : E → Fin n → ℝ → ℝ)
    (hf : ∀ e i, Measurable (f e i))
    (hi : ∀ᵐ e ∂Q, ∀ i, Integrable (fun t => f e i t ^ 2) ν)
    (g : E → ℝ)
    (hcross : Integrable (fun p : E × (Fin n → RecurConfig) =>
      g p.1 * (∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν)))
      (Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν)))) :
    (∫ p : E × (Fin n → RecurConfig),
      g p.1 * (∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν))
      ∂Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν))) = 0 := by
  letI : IsProbabilityMeasure (canonicalRecurrenceLawOf ν) := by
    unfold canonicalRecurrenceLawOf finiteMeasureMarkedPoissonLaw
    infer_instance
  rw [integral_prod _ hcross]
  calc
    _ = ∫ _ : E, (0 : ℝ) ∂Q := by
      apply integral_congr_ae
      filter_upwards [hi] with e hei
      rw [integral_const_mul]
      have hmean := (recurrence_canonical_iid_mean_zero_of_integrable
        ν n (f e) (hf e) (fun i =>
          ((memLp_two_iff_integrable_sq (hf e i).aestronglyMeasurable).2
            (hei i)).integrable (by norm_num))).2
      rw [hmean, mul_zero]
    _ = 0 := integral_zero _ _

/-- Finite averaged Poisson energy and a square-integrable exposure coefficient
make the cross term integrable and exactly zero, including unbounded weights. -/
-- @node: recurrence_canonical_exposure_orthogonal_of_integrable_sq
lemma recurrence_canonical_exposure_orthogonal_of_integrable_sq
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [SFinite Q]
    (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) (f : E → Fin n → ℝ → ℝ)
    (hf : ∀ e i, Measurable (f e i))
    (hi : ∀ᵐ e ∂Q, ∀ i, Integrable (fun t => f e i t ^ 2) ν)
    (hs : Measurable (fun p : E × (Fin n → RecurConfig) =>
      ∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν)))
    (he : Integrable (fun e => ∑ i : Fin n, ∫ t, f e i t ^ 2 ∂ν) Q)
    (g : E → ℝ) (hg : Measurable g) (hg2 : Integrable (fun e => g e ^ 2) Q) :
    Integrable (fun p : E × (Fin n → RecurConfig) =>
      g p.1 * (∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν)))
      (Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν))) ∧
    (∫ p : E × (Fin n → RecurConfig),
      g p.1 * (∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂ν))
      ∂Q.prod (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν))) = 0 := by
  letI : IsProbabilityMeasure (canonicalRecurrenceLawOf ν) := by
    unfold canonicalRecurrenceLawOf finiteMeasureMarkedPoissonLaw
    infer_instance
  have hscore2 := (recurrence_canonical_random_exposure_second_moment_of_integrable_sq
    Q ν n f hf hi hs he).1
  have hcoef2 := hg2.comp_fst
    (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf ν))
  have hcross := ((memLp_two_iff_integrable_sq
    (hg.comp measurable_fst).aestronglyMeasurable).2 hcoef2).integrable_mul
      ((memLp_two_iff_integrable_sq hs.aestronglyMeasurable).2 hscore2)
  exact ⟨hcross, recurrence_canonical_exposure_cross_mean_zero Q ν n f hf hi g hcross⟩

/-- The actual latent iid law inherits exposure orthogonality by its exact
exposure/Poisson pushforward, without independence of the multiplier and exposure. -/
-- @node: recurrence_latent_exposure_orthogonal_of_integrable_sq
lemma recurrence_latent_exposure_orthogonal_of_integrable_sq
    (P : SubjectLaw) (hRandom : RandomAssignment P)
    (hRD : RecurrenceDeathIndependence P) (hC : IndependentCensoring P)
    (hPoisson : PoissonRecurrence P) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] (n : ℕ)
    (f : (Fin n → Arm × (ℝ × ENNReal)) → Fin n → ℝ → ℝ)
    (hf : ∀ e i, Measurable (f e i))
    (hi : ∀ᵐ e ∂Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))),
      ∀ i, Integrable (fun t => f e i t ^ 2) (recurrenceIntensity P a))
    (hs : Measurable (fun p : (Fin n → Arm × (ℝ × ENNReal)) ×
        (Fin n → RecurConfig) =>
      ∑ i : Fin n, ((∑ k : Fin (p.2 i).1, f p.1 i (((p.2 i).2 k).1)) -
        ∫ t, f p.1 i t ∂recurrenceIntensity P a)))
    (he : Integrable (fun e => ∑ i : Fin n,
        ∫ t, f e i t ^ 2 ∂recurrenceIntensity P a)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))))
    (g : (Fin n → Arm × (ℝ × ENNReal)) → ℝ) (hg : Measurable g)
    (hg2 : Integrable (fun e => g e ^ 2)
      (Measure.pi (fun _ : Fin n => P.latent.map
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))))) :
    Integrable (fun z : Fin n → LatentSubject =>
      g (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) *
      (∑ i : Fin n, ((∑ k : Fin ((z i).recur a).1,
        f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i
          ((((z i).recur a).2 k).1)) -
        ∫ t, f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
          ∂recurrenceIntensity P a)))
      (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject,
      g (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) *
      (∑ i : Fin n, ((∑ k : Fin ((z i).recur a).1,
        f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i
          ((((z i).recur a).2 k).1)) -
        ∫ t, f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
          ∂recurrenceIntensity P a)) ∂Measure.pi (fun _ : Fin n => P.latent)) = 0 := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let E := P.latent.map (fun z : LatentSubject =>
    (z.treatment, (z.death a, z.censor a)))
  let : IsProbabilityMeasure E := Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => E)) := by infer_instance
  let : IsFiniteMeasure (Measure.pi (fun _ : Fin n => E)) := by infer_instance
  let : SigmaFinite (Measure.pi (fun _ : Fin n => E)) :=
    IsFiniteMeasure.toSigmaFinite _
  let : SFinite (Measure.pi (fun _ : Fin n => E)) := by infer_instance
  let pair := fun z : Fin n → LatentSubject =>
    ((fun i => ((z i).treatment, ((z i).death a, (z i).censor a))),
      (fun i => (z i).recur a))
  have hp : Measurable pair := by fun_prop
  obtain ⟨hν, hpair⟩ := iid_exposure_recurrence_map_eq_canonical_prod
    P hRandom hRD hC hPoisson a n
  have hm := recurrence_canonical_exposure_orthogonal_of_integrable_sq
    (E := Fin n → Arm × (ℝ × ENNReal))
    (Measure.pi (fun _ : Fin n => E)) (recurrenceIntensity P a) n f hf hi hs he g hg hg2
  change _ = (Measure.pi (fun _ : Fin n => E)).prod
    (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf (recurrenceIntensity P a)))
    at hpair
  have hcross := (hg.comp measurable_fst).mul hs
  rw [← hpair] at hm
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure hcross.aestronglyMeasurable hp.aemeasurable).1 hm.1
  · exact (integral_map (μ := Measure.pi (fun _ : Fin n => P.latent))
      hp.aemeasurable hcross.aestronglyMeasurable).symm.trans hm.2

/-- The full endpoint inverse-retention recurrence oracle is orthogonal to any
square-integrable exposure coefficient under subcritical overlap. The recurrence
energy hypotheses are derived from the model, not imposed on the oracle. -/
-- @node: observedRecurrenceScore_invRetention_exposure_orthogonal
lemma observedRecurrenceScore_invRetention_exposure_orthogonal
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
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
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  let w : ℝ → ℝ := fun t => (retention P a t)⁻¹
  have hw : Measurable w := (measurable_retention P a).inv
  let f := fun (e : Fin n → Arm × (ℝ × ENNReal)) (i : Fin n) (t : ℝ) =>
    observedRecurrenceTimeWeight a 1 w (recurrenceExposureHistory (e i)) t
  have hf (e) (i : Fin n) : Measurable (f e i) :=
    (measurable_observedRecurrenceTimeWeight a 1 w hw).comp
      (measurable_const.prodMk measurable_id)
  obtain ⟨hi, he⟩ := observedRecurrenceScore_energy_conditions_of_integrable_prod
    P a n 1 w hw
    (observedRecurrence_invRetention_exposure_energy_integrable_prod c P hP hk a hn)
  have hm := recurrence_latent_exposure_orthogonal_of_integrable_sq
    P hP.randomAssignment hP.recurrenceDeathIndependence hP.independentCensoring
    hP.poissonRecurrence a n f hf hi
    (measurable_observedRecurrenceExposureScore P a n 1 w hw) he g hg hg2
  simpa only [observedRecurrenceScore_eq_latent, f, w] using hm

/-- An observed exposure-only coefficient inherits full-horizon recurrence
orthogonality. Almost-sure factorization accommodates exceptional tied histories. -/
-- @node: observedRecurrenceScore_invRetention_orthogonal_of_exposure
lemma observedRecurrenceScore_invRetention_orthogonal_of_exposure
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
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
  obtain ⟨hν, _⟩ := (hP.poissonRecurrence a).2.2
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hν
  obtain ⟨hi, hz⟩ := observedRecurrenceScore_invRetention_exposure_orthogonal
    c P hP hk a hn g hg hg2
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
