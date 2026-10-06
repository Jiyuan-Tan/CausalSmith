module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.UnboundedRecurrenceEnergy
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceExposureProductLaw

/-!
# Transport of unbounded recurrence moments to the latent iid sample

Roadmap (2) and (24): exposure-dependent Poisson scores retain their exact
centering and energy under the actual latent sample law. Conditional square
integrability and averaged energy suffice; no bounded endpoint weight or
independence between empirical coefficients and exposure is asserted.
-/

public section

open MeasureTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The actual iid latent law inherits the exact conditional Poisson energy,
including unbounded scores with finite averaged energy. -/
-- @node: recurrence_latent_exposure_second_moment_of_integrable_sq
lemma recurrence_latent_exposure_second_moment_of_integrable_sq
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
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))))) :
    Integrable (fun z : Fin n → LatentSubject => (
      ∑ i : Fin n, ((∑ k : Fin ((z i).recur a).1,
        f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i
          ((((z i).recur a).2 k).1)) -
        ∫ t, f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
          ∂recurrenceIntensity P a)) ^ 2)
      (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject, (
      ∑ i : Fin n, ((∑ k : Fin ((z i).recur a).1,
        f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i
          ((((z i).recur a).2 k).1)) -
        ∫ t, f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
          ∂recurrenceIntensity P a)) ^ 2 ∂Measure.pi (fun _ : Fin n => P.latent)) =
      ∫ e, (∑ i : Fin n, ∫ t, f e i t ^ 2 ∂recurrenceIntensity P a)
        ∂Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))) := by
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
  have hm := recurrence_canonical_random_exposure_second_moment_of_integrable_sq
    (E := Fin n → Arm × (ℝ × ENNReal))
    (Measure.pi (fun _ : Fin n => E)) (recurrenceIntensity P a) n f hf hi hs he
  change _ = (Measure.pi (fun _ : Fin n => E)).prod
    (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf (recurrenceIntensity P a)))
    at hpair
  rw [← hpair] at hm
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure (hs.pow_const 2).aestronglyMeasurable
      hp.aemeasurable).1 hm.1
  · rw [← integral_map hp.aemeasurable (hs.pow_const 2).aestronglyMeasurable]
    exact hm.2

/-- Conditional Poisson centering transports to the actual iid latent sample
once finite averaged energy supplies integrability. -/
-- @node: recurrence_latent_exposure_mean_zero_of_integrable_sq
lemma recurrence_latent_exposure_mean_zero_of_integrable_sq
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
        (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))))) :
    Integrable (fun z : Fin n → LatentSubject =>
      ∑ i : Fin n, ((∑ k : Fin ((z i).recur a).1,
        f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i
          ((((z i).recur a).2 k).1)) -
        ∫ t, f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
          ∂recurrenceIntensity P a))
      (Measure.pi (fun _ : Fin n => P.latent)) ∧
    (∫ z : Fin n → LatentSubject,
      ∑ i : Fin n, ((∑ k : Fin ((z i).recur a).1,
        f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i
          ((((z i).recur a).2 k).1)) -
        ∫ t, f (fun j => ((z j).treatment, ((z j).death a, (z j).censor a))) i t
          ∂recurrenceIntensity P a) ∂Measure.pi (fun _ : Fin n => P.latent)) = 0 := by
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
  have hm := recurrence_canonical_random_exposure_mean_zero_of_integrable_sq
    (E := Fin n → Arm × (ℝ × ENNReal))
    (Measure.pi (fun _ : Fin n => E)) (recurrenceIntensity P a) n f hf hi hs he
  change _ = (Measure.pi (fun _ : Fin n => E)).prod
    (Measure.pi (fun _ : Fin n => canonicalRecurrenceLawOf (recurrenceIntensity P a)))
    at hpair
  rw [← hpair] at hm
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure hs.aestronglyMeasurable hp.aemeasurable).1 hm.1
  · rw [← integral_map hp.aemeasurable hs.aestronglyMeasurable]
    exact hm.2

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
