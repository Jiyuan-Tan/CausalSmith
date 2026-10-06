module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ReferenceDeathProductLaw

/-!
# Exposure and recurrence product laws

Treatment, death, and censoring jointly factor from the same arm's recurrence
configuration. This supplies the exposure conditioning law for weighted Poisson
moment calculations without introducing a filtration or a compensation premise.
-/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Same-arm recurrence is independent of the joint death/censor exposure. -/
-- @node: arm_recurrence_indep_death_censor
lemma arm_recurrence_indep_death_censor (P : SubjectLaw)
    (hRD : RecurrenceDeathIndependence P) (hC : IndependentCensoring P) (a : Arm) :
    IndepFun (fun z : LatentSubject => z.recur a)
      (fun z : LatentSubject => (z.death a, z.censor a)) P.latent := by
  let R := P.latent.map (fun z : LatentSubject => z.recur a)
  let D := P.latent.map (fun z : LatentSubject => z.death a)
  let C := P.latent.map (fun z : LatentSubject => z.censor a)
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map
    (measurable_latentSubject_recur a).aemeasurable
  let : IsProbabilityMeasure D := Measure.isProbabilityMeasure_map
    (measurable_latentSubject_death a).aemeasurable
  let : IsProbabilityMeasure C := Measure.isProbabilityMeasure_map
    (measurable_latentSubject_censor a).aemeasurable
  let triple : LatentSubject → RecurConfig × (ℝ × ENNReal) :=
    fun z => (z.recur a, (z.death a, z.censor a))
  have hmap : P.latent.map triple = R.prod (D.prod C) := by
    calc
      _ = Measure.map MeasurableEquiv.prodAssoc
          (P.latent.map (fun z : LatentSubject => ((z.recur a, z.death a), z.censor a))) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = Measure.map MeasurableEquiv.prodAssoc ((R.prod D).prod C) := by
        rw [arm_recur_death_censor_map_eq_prod P hRD hC a]
      _ = _ := Measure.prodAssoc_prod
  have hi := indepFun_prod (μ := R) (ν := D.prod C) measurable_id measurable_id
  rw [← hmap] at hi
  have hp := indepFun_comp_of_map (φ := triple) (by fun_prop)
    measurable_fst measurable_snd hi
  convert hp using 1 <;> rfl

/-- Full exposure, including random treatment assignment, is independent of
same-arm recurrence. -/
-- @node: arm_exposure_indep_recurrence
lemma arm_exposure_indep_recurrence (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hRD : RecurrenceDeathIndependence P)
    (hC : IndependentCensoring P) (a : Arm) :
    IndepFun (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a)))
      (fun z : LatentSubject => z.recur a) P.latent := by
  let Aμ := P.latent.map LatentSubject.treatment
  let rest : LatentSubject → ((Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) := fun z => (z.recur, z.death, z.censor)
  let Rμ := P.latent.map rest
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure Aμ := Measure.isProbabilityMeasure_map
    measurable_latentSubject_treatment.aemeasurable
  let : IsProbabilityMeasure Rμ := Measure.isProbabilityMeasure_map
    measurable_latentSubject_rest.aemeasurable
  have hrest : IndepFun (fun r : ((Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) => (r.2.1 a, r.2.2 a))
      (fun r : ((Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) => r.1 a) Rμ := by
    apply IndepFun.of_map measurable_latentSubject_rest (by fun_prop) (by fun_prop)
    convert (arm_recurrence_indep_death_censor P hRD hC a).symm using 1 <;> rfl
  have hi := indepFun_prod_fst_prod_snd_of_indep
    (μ := Aμ) (ν := Rμ) (by fun_prop) (by fun_prop) hrest
  let blocks : LatentSubject → Arm × ((Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) := fun z => (z.treatment, rest z)
  have hmap : P.latent.map blocks = Aμ.prod Rμ :=
    treatment_rest_map_eq_prod P hRandom
  rw [← hmap] at hi
  have hp := indepFun_comp_of_map (φ := blocks) (by fun_prop)
    (by fun_prop) (by fun_prop) hi
  convert hp using 1 <;> rfl

/-- The exposure/recurrence law has the canonical Poisson recurrence marginal. -/
-- @node: arm_exposure_recurrence_map_eq_canonical_prod
lemma arm_exposure_recurrence_map_eq_canonical_prod (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hRD : RecurrenceDeathIndependence P)
    (hC : IndependentCensoring P) (hPoisson : PoissonRecurrence P) (a : Arm) :
    ∃ hν : IsFiniteMeasure (recurrenceIntensity P a),
      P.latent.map (fun z : LatentSubject =>
          ((z.treatment, (z.death a, z.censor a)), z.recur a)) =
        (P.latent.map (fun z : LatentSubject =>
          (z.treatment, (z.death a, z.censor a)))).prod
            (@canonicalRecurrenceLaw P a hν) := by
  obtain ⟨hν, hνlaw⟩ := (hPoisson a).2.2
  refine ⟨hν, ?_⟩
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  rw [← hνlaw]
  exact (arm_exposure_indep_recurrence P hRandom hRD hC a).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop)

/-- In a finite iid latent sample, the entire exposure array factors from the
array of canonical Poisson recurrence configurations. -/
-- @node: iid_exposure_recurrence_map_eq_canonical_prod
lemma iid_exposure_recurrence_map_eq_canonical_prod (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hRD : RecurrenceDeathIndependence P)
    (hC : IndependentCensoring P) (hPoisson : PoissonRecurrence P)
    (a : Arm) (n : ℕ) :
    ∃ hν : IsFiniteMeasure (recurrenceIntensity P a),
      (Measure.pi (fun _ : Fin n => P.latent)).map
        (fun z => ((fun i => ((z i).treatment, ((z i).death a, (z i).censor a))),
          (fun i => (z i).recur a))) =
        (Measure.pi (fun _ : Fin n => P.latent.map
          (fun z : LatentSubject => (z.treatment, (z.death a, z.censor a))))).prod
        (Measure.pi (fun _ : Fin n => @canonicalRecurrenceLaw P a hν)) := by
  obtain ⟨hν, hpair⟩ := arm_exposure_recurrence_map_eq_canonical_prod
    P hRandom hRD hC hPoisson a
  refine ⟨hν, ?_⟩
  let E := P.latent.map (fun z : LatentSubject =>
    (z.treatment, (z.death a, z.censor a)))
  let R := @canonicalRecurrenceLaw P a hν
  let pair : LatentSubject → (Arm × (ℝ × ENNReal)) × RecurConfig :=
    fun z => ((z.treatment, (z.death a, z.censor a)), z.recur a)
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure E := Measure.isProbabilityMeasure_map (by fun_prop)
  have hRlaw : P.latent.map (fun z : LatentSubject => z.recur a) = R := by
    obtain ⟨hν', hR⟩ := (hPoisson a).2.2
    exact hR
  let : IsProbabilityMeasure R := by
    rw [← hRlaw]
    exact Measure.isProbabilityMeasure_map (measurable_latentSubject_recur a).aemeasurable
  let : IsProbabilityMeasure (P.latent.map pair) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let split := MeasurableEquiv.arrowProdEquivProdArrow
    (Arm × (ℝ × ENNReal)) RecurConfig (Fin n)
  calc
    _ = Measure.map split
        ((Measure.pi (fun _ : Fin n => P.latent)).map
          (fun z i => pair (z i))) := by
      rw [Measure.map_map split.measurable (by unfold pair; fun_prop)]
      rfl
    _ = Measure.map split (Measure.pi (fun _ : Fin n => P.latent.map pair)) := by
      rw [Measure.pi_map_pi (fun _ => (show Measurable pair by unfold pair; fun_prop).aemeasurable)]
    _ = Measure.map split (Measure.pi (fun _ : Fin n => E.prod R)) := by
      rw [show P.latent.map pair = E.prod R from hpair]
    _ = _ := (measurePreserving_arrowProdEquivProdArrow
      (Arm × (ℝ × ENNReal)) RecurConfig (Fin n) (fun _ => E) (fun _ => R)).map_eq

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
