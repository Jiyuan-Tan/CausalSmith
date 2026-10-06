module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceExposureProductLaw

/-!
# Selected-arm recurrence law

For one randomized subject, retain only the assigned arm's death, censoring,
and recurrence coordinates.  Their law is the two-cell mixture of the proved
same-arm exposure/Poisson product laws.  This avoids any cross-arm recurrence
independence assumption.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Treatment together with the assigned arm's death and censoring times. -/
-- @node: selectedArmExposure
def selectedArmExposure (z : LatentSubject) : Arm × (ℝ × ENNReal) :=
  (z.treatment, (z.death z.treatment, z.censor z.treatment))

/-- The latent recurrence configuration in the subject's assigned arm. -/
-- @node: selectedArmRecurrence
def selectedArmRecurrence (z : LatentSubject) : RecurConfig :=
  z.recur z.treatment

@[fun_prop] lemma measurable_selectedArmExposure : Measurable selectedArmExposure := by
  unfold selectedArmExposure
  exact measurable_latentSubject_treatment.prodMk
    ((measurable_arm_eval _ _ measurable_latentSubject_deathFamily
      measurable_latentSubject_treatment).prodMk
    (measurable_arm_eval _ _ measurable_latentSubject_censorFamily
      measurable_latentSubject_treatment))

@[fun_prop] lemma measurable_selectedArmRecurrence : Measurable selectedArmRecurrence := by
  unfold selectedArmRecurrence
  exact measurable_arm_eval _ _ measurable_latentSubject_recurFamily
    measurable_latentSubject_treatment

/-- On a fixed treatment cell, selecting the assigned coordinates agrees
almost everywhere with reading that fixed arm. -/
lemma selectedArm_pair_map_restrict_eq_fixed (P : SubjectLaw) (a : Arm) :
    (P.latent.restrict {z | z.treatment = a}).map
        (fun z => (selectedArmExposure z, selectedArmRecurrence z)) =
      (P.latent.restrict {z | z.treatment = a}).map
        (fun z => ((z.treatment, (z.death a, z.censor a)), z.recur a)) := by
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem
    (measurable_latentSubject_treatment (measurableSet_singleton a))] with z hz
  simp [selectedArmExposure, selectedArmRecurrence, hz]

/-- Restricting the fixed-arm joint law to its treatment cell restricts only
the exposure factor. -/
lemma fixedArm_pair_map_restrict_eq_product (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hRD : RecurrenceDeathIndependence P)
    (hC : IndependentCensoring P) (hPoisson : PoissonRecurrence P) (a : Arm) :
    ∃ hν : IsFiniteMeasure (recurrenceIntensity P a),
      (P.latent.restrict {z | z.treatment = a}).map
          (fun z => ((z.treatment, (z.death a, z.censor a)), z.recur a)) =
        ((P.latent.map (fun z : LatentSubject =>
          (z.treatment, (z.death a, z.censor a)))).restrict {e | e.1 = a}).prod
          (@canonicalRecurrenceLaw P a hν) := by
  obtain ⟨hν, hpair⟩ := arm_exposure_recurrence_map_eq_canonical_prod
    P hRandom hRD hC hPoisson a
  refine ⟨hν, ?_⟩
  let E := P.latent.map (fun z : LatentSubject =>
    (z.treatment, (z.death a, z.censor a)))
  let R := @canonicalRecurrenceLaw P a hν
  let pair : LatentSubject → (Arm × (ℝ × ENNReal)) × RecurConfig :=
    fun z => ((z.treatment, (z.death a, z.censor a)), z.recur a)
  let cell : Set (Arm × (ℝ × ENNReal)) := {e | e.1 = a}
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure E := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure R := by
    unfold R canonicalRecurrenceLaw canonicalRecurrenceLawOf
    infer_instance
  have hp : Measurable pair := by fun_prop
  have hc : MeasurableSet cell := by
    unfold cell
    exact measurable_fst (measurableSet_singleton a)
  have hpre : pair ⁻¹' (cell ×ˢ (univ : Set RecurConfig)) =
      {z : LatentSubject | z.treatment = a} := by
    ext z
    simp [pair, cell]
  change Measure.map pair (P.latent.restrict {z | z.treatment = a}) = _
  calc
    _ = (P.latent.map pair).restrict (cell ×ˢ (univ : Set RecurConfig)) := by
      rw [Measure.restrict_map hp (hc.prod MeasurableSet.univ), hpre]
    _ = (E.prod R).restrict (cell ×ˢ (univ : Set RecurConfig)) := by
      rw [show P.latent.map pair = E.prod R from hpair]
    _ = (E.restrict cell).prod R := by
      rw [← Measure.prod_restrict cell (univ : Set RecurConfig)]
      simp

/-- The selected exposure/recurrence pushforward is a treatment-cell mixture
of same-arm exposure measures and their canonical Poisson recurrence laws. -/
-- @node: selectedArm_exposure_recurrence_map_eq_mixture
lemma selectedArm_exposure_recurrence_map_eq_mixture (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hRD : RecurrenceDeathIndependence P)
    (hC : IndependentCensoring P) (hPoisson : PoissonRecurrence P) :
    ∃ hν : ∀ a : Arm, IsFiniteMeasure (recurrenceIntensity P a),
      P.latent.map (fun z => (selectedArmExposure z, selectedArmRecurrence z)) =
        ((P.latent.map (fun z : LatentSubject =>
          (z.treatment, (z.death false, z.censor false)))).restrict
            {e | e.1 = false}).prod (@canonicalRecurrenceLaw P false (hν false)) +
        ((P.latent.map (fun z : LatentSubject =>
          (z.treatment, (z.death true, z.censor true)))).restrict
            {e | e.1 = true}).prod (@canonicalRecurrenceLaw P true (hν true)) := by
  choose hν hfixed using fun a => fixedArm_pair_map_restrict_eq_product
    P hRandom hRD hC hPoisson a
  refine ⟨hν, ?_⟩
  let S : Set LatentSubject := {z | z.treatment = false}
  have hS : MeasurableSet S := by
    unfold S
    exact measurable_latentSubject_treatment (measurableSet_singleton false)
  have hSc : Sᶜ = {z : LatentSubject | z.treatment = true} := by
    ext z
    cases z.treatment <;> simp [S]
  have hsplit : P.latent.restrict S +
      P.latent.restrict {z : LatentSubject | z.treatment = true} = P.latent := by
    rw [← hSc, Measure.restrict_add_restrict_compl hS]
  have hsel : Measurable (fun z : LatentSubject =>
      (selectedArmExposure z, selectedArmRecurrence z)) := by fun_prop
  calc
    _ = Measure.map (fun z : LatentSubject =>
        (selectedArmExposure z, selectedArmRecurrence z))
        (P.latent.restrict S +
          P.latent.restrict {z : LatentSubject | z.treatment = true}) := by rw [hsplit]
    _ = Measure.map (fun z : LatentSubject =>
          (selectedArmExposure z, selectedArmRecurrence z)) (P.latent.restrict S) +
        Measure.map (fun z : LatentSubject =>
          (selectedArmExposure z, selectedArmRecurrence z))
            (P.latent.restrict {z : LatentSubject | z.treatment = true}) := by
      exact (P.latent.restrict S).map_add
        (P.latent.restrict {z : LatentSubject | z.treatment = true}) hsel
    _ = _ := by
      rw [selectedArm_pair_map_restrict_eq_fixed P false,
        selectedArm_pair_map_restrict_eq_fixed P true,
        hfixed false, hfixed true]

/-- In an iid latent sample, the selected exposure/recurrence pairs are iid
with the one-subject treatment-cell mixture law. -/
-- @node: iid_selectedArm_exposure_recurrence_map_eq_pi_mixture
lemma iid_selectedArm_exposure_recurrence_map_eq_pi_mixture (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hRD : RecurrenceDeathIndependence P)
    (hC : IndependentCensoring P) (hPoisson : PoissonRecurrence P) (n : ℕ) :
    ∃ hν : ∀ a : Arm, IsFiniteMeasure (recurrenceIntensity P a),
      (Measure.pi (fun _ : Fin n => P.latent)).map
          (fun z i => (selectedArmExposure (z i), selectedArmRecurrence (z i))) =
        Measure.pi (fun _ : Fin n =>
          ((P.latent.map (fun z : LatentSubject =>
            (z.treatment, (z.death false, z.censor false)))).restrict
              {e | e.1 = false}).prod (@canonicalRecurrenceLaw P false (hν false)) +
          ((P.latent.map (fun z : LatentSubject =>
            (z.treatment, (z.death true, z.censor true)))).restrict
              {e | e.1 = true}).prod (@canonicalRecurrenceLaw P true (hν true))) := by
  obtain ⟨hν, hone⟩ := selectedArm_exposure_recurrence_map_eq_mixture
    P hRandom hRD hC hPoisson
  refine ⟨hν, ?_⟩
  let selectedPair : LatentSubject → (Arm × (ℝ × ENNReal)) × RecurConfig :=
    fun z => (selectedArmExposure z, selectedArmRecurrence z)
  have hm : Measurable selectedPair := by
    unfold selectedPair
    fun_prop
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (P.latent.map selectedPair) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  rw [Measure.pi_map_pi (fun _ => hm.aemeasurable)]
  exact congrArg (fun Q => Measure.pi (fun _ : Fin n => Q)) hone

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
