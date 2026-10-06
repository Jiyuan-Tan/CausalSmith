module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryObservedLaw
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ReferenceDeathStoppedLaw

/-!
# Product-law bridge for the reference death process

This module factors assigned-arm follow-up from death and transports the
finite-horizon death coordinate to the global reference law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Adding an independent first block preserves independence between a
measurable coordinate of the second block and another second-block coordinate. -/
lemma indepFun_prod_fst_prod_snd_of_indep
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : B → C} {d : B → D}
    (hc : Measurable c) (hd : Measurable d) (hcd : IndepFun c d ν) :
    IndepFun (fun q : A × B => (q.1, c q.2))
      (fun q : A × B => d q.2) (μ.prod ν) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2
  have hcdMap := hcd.map_prod_eq_prod_map_map hc.aemeasurable hd.aemeasurable
  have hassoc : Measure.map (MeasurableEquiv.prodAssoc.symm :
      A × (C × D) → (A × C) × D) (μ.prod ((ν.map c).prod (ν.map d))) =
      (μ.prod (ν.map c)).prod (ν.map d) := by
    have h := Measure.prodAssoc_prod (μ := μ) (ν := ν.map c) (τ := ν.map d)
    calc
      _ = Measure.map (MeasurableEquiv.prodAssoc.symm :
          A × (C × D) → (A × C) × D)
          (Measure.map (MeasurableEquiv.prodAssoc :
            (A × C) × D → A × (C × D))
            ((μ.prod (ν.map c)).prod (ν.map d))) := by rw [h]
      _ = _ := by
        rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
          MeasurableEquiv.prodAssoc.measurable]
        convert Measure.map_id
        funext q
        exact MeasurableEquiv.prodAssoc.symm_apply_apply q
  have hpairMap :
      Measure.map (fun q : A × B => (q.1, (c q.2, d q.2))) (μ.prod ν) =
        μ.prod (ν.map (fun b => (c b, d b))) := by
    calc
      _ = Measure.map (Prod.map id (fun b => (c b, d b))) (μ.prod ν) := by
        congr 1
      _ = _ := by
        simpa only [Measure.map_id] using
          (Measure.map_prod_map μ ν measurable_id (hc.prodMk hd)).symm
  have hcMap : Measure.map (fun q : A × B => (q.1, c q.2)) (μ.prod ν) =
      μ.prod (ν.map c) := by
    calc
      _ = Measure.map (Prod.map id c) (μ.prod ν) := by congr 1
      _ = _ := by
        simpa only [Measure.map_id] using
          (Measure.map_prod_map μ ν measurable_id hc).symm
  have hdMap : Measure.map (fun q : A × B => d q.2) (μ.prod ν) = ν.map d := by
    rw [← Function.comp_def, ← Measure.map_map hd measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul]
  calc
    Measure.map (fun q : A × B => ((q.1, c q.2), d q.2)) (μ.prod ν) =
        Measure.map (MeasurableEquiv.prodAssoc.symm :
          A × (C × D) → (A × C) × D)
          (Measure.map (fun q : A × B => (q.1, (c q.2, d q.2))) (μ.prod ν)) := by
      rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (by fun_prop)]
      rfl
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm :
          A × (C × D) → (A × C) × D)
          (μ.prod (ν.map (fun b => (c b, d b)))) := by
      rw [hpairMap]
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm :
          A × (C × D) → (A × C) × D)
          (μ.prod ((ν.map c).prod (ν.map d))) := by rw [hcdMap]
    _ = (μ.prod (ν.map c)).prod (ν.map d) := hassoc
    _ = (Measure.map (fun q : A × B => (q.1, c q.2)) (μ.prod ν)).prod
          (Measure.map (fun q : A × B => d q.2) (μ.prod ν)) := by
      rw [hcMap, hdMap]

/-- Independence under a pushforward pulls back along the measurable map. -/
lemma indepFun_comp_of_map
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure A} [IsFiniteMeasure μ] {φ : A → B} {c : B → C} {d : B → D}
    (hφ : Measurable φ) (hc : Measurable c) (hd : Measurable d)
    (h : IndepFun c d (μ.map φ)) :
    IndepFun (c ∘ φ) (d ∘ φ) μ := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hc.comp hφ).aemeasurable (hd.comp hφ).aemeasurable).2
  have hmap := h.map_prod_eq_prod_map_map
    hc.aemeasurable hd.aemeasurable
  calc
    Measure.map (fun x => ((c ∘ φ) x, (d ∘ φ) x)) μ =
        Measure.map (fun y => (c y, d y)) (μ.map φ) := by
      rw [Measure.map_map (hc.prodMk hd) hφ]
      rfl
    _ = (Measure.map c (μ.map φ)).prod (Measure.map d (μ.map φ)) := hmap
    _ = (Measure.map (c ∘ φ) μ).prod (Measure.map (d ∘ φ) μ) := by
      rw [Measure.map_map hc hφ, Measure.map_map hd hφ]

/-- Assigned-arm follow-up as a function of assignment and one censoring coordinate. -/
@[no_expose]
noncomputable def assignedArmFollowup (a : Arm) (q : Arm × ENNReal) : ℝ :=
  if q.1 = a then censorHorizonValue q.2 else 0

@[fun_prop] lemma measurable_assignedArmFollowup (a : Arm) :
    Measurable (assignedArmFollowup a) := by
  unfold assignedArmFollowup
  exact Measurable.ite
    (measurableSet_eq_fun measurable_fst measurable_const)
    (measurable_censorHorizonValue.comp measurable_snd) measurable_const

lemma assignedArmFollowup_treatment_censor (a : Arm) (z : LatentSubject) :
    assignedArmFollowup a (z.treatment, z.censor a) =
      armDeathFailureTime a z := by
  simp only [assignedArmFollowup, armDeathFailureTime, censorHorizon_eq_value]

/-- Under random assignment and independent censoring, assigned-arm follow-up
is independent of the same arm's death time. -/
lemma armDeathFailureTime_indep_death (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hCensor : IndependentCensoring P) (a : Arm) :
    IndepFun (armDeathFailureTime a) (fun z : LatentSubject => z.death a) P.latent := by
  let Aμ := P.latent.map LatentSubject.treatment
  let R := (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))
  let rest : LatentSubject → R := fun z => (z.recur, z.death, z.censor)
  let Rμ := P.latent.map rest
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure Aμ := Measure.isProbabilityMeasure_map
    measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure Rμ := Measure.isProbabilityMeasure_map
    measurable_latentSubject_rest.aemeasurable
  have hCDlatent : IndepFun (fun z : LatentSubject => z.censor a)
      (fun z : LatentSubject => z.death a) P.latent :=
    (hCensor a).comp measurable_id measurable_snd
  have hCDrest : IndepFun (fun r : R => r.2.2 a)
      (fun r : R => r.2.1 a) Rμ := by
    apply IndepFun.of_map measurable_latentSubject_rest
      (by fun_prop) (by fun_prop)
    convert hCDlatent using 1 <;> rfl
  have hblocks := indepFun_prod_fst_prod_snd_of_indep
    (μ := Aμ) (ν := Rμ) (by fun_prop) (by fun_prop) hCDrest
  have hblocks' := hblocks.comp
    (measurable_assignedArmFollowup a) measurable_id
  let blocks : LatentSubject → Arm × R := fun z => (z.treatment, rest z)
  have hmap : P.latent.map blocks = Aμ.prod Rμ := by
    simpa only [blocks, rest, Aμ, Rμ] using treatment_rest_map_eq_prod P hRandom
  rw [← hmap] at hblocks'
  have hpull := indepFun_comp_of_map (μ := P.latent)
    (φ := blocks) (c := fun q : Arm ×
        ((Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) =>
      assignedArmFollowup a (q.1, q.2.2.2 a))
    (d := fun q : Arm ×
        ((Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) => q.2.2.1 a)
    (by fun_prop) (by fun_prop) (by fun_prop) hblocks'
  convert hpull using 1
  · funext z
    exact assignedArmFollowup_treatment_censor a z
  · rfl

/-- The one-subject assigned-follow-up/death pair has the product of its
marginal laws. -/
lemma armDeath_pair_map_eq_prod (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hCensor : IndependentCensoring P) (a : Arm) :
    P.latent.map (fun z : LatentSubject =>
        (armDeathFailureTime a z, z.death a)) =
      (armDeathFailureLaw P a).prod (armDeathEventLaw P a) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  simpa only [armDeathFailureLaw, armDeathEventLaw] using
    (armDeathFailureTime_indep_death P hRandom hCensor a).map_prod_eq_prod_map_map
      (measurable_armDeathFailureTime a).aemeasurable
      (measurable_latentSubject_death a).aemeasurable

/-- Capping death at the study horizon makes the original latent pair law
equal to the corresponding reference-law pair observable. -/
lemma armDeath_stopped_pair_map_eq_reference (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hCensor : IndependentCensoring P) (a : Arm) :
    P.latent.map (fun z : LatentSubject =>
        (armDeathFailureTime a z, min (z.death a) 1)) =
      ((armDeathFailureLaw P a).prod (referenceDeathLaw P a)).map
        (fun q : ℝ × ℝ => (q.1, min q.2 1)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    Measure.isProbabilityMeasure_map
      (measurable_armDeathFailureTime a).aemeasurable
  letI : IsProbabilityMeasure (armDeathEventLaw P a) :=
    Measure.isProbabilityMeasure_map
      (measurable_latentSubject_death a).aemeasurable
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  have hpair := armDeath_pair_map_eq_prod P hRandom hCensor a
  have href := referenceDeathLaw_map_min_one P a
  calc
    _ = (P.latent.map (fun z : LatentSubject =>
        (armDeathFailureTime a z, z.death a))).map
          (fun q : ℝ × ℝ => (q.1, min q.2 1)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ((armDeathFailureLaw P a).prod (armDeathEventLaw P a)).map
          (fun q : ℝ × ℝ => (q.1, min q.2 1)) := by rw [hpair]
    _ = (armDeathFailureLaw P a).prod
          ((armDeathEventLaw P a).map (fun d : ℝ => min d 1)) := by
      calc
        _ = ((armDeathFailureLaw P a).prod (armDeathEventLaw P a)).map
            (Prod.map id (fun d : ℝ => min d 1)) := by congr 1
        _ = _ := by
          simpa only [Measure.map_id, id_eq] using
            (Measure.map_prod_map (armDeathFailureLaw P a) (armDeathEventLaw P a)
              measurable_id (measurable_id.min measurable_const)).symm
    _ = (armDeathFailureLaw P a).prod
          ((referenceDeathLaw P a).map (fun d : ℝ => min d 1)) := by rw [href]
    _ = _ := by
      calc
        _ = ((armDeathFailureLaw P a).prod (referenceDeathLaw P a)).map
            (Prod.map id (fun d : ℝ => min d 1)) := by
          simpa only [Measure.map_id, id_eq] using
            Measure.map_prod_map (armDeathFailureLaw P a) (referenceDeathLaw P a)
              measurable_id (measurable_id.min measurable_const)
        _ = _ := by congr 1

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
