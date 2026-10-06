module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryObservedLaw

@[expose] public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Convert the raw same-arm recurrence/death/censor triple to capped death
data while retaining the complete recurrence configuration. -/
@[no_expose]
noncomputable def capArmTriple
    (q : (RecurConfig × ℝ) × ENNReal) :
      (RecurConfig × (ℝ × Bool)) × ENNReal :=
  ((q.1.1, cappedDeathRecord q.1.2), q.2)

@[fun_prop]
lemma measurable_capArmTriple : Measurable capArmTriple := by
  unfold capArmTriple
  fun_prop

/-- Recurrence is independent of the capped death/censor pair within an arm. -/
lemma arm_recur_cappedDeath_censor_map_eq_prod
    (P : SubjectLaw) (hRecurDeath : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (a : Arm) :
    P.latent.map (fun z : LatentSubject =>
        ((z.recur a, cappedDeathRecord (z.death a)), z.censor a)) =
      ((P.latent.map (fun z : LatentSubject => z.recur a)).prod
        (P.latent.map (fun z : LatentSubject =>
          cappedDeathRecord (z.death a)))).prod
            (P.latent.map (fun z : LatentSubject => z.censor a)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have hraw := arm_recur_death_censor_map_eq_prod P hRecurDeath hCensor a
  have hleft : Measurable (fun z : LatentSubject =>
      ((z.recur a, z.death a), z.censor a)) := by fun_prop
  calc
    _ = Measure.map capArmTriple
        (P.latent.map (fun z : LatentSubject =>
          ((z.recur a, z.death a), z.censor a))) := by
      rw [Measure.map_map measurable_capArmTriple hleft]
      rfl
    _ = Measure.map capArmTriple
        (((P.latent.map (fun z : LatentSubject => z.recur a)).prod
          (P.latent.map (fun z : LatentSubject => z.death a))).prod
            (P.latent.map (fun z : LatentSubject => z.censor a))) := by rw [hraw]
    _ = _ := by
      change Measure.map (Prod.map (Prod.map id cappedDeathRecord) id)
        (((P.latent.map (fun z : LatentSubject => z.recur a)).prod
          (P.latent.map (fun z : LatentSubject => z.death a))).prod
            (P.latent.map (fun z : LatentSubject => z.censor a))) = _
      have houter := Measure.map_prod_map
        ((P.latent.map (fun z : LatentSubject => z.recur a)).prod
          (P.latent.map (fun z : LatentSubject => z.death a)))
        (P.latent.map (fun z : LatentSubject => z.censor a))
        (measurable_id.prodMap measurable_cappedDeathRecord) measurable_id
      rw [← houter]
      have hinner := Measure.map_prod_map
        (P.latent.map (fun z : LatentSubject => z.recur a))
        (P.latent.map (fun z : LatentSubject => z.death a))
        measurable_id measurable_cappedDeathRecord
      rw [← hinner]
      simp only [Measure.map_id]
      rw [Measure.map_map measurable_cappedDeathRecord
        (measurable_latentSubject_death a)]
      rfl

/-- The complete same-arm recurrence configuration jointly with capped death
and censor data is identified by the frozen assumptions. -/
lemma arm_recur_cappedDeath_censor_map_eq
    (P Q : SubjectLaw)
    (hRecurMarginal : ∀ a, P.latent.map (fun z : LatentSubject => z.recur a) =
      Q.latent.map (fun z : LatentSubject => z.recur a))
    (hDeathP : DeathHazard P) (hDeathQ : DeathHazard Q)
    (hRecurDeathP : RecurrenceDeathIndependence P)
    (hRecurDeathQ : RecurrenceDeathIndependence Q)
    (hCensorP : IndependentCensoring P) (hCensorQ : IndependentCensoring Q)
    (hHazard : P.hazard = Q.hazard)
    (hCensorMarginal : P.latent.map LatentSubject.censor =
      Q.latent.map LatentSubject.censor) (a : Arm) :
    P.latent.map (fun z : LatentSubject =>
        ((z.recur a, cappedDeathRecord (z.death a)), z.censor a)) =
      Q.latent.map (fun z : LatentSubject =>
        ((z.recur a, cappedDeathRecord (z.death a)), z.censor a)) := by
  rw [arm_recur_cappedDeath_censor_map_eq_prod P hRecurDeathP hCensorP a,
    arm_recur_cappedDeath_censor_map_eq_prod Q hRecurDeathQ hCensorQ a,
    hRecurMarginal a,
    map_cappedDeathRecord_eq_of_hazard_eq P Q hDeathP hDeathQ hHazard a]
  congr 1
  calc
    P.latent.map (fun z : LatentSubject => z.censor a) =
        Measure.map (Function.eval a)
          (P.latent.map LatentSubject.censor) := by
      rw [Measure.map_map (measurable_pi_apply a)
        measurable_latentSubject_censorFamily]
      rfl
    _ = Measure.map (Function.eval a)
          (Q.latent.map LatentSubject.censor) := by rw [hCensorMarginal]
    _ = Q.latent.map (fun z : LatentSubject => z.censor a) := by
      rw [Measure.map_map (measurable_pi_apply a)
        measurable_latentSubject_censorFamily]
      rfl

/-- Turn a complete recurrence configuration and capped exit inputs into the
observed exit pair and stopped recurrence configuration. -/
@[no_expose]
noncomputable def armExitStoppedFromCapped
    (q : (RecurConfig × (ℝ × Bool)) × ENNReal) :
      (ℝ × Bool) × RecurConfig :=
  let e := armExitFromCapped (q.1.2, q.2)
  (e, q.1.1.stopAt e.1)

@[fun_prop]
lemma measurable_armExitStoppedFromCapped :
    Measurable armExitStoppedFromCapped := by
  let he : (RecurConfig × (ℝ × Bool)) × ENNReal → ℝ × Bool :=
    fun q => armExitFromCapped (q.1.2, q.2)
  have hme : Measurable he := measurable_armExitFromCapped.comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hr : Measurable (fun q : (RecurConfig × (ℝ × Bool)) × ENNReal =>
      q.1.1.stopAt (he q).1) := RecurConfig.measurable_stopAt.comp
    ((measurable_fst.comp hme).prodMk
      (measurable_fst.comp measurable_fst))
  exact hme.prodMk hr

/-- The armwise observed exit and stopped recurrence joint law is identified. -/
lemma arm_exitStopped_map_eq
    (P Q : SubjectLaw)
    (hRecurMarginal : ∀ a, P.latent.map (fun z : LatentSubject => z.recur a) =
      Q.latent.map (fun z : LatentSubject => z.recur a))
    (hDeathP : DeathHazard P) (hDeathQ : DeathHazard Q)
    (hRecurDeathP : RecurrenceDeathIndependence P)
    (hRecurDeathQ : RecurrenceDeathIndependence Q)
    (hCensorP : IndependentCensoring P) (hCensorQ : IndependentCensoring Q)
    (hHazard : P.hazard = Q.hazard)
    (hCensorMarginal : P.latent.map LatentSubject.censor =
      Q.latent.map LatentSubject.censor) (a : Arm) :
    P.latent.map (fun z : LatentSubject =>
        ((min (z.death a) (censorHorizon z a),
            decide (z.death a ≤ censorHorizon z a)),
          (z.recur a).stopAt (min (z.death a) (censorHorizon z a)))) =
      Q.latent.map (fun z : LatentSubject =>
        ((min (z.death a) (censorHorizon z a),
            decide (z.death a ≤ censorHorizon z a)),
          (z.recur a).stopAt (min (z.death a) (censorHorizon z a)))) := by
  have hjoint := arm_recur_cappedDeath_censor_map_eq P Q hRecurMarginal
    hDeathP hDeathQ hRecurDeathP hRecurDeathQ hCensorP hCensorQ hHazard
    hCensorMarginal a
  have hm : Measurable (fun z : LatentSubject =>
      ((z.recur a, cappedDeathRecord (z.death a)), z.censor a)) := by fun_prop
  calc
    _ = P.latent.map (fun z : LatentSubject => armExitStoppedFromCapped
        ((z.recur a, cappedDeathRecord (z.death a)), z.censor a)) := by
      congr 1
      funext z
      rw [show censorHorizon z a = censorHorizonValue (z.censor a) from
        censorHorizon_eq_value z a]
      simp only [armExitStoppedFromCapped, armExitFromCapped_eq]
    _ = Measure.map armExitStoppedFromCapped
        (P.latent.map (fun z : LatentSubject =>
          ((z.recur a, cappedDeathRecord (z.death a)), z.censor a))) := by
      exact (Measure.map_map measurable_armExitStoppedFromCapped hm).symm
    _ = Measure.map armExitStoppedFromCapped
        (Q.latent.map (fun z : LatentSubject =>
          ((z.recur a, cappedDeathRecord (z.death a)), z.censor a))) := by rw [hjoint]
    _ = Q.latent.map (fun z : LatentSubject => armExitStoppedFromCapped
        ((z.recur a, cappedDeathRecord (z.death a)), z.censor a)) := by
      exact Measure.map_map measurable_armExitStoppedFromCapped hm
    _ = _ := by
      congr 1
      funext z
      rw [show censorHorizon z a = censorHorizonValue (z.censor a) from
        censorHorizon_eq_value z a]
      simp only [armExitStoppedFromCapped, armExitFromCapped_eq]

/-- Exit and stopped recurrence data in one arm as a function of the latent
block independent of assignment. -/
@[expose] public noncomputable def restArmExitStopped (a : Arm)
    (r : (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) :
      (ℝ × Bool) × RecurConfig :=
  let e := restArmExit a r
  (e, (r.1 a).stopAt e.1)

@[simp]
lemma restArmExitStopped_apply (a : Arm)
    (r : (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))) :
    restArmExitStopped a r =
      ((min (r.2.1 a) (censorHorizonValue (r.2.2 a)),
          decide (r.2.1 a ≤ censorHorizonValue (r.2.2 a))),
        (r.1 a).stopAt (min (r.2.1 a) (censorHorizonValue (r.2.2 a)))) := by
  rw [restArmExitStopped, restArmExit_apply]

@[fun_prop]
lemma measurable_restArmExitStopped (a : Arm) :
    Measurable (restArmExitStopped a) := by
  have he := measurable_restArmExit a
  have hr : Measurable (fun r :
      (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal)) =>
        (r.1 a).stopAt (restArmExit a r).1) :=
    RecurConfig.measurable_stopAt.comp
      ((measurable_fst.comp he).prodMk
        ((measurable_pi_apply a).comp measurable_fst))
  exact he.prodMk hr

/-- The joint exit-record/stopped-recurrence law is identified for arbitrary
subject laws satisfying the frozen assumptions. -/
lemma exitStoppedLaw_eq
    (P Q : SubjectLaw)
    (hRandomP : RandomAssignment P) (hRandomQ : RandomAssignment Q)
    (hAssignmentP : AssignmentLaw P) (hAssignmentQ : AssignmentLaw Q)
    (hRecurMarginal : ∀ a, P.latent.map (fun z : LatentSubject => z.recur a) =
      Q.latent.map (fun z : LatentSubject => z.recur a))
    (hDeathP : DeathHazard P) (hDeathQ : DeathHazard Q)
    (hRecurDeathP : RecurrenceDeathIndependence P)
    (hRecurDeathQ : RecurrenceDeathIndependence Q)
    (hCensorP : IndependentCensoring P) (hCensorQ : IndependentCensoring Q)
    (hp : P.p = Q.p)
    (hHazard : P.hazard = Q.hazard)
    (hCensorMarginal : P.latent.map LatentSubject.censor =
      Q.latent.map LatentSubject.censor) :
    exitStoppedLaw P = exitStoppedLaw Q := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure Q.latent := ⟨Q.prob⟩
  let rest : LatentSubject →
      (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal)) :=
    fun z => (z.recur, z.death, z.censor)
  have hrest : Measurable rest := by dsimp [rest]; fun_prop
  let packed : Arm × ((ℝ × Bool) × RecurConfig) →
      ExitRecord × RecurConfig := fun q => ((q.1, q.2.1), q.2.2)
  have hpacked : Measurable packed := by dsimp [packed]; fun_prop
  have harm : ∀ a,
      Measure.map (restArmExitStopped a) (P.latent.map rest) =
        Measure.map (restArmExitStopped a) (Q.latent.map rest) := by
    intro a
    rw [Measure.map_map (measurable_restArmExitStopped a) hrest,
      Measure.map_map (measurable_restArmExitStopped a) hrest]
    have hfun : (restArmExitStopped a ∘ rest) = fun z : LatentSubject =>
        ((min (z.death a) (censorHorizon z a),
            decide (z.death a ≤ censorHorizon z a)),
          (z.recur a).stopAt
            (min (z.death a) (censorHorizon z a))) := by
      funext z
      rw [censorHorizon_eq_value]
      exact restArmExitStopped_apply a (rest z)
    rw [hfun]
    exact arm_exitStopped_map_eq P Q hRecurMarginal hDeathP hDeathQ
      hRecurDeathP hRecurDeathQ hCensorP hCensorQ hHazard
      hCensorMarginal a
  have hmix := map_select_prod_eq
    (P.latent.map LatentSubject.treatment)
    (Q.latent.map LatentSubject.treatment)
    (P.latent.map rest) (Q.latent.map rest) restArmExitStopped
    measurable_restArmExitStopped
    (treatment_map_eq_of_assignment P Q hAssignmentP hAssignmentQ hp) harm
  unfold exitStoppedLaw
  calc
    _ = Measure.map packed (Measure.map
        (fun q => (q.1, restArmExitStopped q.1 q.2))
        ((P.latent.map LatentSubject.treatment).prod
          (P.latent.map rest))) := by
      rw [← treatment_rest_map_eq_prod P hRandomP,
        Measure.map_map hpacked
          (by apply measurable_from_prod_countable_right; intro a
              exact measurable_const.prodMk (measurable_restArmExitStopped a)),
        Measure.map_map (hpacked.comp
          (by apply measurable_from_prod_countable_right; intro a
              exact measurable_const.prodMk (measurable_restArmExitStopped a)))
          (measurable_latentSubject_treatment.prodMk hrest)]
      congr 1
    _ = Measure.map packed (Measure.map
        (fun q => (q.1, restArmExitStopped q.1 q.2))
        ((Q.latent.map LatentSubject.treatment).prod
          (Q.latent.map rest))) := by rw [hmix]
    _ = _ := by
      rw [← treatment_rest_map_eq_prod Q hRandomQ,
        Measure.map_map hpacked
          (by apply measurable_from_prod_countable_right; intro a
              exact measurable_const.prodMk (measurable_restArmExitStopped a)),
        Measure.map_map (hpacked.comp
          (by apply measurable_from_prod_countable_right; intro a
              exact measurable_const.prodMk (measurable_restArmExitStopped a)))
          (measurable_latentSubject_treatment.prodMk hrest)]
      congr 1

/-- Consequently the complete observed history law is identified. -/
lemma observedLaw_eq_of_recur_arm_map_eq
    (P Q : SubjectLaw)
    (hRandomP : RandomAssignment P) (hRandomQ : RandomAssignment Q)
    (hAssignmentP : AssignmentLaw P) (hAssignmentQ : AssignmentLaw Q)
    (hRecurMarginal : ∀ a, P.latent.map (fun z : LatentSubject => z.recur a) =
      Q.latent.map (fun z : LatentSubject => z.recur a))
    (hDeathP : DeathHazard P) (hDeathQ : DeathHazard Q)
    (hRecurDeathP : RecurrenceDeathIndependence P)
    (hRecurDeathQ : RecurrenceDeathIndependence Q)
    (hCensorP : IndependentCensoring P) (hCensorQ : IndependentCensoring Q)
    (hp : P.p = Q.p)
    (hHazard : P.hazard = Q.hazard)
    (hCensorMarginal : P.latent.map LatentSubject.censor =
      Q.latent.map LatentSubject.censor) :
    observedLaw P = observedLaw Q := by
  rw [observedLaw_eq_map_exitStoppedLaw, observedLaw_eq_map_exitStoppedLaw,
    exitStoppedLaw_eq P Q hRandomP hRandomQ hAssignmentP hAssignmentQ
      hRecurMarginal hDeathP hDeathQ hRecurDeathP hRecurDeathQ
      hCensorP hCensorQ hp hHazard hCensorMarginal]

lemma observedLaw_eq
    (P Q : SubjectLaw)
    (hRandomP : RandomAssignment P) (hRandomQ : RandomAssignment Q)
    (hAssignmentP : AssignmentLaw P) (hAssignmentQ : AssignmentLaw Q)
    (hPoissonP : PoissonRecurrence P) (hPoissonQ : PoissonRecurrence Q)
    (hDeathP : DeathHazard P) (hDeathQ : DeathHazard Q)
    (hRecurDeathP : RecurrenceDeathIndependence P)
    (hRecurDeathQ : RecurrenceDeathIndependence Q)
    (hCensorP : IndependentCensoring P) (hCensorQ : IndependentCensoring Q)
    (hp : P.p = Q.p) (hLam : P.lam = Q.lam)
    (hHazard : P.hazard = Q.hazard)
    (hCensorMarginal : P.latent.map LatentSubject.censor =
      Q.latent.map LatentSubject.censor) : observedLaw P = observedLaw Q := by
  apply observedLaw_eq_of_recur_arm_map_eq P Q hRandomP hRandomQ
    hAssignmentP hAssignmentQ
  · exact recur_arm_map_eq_of_lam_eq P Q hPoissonP hPoissonQ hLam
  · exact hDeathP
  · exact hDeathQ
  · exact hRecurDeathP
  · exact hRecurDeathQ
  · exact hCensorP
  · exact hCensorQ
  · exact hp
  · exact hHazard
  · exact hCensorMarginal

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
