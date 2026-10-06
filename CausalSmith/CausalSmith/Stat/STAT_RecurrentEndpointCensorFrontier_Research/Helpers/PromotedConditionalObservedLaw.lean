module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ArbitraryObservedLaw
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedArmModel

/-! # Armwise promoted observed-law bridge -/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Forget the paper's Boolean arm label after restricting to one arm. -/
@[no_expose]
noncomputable def paperArmHistoryToUnit (o : ObsHistory) :
    Unit × (ℝ × (Bool × (ℕ → ℝ))) :=
  ((), o.exit, o.deathInd, promotedRecurrenceStream o.recur)

@[fun_prop] lemma measurable_paperArmHistoryToUnit :
    Measurable paperArmHistoryToUnit := by
  exact measurable_const.prodMk
    (measurable_obsHistory_exit.prodMk
      (measurable_obsHistory_deathInd.prodMk
        (measurable_promotedRecurrenceStream.comp measurable_obsHistory_recur)))

/-- The paper potential outcomes in one arm have exactly the independent
primitive law used by the matching promoted arm model. -/
lemma ModelClass.map_latentToPromotedArmOutcome_eq_primitiveLaw
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P) (a : Arm) :
    P.latent.map (fun z : LatentSubject ↦
      ((), z.recur a, z.death a, censorHorizon z a)) =
      (promotedArmModel P hP a).primitiveLaw := by
  let M := promotedArmModel P hP a
  let R := P.latent.map (fun z : LatentSubject ↦ z.recur a)
  let D := P.latent.map (fun z : LatentSubject ↦ z.death a)
  let C := P.latent.map (fun z : LatentSubject ↦ censorHorizon z a)
  let Craw := P.latent.map (fun z : LatentSubject ↦ z.censor a)
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure R := by
    unfold R
    exact Measure.isProbabilityMeasure_map
      (measurable_latentSubject_recur a).aemeasurable
  letI : IsProbabilityMeasure D := by
    unfold D
    exact Measure.isProbabilityMeasure_map
      (measurable_latentSubject_death a).aemeasurable
  letI : IsProbabilityMeasure C := by
    unfold C
    exact Measure.isProbabilityMeasure_map
      (measurable_censorHorizon.comp
        (measurable_id.prodMk measurable_const)).aemeasurable
  have htriple :
      P.latent.map (fun z : LatentSubject ↦
          ((z.recur a, z.death a), censorHorizon z a)) =
        (R.prod D).prod C := by
    let raw : LatentSubject → (RecurConfig × ℝ) × ENNReal := fun z ↦
      ((z.recur a, z.death a), z.censor a)
    let cap : (RecurConfig × ℝ) × ENNReal → (RecurConfig × ℝ) × ℝ := fun q ↦
      (q.1, censorHorizonValue q.2)
    have hraw := arm_recur_death_censor_map_eq_prod P
      hP.recurrenceDeathIndependence hP.independentCensoring a
    calc
      _ = Measure.map cap (P.latent.map raw) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = Measure.map cap ((R.prod D).prod Craw) := by
        rw [hraw]
      _ = Measure.map (Prod.map id censorHorizonValue) ((R.prod D).prod Craw) := by
        congr 1
      _ = (R.prod D).prod (Measure.map censorHorizonValue Craw) := by
        simpa using (Measure.map_prod_map (R.prod D) Craw measurable_id
          measurable_censorHorizonValue).symm
      _ = (R.prod D).prod C := by
        congr 1
        unfold C Craw
        rw [Measure.map_map measurable_censorHorizonValue
          (measurable_latentSubject_censor a)]
        rfl
  have hassoc : Measure.map MeasurableEquiv.prodAssoc ((R.prod D).prod C) =
      R.prod (D.prod C) := Measure.prodAssoc_prod
  have hunit : (Measure.dirac ()).prod (R.prod (D.prod C)) =
      Measure.map (Prod.mk ()) (R.prod (D.prod C)) := Measure.dirac_prod ()
  let triple : LatentSubject → (RecurConfig × ℝ) × ℝ := fun z ↦
    ((z.recur a, z.death a), censorHorizon z a)
  have htripleMeas : Measurable triple := by
    unfold triple
    fun_prop
  calc
    P.latent.map (fun z : LatentSubject ↦
        ((), z.recur a, z.death a, censorHorizon z a)) =
        Measure.map (Prod.mk () ∘ MeasurableEquiv.prodAssoc)
          (P.latent.map triple) := by
      rw [Measure.map_map (by fun_prop) htripleMeas]
      rfl
    _ = Measure.map (Prod.mk () ∘ MeasurableEquiv.prodAssoc)
          ((R.prod D).prod C) := by rw [htriple]
    _ = Measure.map (Prod.mk ())
          (Measure.map MeasurableEquiv.prodAssoc ((R.prod D).prod C)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = (Measure.dirac ()).prod (R.prod (D.prod C)) := by rw [hassoc, hunit]
    _ = M.primitiveLaw := by
      unfold M C D R Causalean.Stat.RecurrentEvent.Model.primitiveLaw
      rw [← promotedArmModel_recurrenceLaw hP a]
      simp only [promotedArmModel_armLaw, promotedArmModel_deathLaw,
        promotedArmModel_censorLaw]

/-- Consequently, the promoted arm's observed law is the pushforward of the
paper potential-outcome law through the promoted strict observation map. -/
lemma ModelClass.promotedArmModel_observedLaw_eq_map_latent
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P) (a : Arm) :
    (promotedArmModel P hP a).observedLaw =
      P.latent.map ((promotedArmModel P hP a).observe ∘
        (fun z : LatentSubject ↦
          ((), z.recur a, z.death a, censorHorizon z a))) := by
  let M := promotedArmModel P hP a
  calc
    M.observedLaw = Measure.map M.observe M.primitiveLaw := rfl
    _ = Measure.map M.observe
        (P.latent.map (fun z : LatentSubject ↦
          ((), z.recur a, z.death a, censorHorizon z a))) := by
      rw [hP.map_latentToPromotedArmOutcome_eq_primitiveLaw a]
    _ = P.latent.map (M.observe ∘ (fun z : LatentSubject ↦
        ((), z.recur a, z.death a, censorHorizon z a))) :=
      Measure.map_map M.measurable_observe (by fun_prop)


end CausalSmith.Stat.RecurrentEndpointCensorFrontier
