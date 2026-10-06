module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedObservableCompaction

/-! # Interior promoted observable equality -/

public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Below the administrative horizon, the promoted death-event cumulative
measure is the paper potential death-before-censor probability. -/
lemma ModelClass.promotedArmModel_deathEventMeasure_Iic
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) {t : ℝ} (ht : t < 1) :
    (promotedArmModel P hP a).deathEventMeasure () (Set.Iic t) =
      P.latent {z : LatentSubject |
        z.death a ≤ censorHorizon z a ∧ z.death a ≤ t} := by
  let M := promotedArmModel P hP a
  rw [M.death_event_measure_primitive,
    ← hP.map_latentToPromotedArmOutcome_eq_primitiveLaw a]
  rw [Measure.restrict_map]
  · rw [Measure.map_map]
    · rw [Measure.map_apply]
      · rw [Measure.restrict_apply]
        · congr 1
          ext z
          simp [M, Causalean.Stat.RecurrentEvent.Model.stopTime, ht]
          constructor
          · rintro ⟨hdc, hd1, hdt⟩
            exact ⟨hd1, hdc⟩
          · rintro ⟨hdc, hdt⟩
            exact ⟨hdt, hdc, lt_of_le_of_lt hdt ht⟩
        · exact measurableSet_Iic.preimage (by fun_prop)
      · fun_prop
      · exact measurableSet_Iic
    · fun_prop
    · fun_prop
  · fun_prop
  · measurability

/-- The paper death cumulative is the assignment-scaled promoted death-event
cumulative at every strictly sub-horizon time. -/
lemma ModelClass.observedArmDeathMass_eq_promoted_Iic
    {c : ClassConstants} {P : SubjectLaw} (hP : ModelClass c P)
    (a : Arm) {t : ℝ} (ht : t < 1) :
    observedArmDeathMass P a t = ENNReal.ofReal (P.p a) *
      (promotedArmModel P hP a).deathEventMeasure () (Set.Iic t) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let s : Set LatentRest := {r |
    r.2.1 a ≤ censorHorizonValue (r.2.2 a) ∧ r.2.1 a ≤ t}
  have hs : MeasurableSet s := by
    unfold s
    measurability
  have hind := hP.randomAssignment.measure_inter_preimage_eq_mul
    ({a} : Set Arm) s (measurableSet_singleton a) hs
  rw [observedArmDeathMass_eq_latent]
  have hevent : latentArmDeathThrough a t =
      (fun z : LatentSubject ↦ z.treatment) ⁻¹' ({a} : Set Arm) ∩
        (fun z : LatentSubject ↦ (z.recur, z.death, z.censor)) ⁻¹' s := by
    ext z
    simp only [latentArmDeathThrough, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, s, censorHorizon_eq_value]
    constructor
    · rintro ⟨ha, hdc, hmin⟩
      have hdt : z.death a ≤ t := by
        rw [min_eq_left hdc] at hmin
        exact hmin
      exact ⟨ha, hdc, hdt⟩
    · rintro ⟨ha, hdc, hdt⟩
      refine ⟨ha, hdc, ?_⟩
      rw [min_eq_left hdc]
      exact hdt
  rw [hevent, hind]
  congr 1
  · rw [← hP.assignmentLaw a]
    exact (ENNReal.ofReal_toReal (measure_ne_top P.latent _)).symm
  · rw [hP.promotedArmModel_deathEventMeasure_Iic a ht]
    congr 1

/-- Equal paper observed laws identify all promoted death-event cumulative
masses strictly below the horizon. -/
lemma promotedArmModel_deathEventMeasure_Iic_eq_of_observedLaw_eq
    {c : ClassConstants} {P Q : SubjectLaw}
    (hP : ModelClass c P) (hQ : ModelClass c Q)
    (hobs : observedLaw P = observedLaw Q) (a : Arm)
    {t : ℝ} (ht : t < 1) :
    (promotedArmModel P hP a).deathEventMeasure () (Set.Iic t) =
      (promotedArmModel Q hQ a).deathEventMeasure () (Set.Iic t) := by
  have hp := hP.assignmentProbability_eq_of_observedLaw_eq hQ hobs a
  have hm := observedArmDeathMass_congr hobs a t
  rw [hP.observedArmDeathMass_eq_promoted_Iic a ht,
    hQ.observedArmDeathMass_eq_promoted_Iic a ht, ← hp] at hm
  have hzero : ENNReal.ofReal (P.p a) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le c.pMin_pos (hP.treatmentOverlap a))).ne'
  have htop : ENNReal.ofReal (P.p a) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_left_inj hzero htop).mp
  simpa [mul_comm] using hm


end CausalSmith.Stat.RecurrentEndpointCensorFrontier
