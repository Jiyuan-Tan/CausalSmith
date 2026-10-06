module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.IdentificationObservables
public import Causalean.Stat.RecurrentEvent

/-!
# Adapter to the promoted recurrent-event substrate

This file records the exact carrier maps used to compare the run-local finite
configuration experiment with `Causalean.Stat.RecurrentEvent.Model`.  It also
isolates the strict-boundary stopped mean used by the promoted model.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

abbrev PromotedObsHistory := Arm × (ℝ × (Bool × (ℕ → ℝ)))

/-- Encode a finite recurrence configuration as the padded time stream used
by the promoted recurrent-event observation carrier. -/
@[no_expose]
noncomputable def promotedRecurrenceStream (s : RecurConfig) : ℕ → ℝ :=
  fun n ↦ (finiteSamplePaddedStream ((2 : ℝ), (0 : ℝ)) s).2 n |>.1

@[fun_prop]
lemma measurable_promotedRecurrenceStream :
    Measurable promotedRecurrenceStream := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_fst.comp
    ((measurable_pi_apply n).comp
      ((finiteSamplePaddedStream_measurable ((2 : ℝ), (0 : ℝ))).snd))

/-- The run-local observed history represented in the promoted stopped-history
carrier. -/
@[no_expose]
noncomputable def obsHistoryToPromoted (o : ObsHistory) : PromotedObsHistory :=
  (o.treatment, o.exit, o.deathInd, promotedRecurrenceStream o.recur)

@[fun_prop]
lemma measurable_obsHistoryToPromoted : Measurable obsHistoryToPromoted := by
  exact measurable_obsHistory_treatment.prodMk
    (measurable_obsHistory_exit.prodMk
      (measurable_obsHistory_deathInd.prodMk
        (measurable_promotedRecurrenceStream.comp measurable_obsHistory_recur)))

/-- The armwise primitive outcome carrier appearing in a promoted model with
recurrence marks `ℝ × ℝ`. -/
abbrev PromotedArmOutcome :=
  Causalean.Stat.RecurrentEvent.Outcome Unit (ℝ × ℝ)

/-- Project one arm of a run-local latent subject to the primitive coordinates
used by an armwise promoted model. -/
@[no_expose]
noncomputable def latentToPromotedArmOutcome (a : Arm)
    (z : LatentSubject) : PromotedArmOutcome :=
  ((), z.recur a, z.death a, censorHorizon z a)

@[fun_prop]
lemma measurable_latentToPromotedArmOutcome (a : Arm) :
    Measurable (latentToPromotedArmOutcome a) := by
  exact measurable_const.prodMk
    ((measurable_latentSubject_recur a).prodMk
      ((measurable_latentSubject_death a).prodMk
        (measurable_censorHorizon.comp
          (measurable_id.prodMk measurable_const))))

/-- The strict stopped recurrence count used by the promoted model.  This
definition deliberately exposes the sole boundary mismatch with the paper's
`clinicalCount`, whose finite-configuration count uses a non-strict cutoff. -/
@[no_expose]
noncomputable def strictClinicalCount (z : LatentSubject) (a : Arm) : ℕ :=
  ∑ i : Fin (z.recur a).1,
    if ((z.recur a).2 i).1 < z.death a ∧ ((z.recur a).2 i).1 < 1
    then 1 else 0

/-- Same-arm recurrence/death independence reconstructs the exact joint
marginal used by the promoted primitive experiment. -/
lemma armRecurrenceDeath_joint_eq_prod (P : SubjectLaw) (a : Arm)
    (hind : RecurrenceDeathIndependence P) :
    P.latent.map (fun z : LatentSubject ↦ (z.recur a, z.death a)) =
      (P.latent.map (fun z : LatentSubject ↦ z.recur a)).prod
        (P.latent.map (fun z : LatentSubject ↦ z.death a)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  exact (hind a).map_prod_eq_prod_map_map
    (measurable_latentSubject_recur a).aemeasurable
    (measurable_latentSubject_death a).aemeasurable

/-- The exact pointwise relation between the promoted strict count and the
run-local non-strict clinical count.  Equality holds precisely when no event
lies on either stopping boundary. -/
lemma strictClinicalCount_eq_clinicalCount_of_no_boundary
    (z : LatentSubject) (a : Arm)
    (hdeath : ∀ i : Fin (z.recur a).1, ((z.recur a).2 i).1 ≠ z.death a)
    (hhorizon : ∀ i : Fin (z.recur a).1, ((z.recur a).2 i).1 ≠ 1) :
    strictClinicalCount z a = clinicalCount z a 1 := by
  unfold strictClinicalCount clinicalCount RecurConfig.countLE
  simp only [RecurConfig.paddedCountLE, finiteSamplePaddedStream]
  apply Finset.sum_congr rfl
  intro i _
  have heq :
      (((z.recur a).2 i).1 < z.death a ∧ ((z.recur a).2 i).1 < 1) ↔
        ((z.recur a).2 i).1 ≤ min 1 (z.death a) := by
    constructor
    · rintro ⟨hd, h1⟩
      exact le_min h1.le hd.le
    · intro hle
      have h1le := hle.trans (min_le_left _ _)
      have hdle := hle.trans (min_le_right _ _)
      exact ⟨lt_of_le_of_ne hdle (hdeath i),
        lt_of_le_of_ne h1le (hhorizon i)⟩
  rw [if_congr heq rfl rfl]
  congr 1
  simp [FiniteSample.count, FiniteSample.points, i.isLt]


end CausalSmith.Stat.RecurrentEndpointCensorFrontier
