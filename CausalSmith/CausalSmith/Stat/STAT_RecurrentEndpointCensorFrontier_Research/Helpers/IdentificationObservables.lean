module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Basic

/-!
# Observable summaries for recurrent-endpoint identification

This module exposes the armwise risk, death, and stopped-recurrence summaries
as measurable functionals of the observed-history law.  It also records their
exact pullbacks along the observation map, so later identification arguments
can work entirely with observable quantities.

`Basic` represents recurrence observations by finite configurations and their
cumulative counts.  Constructing a time-indexed random measure would require
an additional measurable configuration-to-measure interface, so the exact
cumulative functional below is the adapter supplied here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-! ## Observed-history coordinates -/

/-- The treatment coordinate of an observed history is measurable. -/
@[fun_prop]
lemma measurable_obsHistory_treatment :
    Measurable (fun o : ObsHistory => o.treatment) :=
  measurable_fst.comp measurable_obsHistory_toCoordinates

/-- The exit-time coordinate of an observed history is measurable. -/
@[fun_prop]
lemma measurable_obsHistory_exit :
    Measurable (fun o : ObsHistory => o.exit) :=
  (measurable_fst.comp measurable_snd).comp
    measurable_obsHistory_toCoordinates

/-- The death-indicator coordinate of an observed history is measurable. -/
@[fun_prop]
lemma measurable_obsHistory_deathInd :
    Measurable (fun o : ObsHistory => o.deathInd) :=
  ((measurable_fst.comp measurable_snd).comp measurable_snd).comp
    measurable_obsHistory_toCoordinates

/-- The stopped recurrence configuration of an observed history is
measurable. -/
@[fun_prop]
lemma measurable_obsHistory_recur :
    Measurable (fun o : ObsHistory => o.recur) :=
  ((measurable_snd.comp measurable_snd).comp measurable_snd).comp
    measurable_obsHistory_toCoordinates

/-! ## Armwise risk sets -/

/-- Observed histories assigned to arm `a` that remain under observation at
time `t`. -/
def observedArmAtRisk (a : Arm) (t : ℝ) : Set ObsHistory :=
  {o | o.treatment = a ∧ t ≤ o.exit}

/-- The observable arm-at-risk set is measurable. -/
lemma measurableSet_observedArmAtRisk (a : Arm) (t : ℝ) :
    MeasurableSet (observedArmAtRisk a t) := by
  exact (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
    (measurableSet_le measurable_const measurable_obsHistory_exit)

/-- The latent event whose observation is an arm-`a` history still at risk at
time `t`. -/
def latentArmAtRisk (a : Arm) (t : ℝ) : Set LatentSubject :=
  {z | z.treatment = a ∧
    t ≤ min (z.death a) (censorHorizon z a)}

/-- Pulling the observable risk set back along `observe` gives exactly the
corresponding latent event. -/
lemma observe_preimage_observedArmAtRisk (a : Arm) (t : ℝ) :
    observe ⁻¹' observedArmAtRisk a t = latentArmAtRisk a t := by
  ext z
  simp only [mem_preimage, observedArmAtRisk, mem_ofPred_eq, latentArmAtRisk,
    observe]
  constructor
  · rintro ⟨hza, ht⟩
    simpa [hza] using And.intro hza ht
  · rintro ⟨hza, ht⟩
    simpa [hza] using And.intro hza ht

/-- Observable-law mass of the arm-at-risk set. -/
noncomputable def observedArmAtRiskMass (P : SubjectLaw) (a : Arm) (t : ℝ) :
    ℝ≥0∞ :=
  observedLaw P (observedArmAtRisk a t)

/-- The observable risk mass is exactly the latent mass of its pullback. -/
lemma observedArmAtRiskMass_eq_latent (P : SubjectLaw) (a : Arm) (t : ℝ) :
    observedArmAtRiskMass P a t = P.latent (latentArmAtRisk a t) := by
  rw [observedArmAtRiskMass, observedLaw,
    Measure.map_apply measurable_observe
      (measurableSet_observedArmAtRisk a t),
    observe_preimage_observedArmAtRisk]

/-! ## Armwise death events -/

/-- Observed arm-`a` deaths occurring by time `t`. -/
def observedArmDeathThrough (a : Arm) (t : ℝ) : Set ObsHistory :=
  {o | o.treatment = a ∧ o.deathInd = true ∧ o.exit ≤ t}

/-- The observable armwise death event through `t` is measurable. -/
lemma measurableSet_observedArmDeathThrough (a : Arm) (t : ℝ) :
    MeasurableSet (observedArmDeathThrough a t) := by
  exact (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
    ((measurableSet_eq_fun measurable_obsHistory_deathInd measurable_const).inter
      (measurableSet_le measurable_obsHistory_exit measurable_const))

/-- The latent arm-`a` death-before-censoring event occurring by time `t`. -/
def latentArmDeathThrough (a : Arm) (t : ℝ) : Set LatentSubject :=
  {z | z.treatment = a ∧
    z.death a ≤ censorHorizon z a ∧
    min (z.death a) (censorHorizon z a) ≤ t}

/-- Pulling the observable death event back along `observe` gives exactly the
corresponding latent event. -/
lemma observe_preimage_observedArmDeathThrough (a : Arm) (t : ℝ) :
    observe ⁻¹' observedArmDeathThrough a t = latentArmDeathThrough a t := by
  ext z
  simp only [mem_preimage, observedArmDeathThrough, mem_ofPred_eq,
    latentArmDeathThrough, observe]
  constructor
  · rintro ⟨hza, hd, ht⟩
    simpa [hza] using And.intro hza (And.intro (of_decide_eq_true hd) ht)
  · rintro ⟨hza, hd, ht⟩
    simpa [hza, hd] using And.intro hza (And.intro (decide_eq_true hd) ht)

/-- Observable-law mass of arm-`a` deaths through time `t`. -/
noncomputable def observedArmDeathMass (P : SubjectLaw) (a : Arm) (t : ℝ) :
    ℝ≥0∞ :=
  observedLaw P (observedArmDeathThrough a t)

/-- The observable death mass is exactly the latent mass of its pullback. -/
lemma observedArmDeathMass_eq_latent (P : SubjectLaw) (a : Arm) (t : ℝ) :
    observedArmDeathMass P a t = P.latent (latentArmDeathThrough a t) := by
  rw [observedArmDeathMass, observedLaw,
    Measure.map_apply measurable_observe
      (measurableSet_observedArmDeathThrough a t),
    observe_preimage_observedArmDeathThrough]

/-! ## Armwise cumulative recurrence counts -/

/-- The armwise cumulative observed recurrence count through time `t`, with
histories from the other arm contributing zero. -/
noncomputable def observedArmRecurrenceCount (a : Arm) (t : ℝ)
    (o : ObsHistory) : ℝ≥0∞ :=
  if o.treatment = a then (o.recur.countLE t : ℝ≥0∞) else 0

/-- The cumulative observed recurrence count is measurable. -/
@[fun_prop]
lemma measurable_observedArmRecurrenceCount (a : Arm) (t : ℝ) :
    Measurable (observedArmRecurrenceCount a t) := by
  unfold observedArmRecurrenceCount
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_obsHistory_treatment measurable_const
  · exact (measurable_of_countable
      (fun n : ℕ => (n : ℝ≥0∞))).comp
        (RecurConfig.measurable_countLE.comp
          (measurable_const.prodMk measurable_obsHistory_recur))
  · exact measurable_const

/-- The observable cumulative armwise recurrence functional under an observed
law. -/
noncomputable def observedArmRecurrenceCumulative
    (P : SubjectLaw) (a : Arm) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ o, observedArmRecurrenceCount a t o ∂observedLaw P

/-- The corresponding latent stopped recurrence count.  The stopping time is
the observed exit generated from the assigned arm. -/
noncomputable def latentStoppedArmRecurrenceCount (a : Arm) (t : ℝ)
    (z : LatentSubject) : ℝ≥0∞ :=
  if z.treatment = a then
    (↑(((z.recur a).stopAt
        (min (z.death a) (censorHorizon z a))).countLE t) : ℝ≥0∞)
  else 0

/-- Evaluating the observable recurrence count after `observe` is exactly the
latent stopped recurrence count. -/
lemma observedArmRecurrenceCount_observe (a : Arm) (t : ℝ)
    (z : LatentSubject) :
    observedArmRecurrenceCount a t (observe z) =
      latentStoppedArmRecurrenceCount a t z := by
  by_cases hza : z.treatment = a
  · simp [observedArmRecurrenceCount, latentStoppedArmRecurrenceCount,
      observe, hza]
  · simp [observedArmRecurrenceCount, latentStoppedArmRecurrenceCount,
      observe, hza]

/-- Change of variables along `observe` identifies the observable cumulative
recurrence functional with the latent expected stopped count. -/
lemma observedArmRecurrenceCumulative_eq_latent
    (P : SubjectLaw) (a : Arm) (t : ℝ) :
    observedArmRecurrenceCumulative P a t =
      ∫⁻ z, latentStoppedArmRecurrenceCount a t z ∂P.latent := by
  rw [observedArmRecurrenceCumulative, observedLaw,
    lintegral_map (measurable_observedArmRecurrenceCount a t)
      measurable_observe]
  apply lintegral_congr
  intro z
  exact observedArmRecurrenceCount_observe a t z

/-! ## Congruence under equality of observed laws -/

/-- Equal observed laws have equal arm-at-risk masses. -/
lemma observedArmAtRiskMass_congr {P Q : SubjectLaw}
    (h : observedLaw P = observedLaw Q) (a : Arm) (t : ℝ) :
    observedArmAtRiskMass P a t = observedArmAtRiskMass Q a t := by
  simp only [observedArmAtRiskMass, h]

/-- Equal observed laws have equal armwise death masses. -/
lemma observedArmDeathMass_congr {P Q : SubjectLaw}
    (h : observedLaw P = observedLaw Q) (a : Arm) (t : ℝ) :
    observedArmDeathMass P a t = observedArmDeathMass Q a t := by
  simp only [observedArmDeathMass, h]

/-- Equal observed laws have equal armwise cumulative recurrence
functionals. -/
lemma observedArmRecurrenceCumulative_congr {P Q : SubjectLaw}
    (h : observedLaw P = observedLaw Q) (a : Arm) (t : ℝ) :
    observedArmRecurrenceCumulative P a t =
      observedArmRecurrenceCumulative Q a t := by
  simp only [observedArmRecurrenceCumulative, h]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
