module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Finite-horizon stopped recurrent-event experiment

A generic arm, a finite Poisson sample of points with measurable event times,
and independent death and censor times form a product experiment. The observed
history retains only the points before the first exit or the fixed horizon.
The primitive time-intensity law and cumulative-hazard survival equation are
model assumptions; observable risk and event laws are derived in later files.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]

/-- [A nonnegative hazard](hyp:h) and [a time](hyp:t) determine [the survival
probability through that time](goal). -/
noncomputable def hazardSurvival (h : ℝ → ℝ≥0) (t : ℝ) : ℝ :=
  Real.exp (-(∫ u in (0 : ℝ)..t, (h u : ℝ)))

/-- [An arm space](hyp:A) and [a recurrence-mark space](hyp:X) specify a
finite-horizon Poisson recurrent-event model with independent assignment,
death, and censoring blocks. -/
structure Model (A X : Type*) [MeasurableSpace A] [MeasurableSpace X] where
  armLaw : Measure A
  armProb : IsProbabilityMeasure armLaw
  pointLaw : Measure X
  pointProb : IsProbabilityMeasure pointLaw
  poissonRate : ℝ≥0
  deathLaw : Measure ℝ
  deathProb : IsProbabilityMeasure deathLaw
  censorLaw : Measure ℝ
  censorProb : IsProbabilityMeasure censorLaw
  horizon : ℝ
  horizon_nonneg : 0 ≤ horizon
  time : X → ℝ
  measurable_time : Measurable time
  hazard : ℝ → ℝ≥0
  measurable_hazard : Measurable hazard
  hazard_integrable : IntervalIntegrable (fun t : ℝ => (hazard t : ℝ)) volume 0 horizon
  intensity : ℝ → ℝ≥0
  measurable_intensity : Measurable intensity
  primitive_intensity :
    Measure.map time ((poissonRate : ℝ≥0∞) • pointLaw) =
      (volume.restrict (Ico 0 horizon)).withDensity
        (fun t => (intensity t : ℝ≥0∞))
  death_survival : ∀ t ∈ Icc (0 : ℝ) horizon,
    deathLaw (Ici t) = ENNReal.ofReal (hazardSurvival hazard t)

/-- [An arm space](hyp:A) and [a recurrence-mark space](hyp:X) determine [one
primitive outcome](goal), consisting of an arm, a finite recurrence sample,
a death time, and an independent censoring time. -/
abbrev Outcome (A X : Type*) [MeasurableSpace X] :=
  A × (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X × (ℝ × ℝ))

/-- [A recurrent-event model](hyp:M) determines [the independent product law
of its assignment, recurrence, death, and censoring blocks](goal). -/
noncomputable def Model.primitiveLaw (M : Model A X) : Measure (Outcome A X) := by
  letI := M.pointProb
  exact M.armLaw.prod
    ((Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
      M.pointLaw M.poissonRate).prod (M.deathLaw.prod M.censorLaw))

/-- [A recurrent-event model](hyp:M) and [a primitive outcome](hyp:ω)
determine [the administrative stopping time](goal), the earliest of death,
censoring, and the fixed horizon. -/
def Model.stopTime (M : Model A X) (ω : Outcome A X) : ℝ :=
  min (min ω.2.2.1 ω.2.2.2) M.horizon

/-- [A recurrent-event model](hyp:M) and [a primitive outcome](hyp:ω)
determine [the stopped observed history](goal): the arm, exit time, death
indicator, and recurrence times retained before exit. Missing sequence
positions use a value beyond the fixed horizon. -/
noncomputable def Model.observe (M : Model A X) (ω : Outcome A X) :
    A × (ℝ × (Bool × (ℕ → ℝ))) :=
  (ω.1, M.stopTime ω,
    decide (ω.2.2.1 ≤ ω.2.2.2 ∧ ω.2.2.1 < M.horizon),
    fun n => if hn : n < ω.2.1.1 then
      if M.time (ω.2.1.2 ⟨n, hn⟩) < M.stopTime ω then
        M.time (ω.2.1.2 ⟨n, hn⟩) else M.horizon + 1
      else M.horizon + 1)

/-- [A recurrent-event model](hyp:M) determines [the observed-history law](goal)
by applying its stopped-observation rule to the independent primitive experiment. -/
noncomputable def Model.observedLaw (M : Model A X) :
    Measure (A × (ℝ × (Bool × (ℕ → ℝ)))) :=
  Measure.map M.observe M.primitiveLaw

end Causalean.Stat.RecurrentEvent
