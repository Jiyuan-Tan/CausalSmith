module
public import Causalean.Stat.RecurrentEvent.Observation

/-!
# Armwise observable risk sets

The observed risk probability and its model-side time measure factor through
independent assignment, death, and censor blocks before the fixed horizon.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace X]

/-- [A recurrent-event model](hyp:M), [an arm](hyp:a), and [a time](hyp:t)
determine [that arm's observable risk probability](goal): the joint
probability, under the observed-history law, that the unit is assigned to
that arm and its observed exit time (the earliest of death, censoring, and the
fixed horizon) is at least that time. It is a joint probability with the arm,
not a probability conditional on the arm. -/
noncomputable def Model.riskProbability (M : Model A X) (a : A) (t : ℝ) : ℝ≥0∞ :=
  M.observedLaw {y | y.1 = a ∧ t ≤ y.2.1}

/-- [A recurrent-event model](hyp:M) and [an arm](hyp:a) determine [the
armwise risk-set measure](goal): the measure on the time axis that has, with
respect to Lebesgue measure on the half-open interval from zero up to (but
excluding) the fixed horizon, density equal at each time t to the arm's
assignment probability times the probability that death occurs at or after t
times the probability that censoring occurs at or after t. -/
noncomputable def Model.riskSetMeasure (M : Model A X) (a : A) : Measure ℝ :=
  (volume.restrict (Ico 0 M.horizon)).withDensity
    (fun t => M.armLaw {a} * M.deathLaw (Ici t) * M.censorLaw (Ici t))

/-- [A recurrent-event model](hyp:M), [an arm](hyp:a), and [a time](hyp:t)
[between zero and the fixed horizon, endpoints included](hyp:ht) have [an
observable risk probability equal to the arm's assignment probability times
the probability that death occurs at or after that time times the probability
that censoring occurs at or after that time](goal). -/
theorem Model.risk_factorization (M : Model A X) (a : A) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) M.horizon) :
    M.riskProbability a t = M.armLaw {a} * M.deathLaw (Ici t) *
      M.censorLaw (Ici t) := by
  letI := M.armProb
  letI := M.pointProb
  letI := M.deathProb
  letI := M.censorProb
  have hs : MeasurableSet {y : A × (ℝ × (Bool × (ℕ → ℝ))) |
      y.1 = a ∧ t ≤ y.2.1} := by measurability
  have hpre : M.observe ⁻¹' {y : A × (ℝ × (Bool × (ℕ → ℝ))) |
      y.1 = a ∧ t ≤ y.2.1} =
      ({a} : Set A) ×ˢ (Set.univ ×ˢ ((Ici t) ×ˢ (Ici t))) := by
    ext ω
    simp [Model.observe, Model.stopTime, ht.2, and_assoc, Prod.le_def]
  unfold Model.riskProbability Model.observedLaw
  rw [Measure.map_apply M.measurable_observe hs, hpre]
  unfold Model.primitiveLaw
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  simp only [measure_univ, one_mul, mul_assoc]

end Causalean.Stat.RecurrentEvent
