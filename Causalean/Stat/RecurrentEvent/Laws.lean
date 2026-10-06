module
public import Causalean.Stat.RecurrentEvent.DeathStoppedMean
public import Causalean.Stat.RecurrentEvent.Identification

/-!
# Finite-horizon endpoint laws

The main risk, event-density, and identification laws are exported with
their empty zero-horizon special cases.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X Y : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- [A recurrent-event model](hyp:M), [an arm](hyp:a), and [a zero
administrative horizon](hyp:hH) have [no observable death event before
exit](goal). -/
theorem Model.death_event_zero_horizon (M : Model A X) (a : A)
    (hH : M.horizon = 0) : M.deathEventMeasure a = 0 := by
  rw [M.death_event_density]
  simp [Model.riskSetMeasure, hH]

/-- [A recurrent-event model](hyp:M), [an arm](hyp:a), and [a zero
administrative horizon](hyp:hH) have [no observable recurrence event before
exit](goal). -/
theorem Model.recurrence_event_zero_horizon (M : Model A X) (a : A)
    (hH : M.horizon = 0) : M.recurrenceEventMeasure a = 0 := by
  rw [M.recurrence_event_density]
  simp [Model.riskSetMeasure, hH]

/-- [A recurrent-event model](hyp:M) with [a zero administrative
horizon](hyp:hH) has [an independently death-stopped Poisson recurrence mean
of zero](goal). -/
theorem Model.death_stopped_mean_zero_horizon (M : Model A X)
    (hH : M.horizon = 0) : M.deathStoppedCountMean = 0 := by
  rw [M.death_stopped_poisson_mean]
  simp [hH]

end Causalean.Stat.RecurrentEvent
