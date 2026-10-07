module
public import Causalean.Stat.RecurrentEvent.DeathStoppedMean
public import Causalean.Stat.RecurrentEvent.Identification

/-!
# Recurrent events with a terminal event: observable laws on a finite horizon

In the finite-horizon Poisson recurrent-event model with independent treatment assignment, death
and censoring, the observable death events and recurrence events of an arm have, relative to the
armwise risk-set measure (assignment probability × death survival × censoring survival, on times
before the horizon), densities equal to the death hazard and the recurrence intensity. The mean
number of recurrences before independent death equals the integral over the horizon of death
survival times recurrence intensity, and two models with the same law of the observed stopped
history have the same hazard and intensity almost everywhere where the risk set is positive.
Those results are proved in the imported modules; this file adds their degenerate case of a zero
horizon.

## Main results

* `Model.death_event_zero_horizon`, `Model.recurrence_event_zero_horizon` — with horizon zero the
  observable death-event and recurrence-event measures vanish.
* `Model.death_stopped_mean_zero_horizon` — with horizon zero the death-stopped mean recurrence
  count is zero.

Imported: `Model.death_event_density`, `Model.recurrence_event_density`,
`Model.death_stopped_poisson_mean` (`DeathStoppedMean`) and `Model.identify_densities`
(`Identification`).
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
