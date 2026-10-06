module
public import Causalean.Stat.RecurrentEvent.Basic
public import Causalean.Stat.RecurrentEvent.CountingProcess
public import Causalean.Stat.RecurrentEvent.DeathDensity
public import Causalean.Stat.RecurrentEvent.DeathEventPrimitive
public import Causalean.Stat.RecurrentEvent.DeathStoppedMean
public import Causalean.Stat.RecurrentEvent.HazardDensity
public import Causalean.Stat.RecurrentEvent.Identification
public import Causalean.Stat.RecurrentEvent.Laws
public import Causalean.Stat.RecurrentEvent.Observation
public import Causalean.Stat.RecurrentEvent.PoissonCampbell
public import Causalean.Stat.RecurrentEvent.RecurrenceDensity
public import Causalean.Stat.RecurrentEvent.RecurrenceEventPrimitive
public import Causalean.Stat.RecurrentEvent.RiskSet
public import Causalean.Stat.RecurrentEvent.TailRetention

/-!
# Finite-horizon recurrent-event laws

This directory packages a finite-horizon Poisson recurrent-event experiment
with independent death and censoring. It supplies observable risk-set and
event-measure factorisations, density identification from stopped histories,
and a death-stopped Poisson mean identity. The `CountingProcess` subdirectory, which is
independent of the recurrent-event model, supplies finite-sample right-censored counting
processes: compensated censor counts, predictable-integral isometries, Nelson–Aalen identities,
and a finite-jump extension.
-/

public section
