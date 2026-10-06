module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Continuity bridge for recurrent-endpoint identification

This module turns almost-everywhere equality of the armwise recurrence and
death intensities into pointwise equality on the closed study horizon.  It is
the final deterministic step after the observed event measures identify their
Lebesgue densities.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Hölder regularity in the model class supplies a continuous recurrence
intensity on the whole study horizon. -/
lemma ModelClass.recurrenceContinuousOn {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    ContinuousOn (P.lam a) (Set.Icc (0 : ℝ) 1) :=
  (hP.recurrenceHolder a).1.continuousOn

/-- Hölder regularity in the model class supplies a continuous death hazard
on the whole study horizon. -/
lemma ModelClass.deathContinuousOn {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) :
    ContinuousOn (P.hazard a) (Set.Icc (0 : ℝ) 1) :=
  (hP.deathHolder a).1.continuousOn

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
