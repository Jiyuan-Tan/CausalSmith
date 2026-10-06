module
public import Causalean.Mathlib.MeasureTheory.FiniteIntervalPartition

/-! Re-exports the shared finite interval partition API used by this research run. -/

public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

export Causalean.Mathlib.MeasureTheory
  (IsIntervalPartition orderedHalfOpenIntervals_cover orderedIntervalCells_partition)

end CausalSmith.PartialID.UnlinkedPropensityAte
