import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinTraceData

/-! Data containers for bounded insulin-grid recurrence chunks. -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- The record collecting the data for Insulin Chunk Coordinate Data. -/
structure InsulinChunkCoordinateData where
  data : Array RatInterval
  size_eq : data.size = 9

/-- For [the row input](hyp:row), [the c input](hyp:c), [this defines the get object](goal). -/
def InsulinChunkCoordinateData.get (row : InsulinChunkCoordinateData)
    (c : Fin 9) : RatInterval :=
  row.data[c.val]'(by rw [row.size_eq]; exact c.isLt)

/-- The record collecting the data for Insulin Chunk Step Data. -/
structure InsulinChunkStepData where
  data : Array InsulinChunkCoordinateData
  size_eq : data.size = 360

/-- For [the step input](hyp:step), [the j input](hyp:j), [this defines the get object](goal). -/
def InsulinChunkStepData.get (step : InsulinChunkStepData)
    (j : Fin 360) : InsulinChunkCoordinateData :=
  step.data[j.val]'(by rw [step.size_eq]; exact j.isLt)

end CausalSmith.Stat.PomdpLatentOverlapMinimax
