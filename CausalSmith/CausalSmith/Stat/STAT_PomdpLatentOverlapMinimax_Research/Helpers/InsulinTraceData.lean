import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinTraceData.False10
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinTraceData.False11
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinTraceData.True10
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinTraceData.True11

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- For [the target input](hyp:target), [the k input](hyp:k), [the i input](hyp:i), [this defines the insulin Trace Interval object](goal). -/
def insulinTraceInterval (target : Bool) (k : Fin 2) (i : Fin 360) : RatInterval :=
  if k.val = 0 then
    if target then insulinTrueTraceRow10 i else insulinFalseTraceRow10 i
  else
    if target then insulinTrueTraceRow11 i else insulinFalseTraceRow11 i

end CausalSmith.Stat.PomdpLatentOverlapMinimax
