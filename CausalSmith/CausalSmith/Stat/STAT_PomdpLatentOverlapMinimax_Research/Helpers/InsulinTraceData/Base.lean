module
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Basic

set_option linter.style.longLine false

/-! Exact rational trace data for the certified insulin-grid computation. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Causalean.Mathlib.Analysis.IntervalArithmetic
/-- For [the lo input](hyp:lo), [the hi input](hyp:hi), [this defines the insulin Interval From Endpoints object](goal). -/
def insulinIntervalFromEndpoints (lo hi : ℚ) : RatInterval :=
  ⟨min lo hi, max lo hi, min_le_max⟩

end CausalSmith.Stat.PomdpLatentOverlapMinimax
