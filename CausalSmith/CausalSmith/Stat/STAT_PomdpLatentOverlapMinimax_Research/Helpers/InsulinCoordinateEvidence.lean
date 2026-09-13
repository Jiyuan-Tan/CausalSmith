import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinCoordinateEvidenceFalse
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinCoordinateEvidenceTrue

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- [the insulin Coordinate Checked assertion holds](goal). -/
theorem insulinCoordinateChecked (target : Bool) (j : Fin 360) :
    InsulinCoordinateChecked target j := by
  cases target
  · exact insulinFalse10CoordinateChecked j
  · exact insulinTrue10CoordinateChecked j

end CausalSmith.Stat.PomdpLatentOverlapMinimax
