import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.TPositiveNoiseRealization
import Causalean.Mathlib.LinearAlgebra.Cholesky

/-! # Sharp target-fiber theorem -/

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

-- @node: thm:sharp-target-fiber
theorem sharp_target_fiber {d E r : ℕ} (θ : CovarianceTuple d E)
    (hd : 2 ≤ d) (hE : 2 ≤ E) (hr0 : 1 ≤ r) (hrd : r < d)
    (hBase : BaselinePositive θ) (hRank : AggregateExactRank θ r)
    (hRange : CommonShiftRange θ)
    (hNonnegative : ∀ M : CovShiftModel d E r,
      LegalCovShiftModel M → NonnegativeVarianceShifts M) :
    causalTargetFiber θ r = algebraicTargetFiber θ r := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets
