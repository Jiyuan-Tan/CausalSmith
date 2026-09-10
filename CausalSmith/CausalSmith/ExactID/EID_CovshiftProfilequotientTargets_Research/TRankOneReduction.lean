import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.TSharpTargetFiber

/-! # Rank-one reduction -/

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

-- @node: prop:rank-one-reduction
theorem rank_one_reduction {d E : ℕ} (θ : CovarianceTuple d E)
    (hne : (causalTargetFiber θ 1).Nonempty) :
    causalTargetFiber θ 1 =
      {T | ∃ j : Fin d, T = {j} ∧ 0 < aggregateShift θ j j} := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets
