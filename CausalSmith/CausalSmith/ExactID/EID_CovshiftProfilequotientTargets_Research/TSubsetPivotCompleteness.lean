import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.PivotRecursion
import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.TSharpTargetFiber

/-! # Completeness and complexity of subset pivoting -/

open scoped BigOperators

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

/-- All subset states of depth at most `r`. -/
def visitedSubsetStates (d r : ℕ) : Finset (Finset (Fin d)) :=
  Finset.univ.filter fun S => S.card ≤ r

noncomputable def leafIntersection {d : ℕ} (L : Set (Finset (Fin d))) : Finset (Fin d) :=
  by classical exact Finset.univ.filter fun j => ∀ T, T ∈ L → j ∈ T

noncomputable def leafUnion {d : ℕ} (L : Set (Finset (Fin d))) : Finset (Fin d) :=
  by classical exact Finset.univ.filter fun j => ∃ T, T ∈ L ∧ j ∈ T

-- @node: thm:subset-pivot-completeness
theorem subset_pivot_completeness {d E r : ℕ} (θ : CovarianceTuple d E)
    (hd : 2 ≤ d) (hE : 2 ≤ E) (hr0 : 1 ≤ r) (hrd : r < d)
    (hBase : BaselinePositive θ) (hRank : AggregateExactRank θ r)
    (hRange : CommonShiftRange θ) :
    let R := subsetPivotRecursion (covarianceShift θ) (by simp [covarianceShift])
      (fun e ↦ (θ.symmetric e).sub (θ.symmetric 0)) r
    R.leaves = algebraicTargetFiber θ r ∧
    algebraicTargetFiber θ r = causalTargetFiber θ r ∧
    ∅ ∈ R.reachable ∧
    (∀ S R' Me', R.run S R' Me' →
      R' = R.residual S ∧ ∀ e, Me' e = R.environmentResidual e S) ∧
    (∀ S ∈ R.reachable, S.card ≤ r) ∧
    R.reachable.Finite ∧
    R.reachable.ncard ≤ ∑ k ∈ Finset.range (r + 1), Nat.choose d k ∧
    leafIntersection R.leaves = compulsoryLabels θ r ∧
    leafUnion R.leaves = possibleLabels θ r := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets
