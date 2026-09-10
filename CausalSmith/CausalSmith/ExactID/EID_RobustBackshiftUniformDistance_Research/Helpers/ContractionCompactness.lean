import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.CitedGates
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ConfidenceUnion
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.OverlapUniqueness

/-!
# Compactness and the global residual gap

The non-effective contraction proof packages candidate feasibility, compactifies the finite union
of constraint families, and obtains a positive minimum residual on its far subfamily.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set

/-- The sole candidate-side quantitative assumption: every exactly feasible candidate has the
prescribed condition-number bound. -/
def CandidateConditionBound {p m c : ℕ} (C : Environment m → Set (RealMatrix p))
    (kappabar : ℝ) : Prop :=
  ∀ (K : Finset (Environment m)), K.card = honestCount m c →
    ∀ (A : RealMatrix p), A ∈ admissibleSet p →
      ∀ (Psi : RealMatrix p), Psi.PosSemidef →
        ∀ (t : Environment m → Fin p → ℝ), (∀ e ∈ K, ∀ j, 0 ≤ t e j) →
          ∀ (Gamma : Environment m → RealMatrix p),
            (∀ e ∈ K, Gamma e ∈ C e) →
            (∀ e ∈ K,
              A * Gamma e * A.transpose = Psi + Matrix.diagonal (t e)) →
            matrixConditionNumber A ≤ kappabar

end CausalSmith.ExactID.RobustBackshiftUniformDistance
