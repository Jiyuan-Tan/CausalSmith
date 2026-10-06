module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.FKExpectation

/-! Algebraic core of the conditional centered-numerator mean. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

/-- Equation (16) after substituting the conditional means of the two outcome
sums.  This is the exact algebraic prerequisite for the probabilistic
conditional-expectation statement. -/
-- keep: paper equation (16) as a standalone algebraic audit identity
lemma centeredNumerator_mean_identity {n : ℕ} (P : Law n) (k : Fin n)
    (t : ℝ) (N0 N1 : ℕ) :
    (N0 : ℝ) * ((N1 : ℝ) * P.outcomeMean true k) -
        (N1 : ℝ) * ((N0 : ℝ) * P.outcomeMean false k) -
        t * (N0 : ℝ) * (N1 : ℝ) =
      (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) := by
  unfold DiscreteAteHeterogeneityFrontier.cellEffect
  ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
