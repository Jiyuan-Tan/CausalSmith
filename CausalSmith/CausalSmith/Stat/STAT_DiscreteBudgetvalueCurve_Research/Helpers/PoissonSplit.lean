module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.Estimator

/-! Exact finite auxiliary weights for the capped Poisson split. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open scoped BigOperators NNReal

/-- The probability weight of one Poisson count, permutation, and marking. -/
noncomputable def auxiliaryWeight (n M : ℕ) : ℝ :=
  ((ProbabilityTheory.poissonMeasure ((n : ℝ≥0) / 4)) {M}).toReal /
    ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
      (Fintype.card (Fin n → Bool) : ℝ))

/-- Finite expectation over the nonzero cap-event outcomes. -/
noncomputable def auxiliaryAverage (n : ℕ)
    (f : ℕ → Equiv.Perm (Fin n) → (Fin n → Bool) → ℝ) : ℝ :=
  ∑ M ∈ Finset.range (n + 1),
    ∑ perm : Equiv.Perm (Fin n),
      ∑ marks : Fin n → Bool, auxiliaryWeight n M * f M perm marks

end CausalSmith.Stat.DiscreteBudgetvalueCurve
