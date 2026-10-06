module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.TPairedCapacityIdentity

/-! Fixed-sample paired-kernel reduction substrate for the lower proof. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

/-- The hard capacity-active subclass, including the binding requirement. -/
def capacityHardClass (d : ℕ) (epsilon : ℝ) : Set (PotentialLaw d) :=
  {Q | CausalModelClass epsilon Q ∧ budgetValue Q 1 = 1 / 2 ∧
    (∀ j, 0 < poCellMass Q j → effect Q j ∈ Set.Icc (1 / 8 : ℝ) (3 / 8)) ∧
    BindingHalfBudget Q}

end CausalSmith.Stat.DiscreteBudgetvalueCurve
