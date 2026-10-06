module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.DenseLower
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.TwoSampleL1Splice

/-! Sparse, dense, and finite-alphabet lower-bound splice. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

/-- The matched lower-rate scale. -/
noncomputable def curveRate (n d : ℕ) : ℝ :=
  min 1 ((d : ℝ) / (n * logAlphabet d))

end CausalSmith.Stat.DiscreteBudgetvalueCurve
