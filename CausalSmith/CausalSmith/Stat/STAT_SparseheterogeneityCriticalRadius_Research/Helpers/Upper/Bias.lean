module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.BiasSummation

/-! Classifier-weighted bias step; the eventual proof expands the light and
heavy weights separately. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators

-- keep: existential audit theorem for the estimator's aggregate weight bias
lemma audit_weight_bias_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n M rho (P : KnownRadiusClass n M rho),
      3 ≤ n →
      (∑ k : Fin n, |upperAuditWeights n rho P.law k - P.law.cellMass k|) ≤
        C / degree n rho := by
  refine ⟨196612, by norm_num, ?_⟩
  intro n M rho P hn
  exact audit_weight_bias_bound_explicit rho P.law (by omega) P.overlap

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
