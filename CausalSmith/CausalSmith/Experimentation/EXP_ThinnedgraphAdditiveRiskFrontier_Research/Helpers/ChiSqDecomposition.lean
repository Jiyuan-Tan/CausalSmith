module
public import Causalean.Stat.Minimax.ChiSquared
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.LikelihoodExpansion

/-!
# Conditional chi-squared decomposition interface
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Conditional chi-squared divergence against the actual assignment and independent reference
responses. -/
def hiddenChiSq (n B d : ℕ) (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (h : ℝ) (H : OffDiag (Fin n) → Bool) : ℝ :=
  Causalean.Stat.chiSqDiv (conditionalBlockLaw n B d D true h H) (hiddenReferenceLaw n B d D h)

/-- Conditional chi-squared divergence is nonnegative.  [For the stated data and conditions](hyp:n,B,d,D,h,H), [the stated conclusion holds](goal). -/
-- @node: hiddenChiSq_nonneg
lemma hiddenChiSq_nonneg (n B d : ℕ) (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (h : ℝ) (H : OffDiag (Fin n) → Bool) : 0 ≤ hiddenChiSq n B d D h H := by
  exact Causalean.Stat.chiSqDiv_nonneg

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
