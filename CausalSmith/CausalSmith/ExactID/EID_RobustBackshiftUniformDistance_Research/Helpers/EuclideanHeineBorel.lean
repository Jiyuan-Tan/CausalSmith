import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean Heine–Borel helper

This module supplies the paper-local compactness bridge from closedness and boundedness for
finite-dimensional Euclidean spaces.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

-- @node: lem:euclidean-heine-borel
/-- A [closed](hyp:hS_closed), [bounded](hyp:hS_bounded) subset of a finite-dimensional real
Euclidean space [is compact](goal). [Under the stated hypotheses](hyp:_hd) [this conclusion](goal) applies. -/
lemma euclideanHeineBorel_mathlib {d : ℕ} (_hd : 0 < d)
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S) : IsCompact S := by
  exact Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded

end CausalSmith.ExactID.RobustBackshiftUniformDistance
