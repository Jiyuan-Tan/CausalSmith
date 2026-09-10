import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

/-!
# Minimum attainment on compact Euclidean sets

This module records the compact extreme-value theorem in the precise Euclidean form needed by the
robust backshift uniform-distance development.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

-- @node: lem:compact-extreme-value
/-- A [continuous function](hyp:hf) on a [nonempty compact Euclidean set](hyp:hS,hne)
[attains its minimum on that set](goal). -/
lemma compactExtremeValueMinimum_mathlib {d : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : IsCompact S) (hne : S.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContinuousOn f S) :
    ∃ x ∈ S, ∀ y ∈ S, f x ≤ f y := by
  obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn hne hf
  exact ⟨x, hx, fun _ hy ↦ hmin hy⟩

end CausalSmith.ExactID.RobustBackshiftUniformDistance
