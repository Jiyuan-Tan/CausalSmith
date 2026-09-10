import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T4_DualFaceStrictRefinement

/-! # A relatively open region of two-sided strict refinement -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open Set

/-- The perturbed rational law lies in a nonempty relatively open subset of
the relative interior on which both full-data endpoints strictly improve. -/
-- @node: thm:relative-open-strict-refinement
theorem relative_open_strict_refinement :
    ∃ U : Set (Fin 12 → ℝ),
      U.Nonempty ∧ witness32Law witness32PiCirc ∈ U ∧
      U ⊆ intrinsicInterior ℝ (observablePolytope witness32Geometry) ∧
      (∃ V : Set (Fin 12 → ℝ), IsOpen V ∧
        U = V ∩ intrinsicInterior ℝ (observablePolytope witness32Geometry)) ∧
      ∀ p ∈ U,
        (blindEndpointPrograms witness32Geometry p).1 < lowerEndpoint witness32Geometry p ∧
        upperEndpoint witness32Geometry p < (blindEndpointPrograms witness32Geometry p).2 := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
