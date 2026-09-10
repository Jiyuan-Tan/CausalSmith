import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.Duality
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.Witness32
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T3_Complete32Certificate

set_option linter.unusedDecidableInType false

/-! # Optimal-face characterization of strict label refinement -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open Set

variable {O T OBlind : Type*} [Fintype O] [Fintype T] [Fintype OBlind]
  [DecidableEq O] [DecidableEq T] [DecidableEq OBlind]

/-- Strict improvement is equivalent to exclusion of every blind-embedded
optimizer; the lower and upper conditions have their explicit linear-system
forms, the strict region is relatively open, and every bracketed design has a
nonempty relative-interior strict region. -/
-- @node: thm:general-dual-face-strict-refinement-characterization
theorem general_dual_face_strict_refinement_characterization
    (G : SLCCIncidence O T OBlind) :
    (∀ p ∈ observablePolytope G,
      ((blindEndpointPrograms G p).1 < lowerEndpoint G p ↔
        lowerOptimalFace G p ∩ embeddedBlindDual G = ∅) ∧
      (upperEndpoint G p < (blindEndpointPrograms G p).2 ↔
        upperOptimalFace G p ∩ embeddedBlindDual G = ∅) ∧
      ((blindEndpointPrograms G p).1 < lowerEndpoint G p ↔
        ¬ ∃ alpha : ℝ, ∃ lambda : O → ℝ, ∃ nu : OBlind → ℝ,
          (∀ t, alpha + ∑ o, G.B o t * lambda o ≤ G.h t) ∧
          (∀ o, lambda o = ∑ b, G.K b o * nu b) ∧
          alpha + ∑ o, lambda o * p o = lowerEndpoint G p) ∧
      (upperEndpoint G p < (blindEndpointPrograms G p).2 ↔
        ¬ ∃ alpha : ℝ, ∃ lambda : O → ℝ, ∃ nu : OBlind → ℝ,
          (∀ t, G.h t ≤ alpha + ∑ o, G.B o t * lambda o) ∧
          (∀ o, lambda o = ∑ b, G.K b o * nu b) ∧
          alpha + ∑ o, lambda o * p o = upperEndpoint G p)) ∧
    (∃ U : Set (O → ℝ), IsOpen U ∧
      strictRefinementRegion G = U ∩ observablePolytope G) ∧
    (∀ d : SLCCDesign, BracketSLCC d →
      (strictRefinementRegion (designGeometry d) ∩
        intrinsicInterior ℝ (observablePolytope (designGeometry d))).Nonempty ∧
      ∃ U : Set (ObservableCell d → ℝ), U.Nonempty ∧ IsOpen U ∧
        U ∩ observablePolytope (designGeometry d) ⊆
          strictRefinementRegion (designGeometry d)) := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
