import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Basic
import Causalean.Experimentation.DesignBased.ProductReindex
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! A finite carrier for the perfect-matching representation of balanced signs. -/

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open Causalean.Experimentation.DesignBased

abbrev FixedPointFreeMatching (G : ℕ) :=
  {mate : Fin G → Fin G // Function.Involutive mate ∧ ∀ g, mate g ≠ g}

abbrev OrientedPerfectMatching (G : ℕ) :=
  {mo : FixedPointFreeMatching G × (Fin G → Bool) //
    ∀ g, mo.2 (mo.1.1 g) = !mo.2 g}

-- @node: def:perfect-matching-handle
noncomputable def perfectMatchingHandle (G : ℕ) : Type := by
  classical
  exact {H : FiniteDesign (OrientedPerfectMatching G) ×
      (OrientedPerfectMatching G → BalancedSignAssignment G) //
    (∀ mo, H.1.p mo = (Fintype.card (OrientedPerfectMatching G) : ℝ)⁻¹) ∧
    (∀ S, H.1.Pr (fun mo ↦ H.2 mo = S) =
      (Nat.choose G (G / 2) : ℝ)⁻¹) ∧
    (∀ mo g, balancedSign (H.2 mo) g = mo.1.2 g)}

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
