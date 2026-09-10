import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.BlockScore
import Causalean.Experimentation.DesignBased.ProductVariance
import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization

/-! Uniform fourth-moment control for normalized block scores. -/

open scoped BigOperators

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open Causalean.Experimentation.DesignBased
open BoundedLagOnePartialInterferenceClass

def vecNormSq (x : Vec2) : ℝ := ∑ i, x i ^ 2

variable {Omega : Type*} [Fintype Omega]

-- @node: lem:block-moments
lemma block_fourth_moment_bound :
    ∀ (M KH eta : ℝ), 0 < M → 0 < KH → eta ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ C_R : ℝ, 0 ≤ C_R ∧
      ∀ (Omega : Type*) [Fintype Omega]
        (Mdl : BoundedLagOnePartialInterferenceClass Omega),
        Mdl.M = M → Mdl.KH = KH → Mdl.eta = eta →
        DesignBasedFiniteness (_hB := Mdl.B_pos) Mdl.x Mdl.Aassign
          Mdl.Y Mdl.realizedHistory Mdl.observed →
        (∀ w b, pathConditionalE (Mdl.referenceDesign w b) Mdl.x Mdl.Aassign b w
            (fun z ↦ vecNormSq (blockR Mdl z b) ^ 2) ≤ C_R) ∧
        (∀ w b, conditionalE Mdl b w (fun z ↦ vecNormSq (blockR Mdl z b) ^ 2) ≤
          C_R / eta) := by sorry

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
