import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Witnesses
import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.InformationDistance
import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.TSharpTargetFiber

/-! # Four-node profile collision and local rate -/

open scoped ENNReal

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

/-- The three compatible targets away from the collision. -/
def offCollisionFiber : Set (Finset (Fin 4)) :=
  {T | T = {0, 1} ∨ T = {0, 2} ∨ T = {0, 3}}

/-- All six two-element targets at the collision. -/
def atCollisionFiber : Set (Finset (Fin 4)) := {T | T.card = 2}

-- @node: prop:four-node-collision
theorem four_node_collision (m M : ℝ) (hm : 0 < m) (hM : m < M) :
    (∀ γ : CollisionParameter, γ.1 ≠ 0 →
      causalTargetFiber (fourNodeCollisionPath γ) 2 = offCollisionFiber ∧
      completeClassification (fourNodeCollisionPath γ) 2 =
        ({0}, Finset.univ)) ∧
    causalTargetFiber (fourNodeCollisionPath collisionZero) 2 = atCollisionFiber ∧
    completeClassification (fourNodeCollisionPath collisionZero) 2 =
      (∅, Finset.univ) ∧
    ((∃ γ0 : ℝ, 0 < γ0 ∧ ∀ γ : CollisionParameter, |γ.1| ≤ γ0 →
        fourNodeCollisionPath γ ∈ ThetaK 4 2 2 m M) →
      ∃ c C : ℝ, 0 < c ∧ c < C ∧
        ∃ γ1 : ℝ, 0 < γ1 ∧ ∀ γ : CollisionParameter,
          0 < |γ.1| → |γ.1| ≤ γ1 → ∀ N : ℕ,
          ENNReal.ofReal (c * Real.sqrt N * |γ.1|) ≤
            classificationInformationDistance m M (fun _ => N)
              (fourNodeCollisionPath γ) 2 ∧
          classificationInformationDistance m M (fun _ => N)
              (fourNodeCollisionPath γ) 2 ≤
            ENNReal.ofReal (C * Real.sqrt N * |γ.1|)) := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets
