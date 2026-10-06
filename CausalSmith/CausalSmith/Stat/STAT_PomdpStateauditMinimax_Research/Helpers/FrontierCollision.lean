module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CollisionTV

/-! # Collision identities for the constant-path frontier witness. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory

-- @node: constantPath_cloneCollision_iff_coordinateCollision
/-- Along a constant base state path, the audited cloned states repeat exactly
when their clone coordinates repeat. -/
lemma constantPath_cloneCollision_iff_coordinateCollision {T n k m : Nat}
    (π : Fin n × Fin m ≃ Fin (n * m))
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (mask : AuditMask T) (s0 : JointState 1 n)
    (hconstant : ∀ t : Fin T, currentState w t = s0) :
    CloneCollision mask (clonePath π w coords) ↔
      ∃ t u : Fin T, t ≠ u ∧ mask t = true ∧ mask u = true ∧
        coords t.castSucc = coords u.castSucc := by
  constructor
  · exact cloneCollision_implies_coordinateCollision π w coords mask
  · rintro ⟨t, u, htu, ht, hu, hcoord⟩
    refine ⟨t, u, htu, ht, hu, ?_⟩
    change ((currentState w t).1, π ((currentState w t).2, coords t.castSucc)) =
      ((currentState w u).1, π ((currentState w u).2, coords u.castSucc))
    rw [hconstant t, hconstant u, hcoord]

-- @node: frontier_coordinateCollision_mass
/-- The fixed-permutation coupling gives the exact binomial mass to repeated
audited clone coordinates, independently of the base trajectory. -/
lemma frontier_coordinateCollision_mass {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m) (eta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    ((fixedPermutationCoupling (m := m) M eta)
      {q | ¬Function.Injective
        (fun t : auditedIndex q.2.2 => q.1.2 t.1.castSucc)}).toReal =
      collisionEnvelope T eta m := by
  rw [← coordinateMaskCollision_real hm eta heta]
  rw [← fixedPermutationCoupling_coordinateMask M hm eta heta]
  have hproj : Measurable (fun q : (FullPath T 1 n k ×
      (Fin (T + 1) → Fin m)) ×
      ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T) => (q.1.2, q.2.2)) := by
    fun_prop
  exact congrArg ENNReal.toReal ((Measure.map_apply hproj
    (MeasurableSet.of_discrete : MeasurableSet
      {q : (Fin (T + 1) → Fin m) × AuditMask T |
        ¬Function.Injective
          (fun t : auditedIndex q.2 => q.1 t.1.castSucc)})).symm)

end CausalSmith.Stat.PomdpStateauditMinimax
