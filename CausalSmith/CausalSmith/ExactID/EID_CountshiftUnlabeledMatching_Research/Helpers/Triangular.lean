module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Basic
public import Causalean.Graph.DAG
public import Causalean.Graph.AcyclicConstruct

/-! Acyclic matrix support and total-effect inversion. -/

public section

open Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: acyclic_unit_matrix_invertible
lemma acyclic_unit_matrix_invertible {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ i, B i i = 1)
    (hacyclic : ∀ i, ¬ Relation.TransGen
      (fun j k => j ≠ k ∧ B k j ≠ 0) i i) : IsUnit B.det := by
  classical
  let e : Fin p → Fin p → Prop := fun j k => j ≠ k ∧ B k j ≠ 0
  let G := Causalean.Graph.DAG.ofAcyclic e hacyclic
  let rank : Fin p → ℕᵒᵈ ×ₗ Fin p := fun i => toLex (OrderDual.toDual (G.topoOrder i), i)
  have hrank : Function.Injective rank := by
    intro i j hij
    exact congrArg (fun x : ℕᵒᵈ ×ₗ Fin p => (ofLex x).2) hij
  let ord : LinearOrder (Fin p) := LinearOrder.lift' rank hrank
  have htri : @Matrix.IsUpperTriangular (Fin p) ℝ _ ord.toLT B := by
    intro i j hij
    by_contra hne
    have hedge : G.edge j i := by
      rw [Causalean.Graph.DAG.ofAcyclic_edge]
      constructor
      · intro hji
        subst j
        have hkey : rank i < rank i := by
          change rank i < rank i at hij
          exact hij
        exact (lt_irrefl (rank i)) hkey
      · exact hne
    have hlt := G.topoOrder_lt j i hedge
    have hle : G.topoOrder i ≤ G.topoOrder j := by
      have hkey : rank j < rank i := by
        change rank j < rank i at hij
        exact hij
      rcases (Prod.Lex.lt_iff.mp hkey) with h | h
      · exact Nat.le_of_lt h
      · exact le_of_eq h.1.symm
    exact (not_lt_of_ge hle) hlt
  have hdet : B.det = 1 := by
    rw [@Matrix.det_of_isUpperTriangular (Fin p) ℝ B _ _ _ ord htri]
    simp [hdiag]
  rw [hdet]
  exact isUnit_one

lemma acyclic_mechanism_totalEffect_diagonal {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : AcyclicMechanism A) :
    ∀ i, totalEffect A i i = 1 := by
  classical
  let e : Fin p → Fin p → Prop := fun j k => A k j ≠ 0
  let G := Causalean.Graph.DAG.ofAcyclic e hA.2
  let rank : Fin p → ℕᵒᵈ ×ₗ Fin p := fun i => toLex (OrderDual.toDual (G.topoOrder i), i)
  have hrank : Function.Injective rank := by
    intro i j hij
    exact congrArg (fun x : ℕᵒᵈ ×ₗ Fin p => (ofLex x).2) hij
  let ord : LinearOrder (Fin p) := LinearOrder.lift' rank hrank
  have htriA : @Matrix.IsUpperTriangular (Fin p) ℝ _ ord.toLT A := by
    intro i j hij
    by_contra hne
    have hedge : G.edge j i := by
      rw [Causalean.Graph.DAG.ofAcyclic_edge]
      exact hne
    have hlt := G.topoOrder_lt j i hedge
    have hle : G.topoOrder i ≤ G.topoOrder j := by
      have hkey : rank j < rank i := by
        change rank j < rank i at hij
        exact hij
      rcases (Prod.Lex.lt_iff.mp hkey) with h | h
      · exact Nat.le_of_lt h
      · exact le_of_eq h.1.symm
    exact (not_lt_of_ge hle) hlt
  let C : Matrix (Fin p) (Fin p) ℝ := 1 - A
  have htriC : @Matrix.IsUpperTriangular (Fin p) ℝ _ ord.toLT C := by
    intro i j hij
    have hne : i ≠ j := by
      intro h
      subst j
      have hkey : rank i < rank i := by
        change rank i < rank i at hij
        exact hij
      exact (lt_irrefl (rank i)) hkey
    simp [C, Matrix.sub_apply, hne, htriA hij]
  have hdiagC : ∀ i, C i i = 1 := by
    intro i
    simp [C, hA.1 i]
  have hdet : C.det = 1 := by
    rw [@Matrix.det_of_isUpperTriangular (Fin p) ℝ C _ _ _ ord htriC]
    simp [hdiagC]
  have hunit : IsUnit C.det := by rw [hdet]; exact isUnit_one
  letI : Invertible C := Matrix.invertibleOfIsUnitDet C hunit
  have htriInv : @Matrix.IsUpperTriangular (Fin p) ℝ _ ord.toLT C⁻¹ := by
    letI : LinearOrder (Fin p) := ord
    exact Matrix.blockTriangular_inv_of_blockTriangular htriC
  intro i
  have hmul := congrArg (fun B : Matrix (Fin p) (Fin p) ℝ => B i i)
    (Matrix.mul_nonsing_inv C hunit)
  have hsum : (C * C⁻¹) i i = C i i * C⁻¹ i i := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single i
    · intro k _ hki
      rcases @lt_trichotomy (Fin p) ord k i with h | h | h
      · simp [htriC h]
      · exact (hki h).elim
      · simp [htriInv h]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  change C⁻¹ i i = 1
  simpa [hsum, hdiagC] using hmul

/-- The off-diagonal support of a total-effect matrix follows the same
topological order as the structural coefficients. -/
-- @node: acyclic_mechanism_totalEffect_acyclic
lemma acyclic_mechanism_totalEffect_acyclic {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : AcyclicMechanism A) :
    ∀ i, ¬ Relation.TransGen
      (fun j k => j ≠ k ∧ totalEffect A k j ≠ 0) i i := by
  classical
  let e : Fin p → Fin p → Prop := fun j k => A k j ≠ 0
  let G := Causalean.Graph.DAG.ofAcyclic e hA.2
  let rank : Fin p → ℕᵒᵈ ×ₗ Fin p :=
    fun i => toLex (OrderDual.toDual (G.topoOrder i), i)
  have hrank : Function.Injective rank := by
    intro i j hij
    exact congrArg (fun x : ℕᵒᵈ ×ₗ Fin p => (ofLex x).2) hij
  let ord : LinearOrder (Fin p) := LinearOrder.lift' rank hrank
  have htriA : @Matrix.IsUpperTriangular (Fin p) ℝ _ ord.toLT A := by
    intro i j hij
    by_contra hne
    have hedge : G.edge j i := by
      rw [Causalean.Graph.DAG.ofAcyclic_edge]
      exact hne
    have hlt := G.topoOrder_lt j i hedge
    have hle : G.topoOrder i ≤ G.topoOrder j := by
      have hkey : rank j < rank i := by
        change rank j < rank i at hij
        exact hij
      rcases (Prod.Lex.lt_iff.mp hkey) with h | h
      · exact Nat.le_of_lt h
      · exact le_of_eq h.1.symm
    exact (not_lt_of_ge hle) hlt
  let C : Matrix (Fin p) (Fin p) ℝ := 1 - A
  have htriC : @Matrix.IsUpperTriangular (Fin p) ℝ _ ord.toLT C := by
    intro i j hij
    have hne : i ≠ j := by
      intro h
      subst j
      have hkey : rank i < rank i := by
        change rank i < rank i at hij
        exact hij
      exact (lt_irrefl (rank i)) hkey
    simp [C, Matrix.sub_apply, hne, htriA hij]
  have hdiagC : ∀ i, C i i = 1 := by
    intro i
    simp [C, hA.1 i]
  have hdet : C.det = 1 := by
    rw [@Matrix.det_of_isUpperTriangular (Fin p) ℝ C _ _ _ ord htriC]
    simp [hdiagC]
  have hunit : IsUnit C.det := by rw [hdet]; exact isUnit_one
  letI : Invertible C := Matrix.invertibleOfIsUnitDet C hunit
  have htriInv : @Matrix.IsUpperTriangular (Fin p) ℝ _ ord.toLT C⁻¹ := by
    letI : LinearOrder (Fin p) := ord
    exact Matrix.blockTriangular_inv_of_blockTriangular htriC
  have hedge : ∀ j k, j ≠ k → totalEffect A k j ≠ 0 → ord.lt k j := by
    intro j k hjk hnonzero
    rcases @lt_trichotomy (Fin p) ord j k with h | h | h
    · exact False.elim (hnonzero (htriInv h))
    · exact False.elim (hjk h)
    · exact h
  intro i hcycle
  have hpath : Relation.TransGen (fun j k => ord.lt k j) i i :=
    hcycle.lift id (by intro j k h; exact hedge j k h.1 h.2)
  letI : LinearOrder (Fin p) := ord
  have hstrict : ∀ {j k}, Relation.TransGen (fun a b => ord.lt b a) j k →
      ord.lt k j := by
    intro j k h
    induction h with
    | single h => exact h
    | tail h₁ h₂ ih => exact @lt_trans (Fin p) ord.toPreorder _ _ _ h₂ ih
  exact (@lt_irrefl (Fin p) ord.toPreorder i) (hstrict hpath)

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
