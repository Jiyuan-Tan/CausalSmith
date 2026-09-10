import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Basic

/-!
# Determinant envelope from cycle normalization

This file bounds determinant monomials by decomposing their permutations into disjoint cycles.
It supplies both the closed cycle-product boundary used in compactness arguments and the strict
admissible-set specialization.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open scoped BigOperators

noncomputable section

/-- Every absolute Leibniz monomial of a unit-diagonal matrix is at most one when its
cycle product is at most one. [Under the stated hypotheses](hyp:hdiag,hcycle) [this conclusion](goal) applies. -/
lemma permutationMonomial_abs_le_one_of_cycleProduct {p : ℕ} (A : RealMatrix p)
    (hdiag : ∀ i, A i i = 1) (hcycle : cycleProduct (1 - A) ≤ 1)
    (σ : Equiv.Perm (Fin p)) :
    ∏ i, |A (σ i) i| ≤ 1 := by
  classical
  let τ : Equiv.Perm (Fin p) := σ⁻¹
  have hreindex : (∏ i, |A (σ i) i|) = ∏ i, |A i (τ i)| := by
    have h := Equiv.prod_comp σ (fun i : Fin p ↦ |A i (τ i)|)
    simpa [τ] using h
  rw [hreindex]
  have hsupport : τ.support =
      τ.cycleFactorsFinset.biUnion (fun c ↦ c.support) := by
    ext i
    simp only [Finset.mem_biUnion]
    exact Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset
  have hrestrict : (∏ i, |A i (τ i)|) = ∏ i ∈ τ.support, |A i (τ i)| := by
    symm
    apply Finset.prod_subset (Finset.subset_univ τ.support)
    intro i _ hi
    have hitau : τ i = i := Equiv.Perm.notMem_support.mp hi
    simp [hitau, hdiag]
  rw [hrestrict, hsupport]
  have hpair : (τ.cycleFactorsFinset : Set (Equiv.Perm (Fin p))).PairwiseDisjoint
      (fun c ↦ c.support) := by
    intro c hc d hd hcd
    exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint τ hc hd hcd).disjoint_support
  rw [Finset.prod_biUnion hpair]
  apply Finset.prod_le_one
  · intro c hc
    exact Finset.prod_nonneg fun _ _ ↦ abs_nonneg _
  · intro c hc
    have hcdata := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc
    have hcweight : (∏ i ∈ c.support, |A i (τ i)|) =
        simpleCycleWeight (1 - A) c := by
      unfold simpleCycleWeight
      rw [if_pos ⟨hcdata.1, hcdata.1.two_le_card_support⟩]
      apply Finset.prod_congr rfl
      intro i hi
      rw [← hcdata.2 i hi]
      have hne : i ≠ c i := (Equiv.Perm.mem_support.mp hi).symm
      simp [Matrix.sub_apply, hne]
    rw [hcweight]
    have hall := (Finset.fold_max_le
      (s := (Finset.univ : Finset (Equiv.Perm (Fin p))))
      (b := (0 : ℝ)) (f := simpleCycleWeight (1 - A)) (c := 1)).mp hcycle
    exact hall.2 c (Finset.mem_univ c)

/-- A unit-diagonal matrix on the closed cycle-product boundary has determinant absolute value
at most the number of coordinate permutations. [Under the stated hypotheses](hyp:hdiag,hcycle) [this conclusion](goal) applies. -/
lemma abs_det_le_factorial_of_cycleProduct {p : ℕ} (A : RealMatrix p)
    (hdiag : ∀ i, A i i = 1) (hcycle : cycleProduct (1 - A) ≤ 1) :
    |A.det| ≤ (Nat.factorial p : ℝ) := by
  classical
  rw [Matrix.det_apply]
  calc
    |∑ σ : Equiv.Perm (Fin p), Equiv.Perm.sign σ • ∏ i, A (σ i) i| ≤
        ∑ σ : Equiv.Perm (Fin p),
          |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin p), ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Units.smul_def, zsmul_eq_mul, abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs,
        Int.cast_one, one_mul, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin p), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro σ _
      exact permutationMonomial_abs_le_one_of_cycleProduct A hdiag hcycle σ
    _ = (Nat.factorial p : ℝ) := by
      simp [Fintype.card_perm, Fintype.card_fin]

/-- Every BACKSHIFT-admissible matrix has determinant absolute value at most `p!`. [Under the stated hypotheses](hyp:hA) [this conclusion](goal) applies. -/
lemma abs_det_le_factorial_of_mem_admissibleSet {p : ℕ} {A : RealMatrix p}
    (hA : A ∈ admissibleSet p) :
    |A.det| ≤ (Nat.factorial p : ℝ) := by
  exact abs_det_le_factorial_of_cycleProduct A hA.2.1 (le_of_lt hA.2.2)

end

end CausalSmith.ExactID.RobustBackshiftUniformDistance
