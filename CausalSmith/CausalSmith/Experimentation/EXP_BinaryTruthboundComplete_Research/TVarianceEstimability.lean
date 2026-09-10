import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TObservableMobius

/-! Exact design-estimability criterion for the true variance. -/

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- For [an experiment](hyp:E), [the true-variance function is the sum of pairwise monomials weighted by the variance matrix](goal). -/
-- @node: trueVarianceFn_monomial_expansion
lemma trueVarianceFn_monomial_expansion (E : Setup) : trueVarianceFn E =
    ∑ i, ∑ k, varianceMatrix E i k • monomial E {i, k} := by
  funext θ
  simp only [trueVarianceFn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [show monomial E {i, k} θ = ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ) by
    by_cases h : i = k
    · subst k
      have hv : (θ i).val = 0 ∨ (θ i).val = 1 := by omega
      rcases hv with hv | hv <;> simp [monomial, hv]
    · simp [monomial, h]]
  ring

/-- For [an experiment](hyp:E), [a finite index type](hyp:α), [a family of Boolean functions](hyp:u), and [a coordinate set](hyp:S), [the Möbius coefficient of the finite sum is the sum of the individual Möbius coefficients](goal). -/
-- @node: beta_fintype_sum
lemma beta_fintype_sum (E : Setup) {α : Type*} [Fintype α] (u : α → Theta E → ℝ)
    (S : Finset (Fin E.K)) :
    beta E (∑ T, u T) S = ∑ T, beta E (u T) S := by
  simp only [beta, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- For [an experiment](hyp:E) and [two distinct coordinates](hyp:i,k,hik), [the pairwise Möbius coefficient of true variance is the sum of the two transposed variance-matrix entries](goal). -/
-- @node: beta_trueVarianceFn_pair
lemma beta_trueVarianceFn_pair (E : Setup) (i k : Fin E.K) (hik : i ≠ k) :
    beta E (trueVarianceFn E) {i, k} =
      varianceMatrix E i k + varianceMatrix E k i := by
  classical
  rw [trueVarianceFn_monomial_expansion, beta_fintype_sum]
  simp_rw [beta_fintype_sum, beta_smul, beta_monomial]
  simp only [mul_ite, mul_one, mul_zero]
  have hp (a b : Fin E.K) :
      ({i, k} : Finset (Fin E.K)) = {a, b} ↔
        (a = i ∧ b = k) ∨ (a = k ∧ b = i) := by
    constructor
    · intro h
      have hi : i = a ∨ i = b := by
        have : i ∈ ({a, b} : Finset (Fin E.K)) := by rw [← h]; simp
        simpa [eq_comm] using this
      have hk : k = a ∨ k = b := by
        have : k ∈ ({a, b} : Finset (Fin E.K)) := by rw [← h]; simp
        simpa [eq_comm] using this
      rcases hi with hi | hi <;> rcases hk with hk | hk
      · exact (hik (hi.trans hk.symm)).elim
      · exact Or.inl ⟨hi.symm, hk.symm⟩
      · exact Or.inr ⟨hk.symm, hi.symm⟩
      · exact (hik (hi.trans hk.symm)).elim
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [Finset.pair_comm]
  simp_rw [hp]
  calc
    (∑ a, ∑ b, if a = i ∧ b = k ∨ a = k ∧ b = i
        then varianceMatrix E a b else 0) =
        ∑ a, ((if a = i then varianceMatrix E i k else 0) +
          if a = k then varianceMatrix E k i else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hai : a = i
      · subst a
        simp [hik]
      · by_cases hak : a = k
        · subst a
          simp [hai]
        · simp [hai, hak]
    _ = varianceMatrix E i k + varianceMatrix E k i := by
      rw [Finset.sum_add_distrib]
      change (∑ a ∈ Finset.univ, if a = i then varianceMatrix E i k else 0) +
        (∑ a ∈ Finset.univ, if a = k then varianceMatrix E k i else 0) = _
      rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp

/-- In [an experiment](hyp:E) with [observable scores](hyp:hobs), if [two coordinates](hyp:i,k) [are never jointly observed](hyp:hn), then [their variance-matrix entry is the negative product of their target coefficients](goal). -/
-- @node: varianceMatrix_eq_neg_target_mul_of_not_joint
lemma varianceMatrix_eq_neg_target_mul_of_not_joint (E : Setup) (hobs : ObservableScore E)
    (i k : Fin E.K) (hn : ∀ z, ¬ ({i, k} : Finset (Fin E.K)) ⊆ E.O z) :
    varianceMatrix E i k = -(targetCoeff E i * targetCoeff E k) := by
  have hvprod : ∀ z, E.v z i * E.v z k = 0 := by
    intro z
    by_cases hi : E.v z i = 0
    · simp [hi]
    · have hiO := hobs z i hi
      have hk : E.v z k = 0 := by
        by_contra hk
        apply hn z
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · exact hx ▸ hiO
        · exact hx ▸ hobs z k hk
      simp [hk]
  unfold varianceMatrix
  have he : E.design.E (fun z => E.v z i * E.v z k) = 0 := by
    unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
    simp_rw [hvprod]
    simp
  rw [he]
  ring

/-- For [an experiment and two coordinates](hyp:E,i,k), [the variance matrix is symmetric at those coordinates](goal). -/
-- @node: varianceMatrix_comm
lemma varianceMatrix_comm (E : Setup) (i k : Fin E.K) :
    varianceMatrix E i k = varianceMatrix E k i := by
  unfold varianceMatrix targetCoeff Causalean.Experimentation.DesignBased.FiniteDesign.E
  congr 1
  · apply Finset.sum_congr rfl
    intro z hz
    ring
  · ring

/-- In [an experiment](hyp:E) with [observable scores](hyp:hobs), [the true design variance has an
unbiased assignment-rule estimator exactly when it lies in the observable span; equivalently, every
never-jointly-observed distinct pair has zero product of target coefficients](goal). -/
-- @node: prop:variance-estimability
theorem designVariance_estimable_iff (E : Setup) (hobs : ObservableScore E) :
    ((∃ g : AssignmentRule E, expectedRule E g = trueVarianceFn E) ↔
      trueVarianceFn E ∈ observableSpan E ⊤) ∧
    (trueVarianceFn E ∈ observableSpan E ⊤ ↔
      ∀ (i k : Fin E.K), i ≠ k →
        (∀ z, ¬ ({i, k} : Finset (Fin E.K)) ⊆ E.O z) →
        targetCoeff E i * targetCoeff E k = 0) := by
  classical
  constructor
  · exact (expectedRule_mem_observableSpan_iff E).1 (trueVarianceFn E) |>.1
  · constructor
    · intro hf i k hik hn
      have hncomplex : ({i, k} : Finset (Fin E.K)) ∉ observableComplex E := by
        intro hmem
        rcases (Finset.mem_filter.mp hmem).2 with ⟨z, hz⟩
        exact hn z hz
      have hbeta := (observableSpan_iff_beta_vanishes E (trueVarianceFn E)).mp hf
        {i, k} hncomplex
      rw [beta_trueVarianceFn_pair E i k hik,
        ← varianceMatrix_comm E i k,
        varianceMatrix_eq_neg_target_mul_of_not_joint E hobs i k hn] at hbeta
      linarith
    · intro hc
      rw [trueVarianceFn_monomial_expansion]
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.sum_mem
      intro k hk
      by_cases hik : i = k
      · subst k
        rw [show ({i, i} : Finset (Fin E.K)) = {i} by ext; simp]
        by_cases hseen : ∃ z, i ∈ E.O z
        · apply Submodule.smul_mem
          apply Submodule.subset_span
          rcases hseen with ⟨z, hz⟩
          refine ⟨{i}, ?_, by simp, rfl⟩
          unfold observableComplex
          simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.subset_univ _, z, by simpa using hz⟩
        · have hv : ∀ z, E.v z i = 0 := by
            intro z
            by_contra hv
            exact hseen ⟨z, hobs z i hv⟩
          have hvm : varianceMatrix E i i = 0 := by
            unfold varianceMatrix targetCoeff
            unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
            simp_rw [hv]
            simp
          rw [hvm, zero_smul]
          exact (observableSpan E ⊤).zero_mem
      · by_cases hjoint : ∃ z, ({i, k} : Finset (Fin E.K)) ⊆ E.O z
        · apply Submodule.smul_mem
          apply Submodule.subset_span
          rcases hjoint with ⟨z, hz⟩
          refine ⟨{i, k}, ?_, by simp, rfl⟩
          unfold observableComplex
          simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.subset_univ _, z, hz⟩
        · have hn : ∀ z, ¬ ({i, k} : Finset (Fin E.K)) ⊆ E.O z := by
            simpa only [not_exists] using hjoint
          rw [varianceMatrix_eq_neg_target_mul_of_not_joint E hobs i k hn,
            hc i k hik hn]
          simp

end CausalSmith.Experimentation.BinaryTruthbound
