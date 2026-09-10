import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.AronowSamiiBinary
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TQuarticSeparation

/-! Conservative-cone membership of the binary Aronow–Samii correction. -/

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- In [a finite binary experiment](hyp:E) with [positive singleton observation probabilities](hyp:hsingle) and [Horvitz–Thompson scores](hyp:hHT), [the binary Aronow–Samii correction is degree-two conservative with the stated excess formula; the concrete quartic witness is unrestricted-feasible but not degree-three observable, and its degree-three optimality gap is 1/24](goal). -/
-- @node: thm:aronow-samii-specialization
theorem asBinaryCorrection_mem_conservativeCone_two (E : Setup)
    (hsingle : ∀ i, 0 < jointObsProb E {i})
    (hHT : ∀ z i, E.v z i = (if i ∈ E.O z then 1 else 0) / jointObsProb E {i}) :
    asBinaryCorrection E hsingle hHT ∈ conservativeCone E 2 ∧
    (∀ θ, asBinaryCorrection E hsingle hHT θ - trueVarianceFn E θ =
      (1 / 2 : ℝ) * ∑ i, ∑ k,
        if i ≠ k ∧ jointObsProb E {i, k} = 0 then
          (((θ i : ℕ) : ℝ) + ((θ k : ℕ) : ℝ)) ^ 2 else 0) ∧
    bStar ∈ unrestrictedConservativeCone witnessExperiment ∧
    bStar ∉ observableSpan witnessExperiment 3 ∧
    optValue witnessExperiment witnessObjective 3 -
      optValue witnessExperiment witnessObjective ⊤ = 1 / 24 := by
  classical
  let u : Fin E.K → Fin E.K → Theta E → ℝ := fun i k θ =>
    varianceMatrix E i k * ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ) +
      if i ≠ k ∧ jointObsProb E {i, k} = 0 then
        (1 / 2 : ℝ) * ((((θ i : ℕ) : ℝ) + ((θ k : ℕ) : ℝ)) ^ 2) else 0
  have hu_mem (i k : Fin E.K) : u i k ∈ observableSpan E 2 := by
    by_cases hp : 0 < jointObsProb E {i, k}
    · have hobs : {i, k} ∈ observableComplex E :=
        observableComplex_of_jointObsProb_pos E {i, k} hp
      have heq : u i k = varianceMatrix E i k • monomial E {i, k} := by
        funext θ
        simp only [u, hp, ne_of_gt hp, and_false, if_false, add_zero, Pi.smul_apply,
          smul_eq_mul]
        by_cases hik : i = k
        · subst k
          have hi : (θ i : ℕ) = 0 ∨ (θ i : ℕ) = 1 := by omega
          rcases hi with hi | hi <;> simp [monomial, hi]
        · simp [monomial, hik]
          ring
      rw [heq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨{i, k}, hobs, by
        by_cases hik : i = k <;> simp [hik], rfl⟩)
    · have hnonneg : 0 ≤ jointObsProb E {i, k} := by
        unfold jointObsProb Causalean.Experimentation.DesignBased.FiniteDesign.E
        exact Finset.sum_nonneg fun z _ => mul_nonneg (E.design.p_nonneg z) (by positivity)
      have hz : jointObsProb E {i, k} = 0 := le_antisymm (not_lt.mp hp) hnonneg
      have hik : i ≠ k := by
        intro heq
        subst k
        have hs : jointObsProb E {i, i} = jointObsProb E {i} := by simp
        exact (ne_of_gt (hsingle i)) (hs ▸ hz)
      have hiobs : {i} ∈ observableComplex E :=
        observableComplex_of_jointObsProb_pos E {i} (hsingle i)
      have hkobs : {k} ∈ observableComplex E :=
        observableComplex_of_jointObsProb_pos E {k} (hsingle k)
      have heq : u i k =
          (1 / 2 : ℝ) • monomial E {i} + (1 / 2 : ℝ) • monomial E {k} := by
        funext θ
        dsimp [u]
        rw [ht_varianceMatrix_formula E hsingle hHT i k]
        simp only [hp, hz, hik, ne_eq, not_false_eq_true, and_self, if_true,
          zero_div, zero_sub, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have hi : ((θ i : ℕ) : ℝ) ^ 2 = ((θ i : ℕ) : ℝ) := by
          have hi' : (θ i : ℕ) = 0 ∨ (θ i : ℕ) = 1 := by omega
          rcases hi' with hi' | hi' <;> simp [hi']
        have hk : ((θ k : ℕ) : ℝ) ^ 2 = ((θ k : ℕ) : ℝ) := by
          have hk' : (θ k : ℕ) = 0 ∨ (θ k : ℕ) = 1 := by omega
          rcases hk' with hk' | hk' <;> simp [hk']
        simp [monomial]
        nlinarith [hi, hk]
      rw [heq]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨{i}, hiobs, by simp, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨{k}, hkobs, by simp, rfl⟩))
  have hrepr : asBinaryCorrection E hsingle hHT = ∑ i, ∑ k, u i k := by
    funext θ
    have hid := asBinaryCorrection_excess_identity E hsingle hHT θ
    unfold trueVarianceFn at hid
    rw [Finset.mul_sum] at hid
    simp_rw [Finset.mul_sum] at hid
    simp_rw [mul_ite, mul_zero] at hid
    simp only [Finset.sum_apply]
    dsimp [u]
    simp_rw [Finset.sum_add_distrib]
    linarith
  have hspan : asBinaryCorrection E hsingle hHT ∈ observableSpan E 2 := by
    rw [hrepr]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => hu_mem i k
  have hdom : ∀ θ, trueVarianceFn E θ ≤ asBinaryCorrection E hsingle hHT θ := by
    intro θ
    rw [← sub_nonneg]
    rw [asBinaryCorrection_excess_identity E hsingle hHT θ]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun k _ => by split <;> positivity)
  rcases witness_quartic_separation with
    ⟨hTop, _hTwo, hThree, _hGapTwo, hbStar, hbNot, _⟩
  refine ⟨⟨hspan, hdom⟩, asBinaryCorrection_excess_identity E hsingle hHT,
    hbStar, hbNot, ?_⟩
  rw [hThree, hTop]
  norm_num

end CausalSmith.Experimentation.BinaryTruthbound
