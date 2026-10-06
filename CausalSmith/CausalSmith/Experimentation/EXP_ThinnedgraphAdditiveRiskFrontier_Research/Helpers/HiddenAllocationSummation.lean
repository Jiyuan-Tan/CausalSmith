module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenAllocationEnergy

/-!
# Summing constrained allocation energies

Summing over the observed total hidden degree removes the degree constraint exactly.
The remaining nonnegative allocation energies factor over rows, including restrictions
requiring positive degree on hidden active rows. This supplies the degree-summation
step of the hidden-allocation contraction proof without assuming a posterior identity.
-/

public section

open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Each allocation contributes to exactly one total-degree fiber; summing all fibers
recovers its energy without an independence assumption on constrained row counts.  [For the stated data and conditions](hyp:B,M,u,S,F,hUM), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_degree_sum
lemma hidden_allocation_degree_sum (B M : ℕ) (u : Fin B → ℕ)
    (S : Finset (∀ ℓ, Fin (u ℓ + 1)))
    (F : (∀ ℓ, Fin (u ℓ + 1)) → ℝ) (hUM : (∑ ℓ, u ℓ) ≤ M) :
    (∑ k ∈ Finset.range (M + 1),
      ∑ t ∈ S.filter (fun t => k = ∑ ℓ, (t ℓ).val), F t) = ∑ t ∈ S, F t := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hdegree : (∑ ℓ, (t ℓ).val) < M + 1 := by
    have hle : (∑ ℓ, (t ℓ).val) ≤ ∑ ℓ, u ℓ :=
      Finset.sum_le_sum (fun ℓ _ => by have := (t ℓ).isLt; omega)
    omega
  simp [Finset.mem_range, hdegree]

/-- Independent row choices factor the unrestricted weighted gamma-energy sum.  [For the stated data and conditions](hyp:B,d,h,u,j), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_gamma_sum_factor
lemma hidden_allocation_gamma_sum_factor (B d : ℕ) (h : ℝ) (u j : Fin B → ℕ) :
    (∑ t : ∀ ℓ, Fin (u ℓ + 1),
      (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
        ∏ ℓ, gamma d h (j ℓ + (t ℓ).val)) =
      ∏ ℓ, ∑ k : Fin (u ℓ + 1),
        ((u ℓ).choose k.val : ℝ) * gamma d h (j ℓ + k.val) := by
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun ℓ (k : Fin (u ℓ + 1)) =>
    ((u ℓ).choose k.val : ℝ) * gamma d h (j ℓ + k.val))).symm

/-- Rowwise restrictions, such as positive degree on a hidden active row, preserve
factorization. They are imposed before summing rather than discarded by a bound.  [For the stated data and conditions](hyp:B,d,h,u,j,P), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_restricted_gamma_sum_factor
lemma hidden_allocation_restricted_gamma_sum_factor (B d : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) (P : ∀ ℓ, Fin (u ℓ + 1) → Prop) :
    (∑ t : ∀ ℓ, Fin (u ℓ + 1),
      if ∀ ℓ, P ℓ (t ℓ) then
        (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
          ∏ ℓ, gamma d h (j ℓ + (t ℓ).val) else 0) =
      ∏ ℓ, ∑ k : Fin (u ℓ + 1), if P ℓ k then
        ((u ℓ).choose k.val : ℝ) * gamma d h (j ℓ + k.val) else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : ∀ ℓ, P ℓ (t ℓ)
  · simp only [if_pos ht, if_pos (ht _), Finset.prod_mul_distrib]
  · rw [if_neg ht]
    push Not at ht
    obtain ⟨ℓ, hℓ⟩ := ht
    exact (Finset.prod_eq_zero (Finset.mem_univ ℓ) (by simp [hℓ])).symm

/-- Summing the good-event coefficient bound over every hidden degree gives one
contraction factor times the remaining allocation-energy sum. The minimum hidden
degree is supplied by the active-row restriction, not by independent hidden counts.  [For the stated data and conditions](hyp:B,d,M,a,b,h,u,j,S,hB,hd,hUM,hU,hgood,hmin), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_summed_walsh_energy_le
lemma hidden_allocation_summed_walsh_energy_le (B d M a b : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) (S : Finset (∀ ℓ, Fin (u ℓ + 1)))
    (hB : 0 < B) (hd : 0 < d) (hUM : (∑ ℓ, u ℓ) ≤ M)
    (hU : (∑ ℓ, u ℓ) ≤ d * (a + b))
    (hgood : (B * d : ℕ) / (4 : ℝ) ≤ M)
    (hmin : ∀ t ∈ S, b ≤ ∑ ℓ, (t ℓ).val) :
    (∑ k ∈ Finset.range (M + 1),
      (∫ y : Fin B → ℝ, (∑ t ∈ S.filter (fun t => k = ∑ ℓ, (t ℓ).val),
        (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
          ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ)) ^ 2
        ∂Measure.pi (fun _ : Fin B => volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w)))) / (M.choose k : ℝ)) ≤
      (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
        ∑ t ∈ S, (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
          ∏ ℓ, gamma d h (j ℓ + (t ℓ).val) := by
  classical
  calc
    _ ≤ ∑ k ∈ Finset.range (M + 1),
        (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
          ∑ t ∈ S.filter (fun t => k = ∑ ℓ, (t ℓ).val),
            (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
              ∏ ℓ, gamma d h (j ℓ + (t ℓ).val) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hbk : b ≤ k
      · exact hidden_allocation_walsh_energy_le B d M a b k h u j
          (S.filter (fun t => k = ∑ ℓ, (t ℓ).val)) hB hd hUM hU hgood hbk
          (fun t ht => (Finset.mem_filter.mp ht).2)
      · have hempty : S.filter (fun t => k = ∑ ℓ, (t ℓ).val) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t ht
          obtain ⟨htS, htdeg⟩ := Finset.mem_filter.mp ht
          exact hbk (htdeg ▸ hmin t htS)
        simp [hempty]
    _ = _ := by
      rw [← Finset.mul_sum, hidden_allocation_degree_sum B M u S _ hUM]

/-- Summing all total-degree coefficients with rowwise degree restrictions leaves
exactly the product of the restricted row energies. This combines the good-event
ratio estimate, weighted Cauchy–Schwarz, and independent response energies.  [For the stated data and conditions](hyp:B,d,M,a,b,h,u,j,P,hB,hd,hUM,hU,hgood,hmin), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_rowwise_summed_energy_le
lemma hidden_allocation_rowwise_summed_energy_le (B d M a b : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) (P : ∀ ℓ, Fin (u ℓ + 1) → Prop)
    (hB : 0 < B) (hd : 0 < d) (hUM : (∑ ℓ, u ℓ) ≤ M)
    (hU : (∑ ℓ, u ℓ) ≤ d * (a + b))
    (hgood : (B * d : ℕ) / (4 : ℝ) ≤ M)
    (hmin : ∀ t : ∀ ℓ, Fin (u ℓ + 1), (∀ ℓ, P ℓ (t ℓ)) →
      b ≤ ∑ ℓ, (t ℓ).val) :
    (∑ k ∈ Finset.range (M + 1),
      (∫ y : Fin B → ℝ,
        (∑ t ∈ Finset.univ.filter
          (fun t : ∀ ℓ, Fin (u ℓ + 1) => (∀ ℓ, P ℓ (t ℓ)) ∧
            k = ∑ ℓ, (t ℓ).val),
          (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
            ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ)) ^ 2
        ∂Measure.pi (fun _ : Fin B => volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w)))) / (M.choose k : ℝ)) ≤
      (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
        ∏ ℓ, ∑ t : Fin (u ℓ + 1), if P ℓ t then
          ((u ℓ).choose t.val : ℝ) * gamma d h (j ℓ + t.val) else 0 := by
  classical
  have hb := hidden_allocation_summed_walsh_energy_le B d M a b h u j
    (Finset.univ.filter (fun t => ∀ ℓ, P ℓ (t ℓ)))
    hB hd hUM hU hgood
    (fun t ht => hmin t (Finset.mem_filter.mp ht).2)
  simp only [Finset.filter_filter] at hb
  rw [Finset.sum_filter, hidden_allocation_restricted_gamma_sum_factor] at hb
  exact hb

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
