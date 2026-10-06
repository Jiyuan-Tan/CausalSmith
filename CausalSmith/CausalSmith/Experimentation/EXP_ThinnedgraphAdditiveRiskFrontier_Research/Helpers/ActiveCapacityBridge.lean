module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ActualLabelSupportEnergy

/-!
# Masking inactive capacities in the actual conditional coefficient

An exact reindexing removes the unused slots outside a response support before
applying the active-slot contraction bound.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Only rows belonging to the response support retain hidden slots. -/
-- @node: activeCapacity
def activeCapacity (B : ℕ) (u : Fin B → ℕ) (T : Finset (Fin B)) : Fin B → ℕ :=
  fun ℓ => if ℓ ∈ T then u ℓ else 0

/-- Inactive rows have zero hidden degree in every compatible allocation.  [For the stated data and conditions](hyp:B,j,t,T,ht,ℓ,hℓ), [the stated conclusion holds](goal). -/
-- @node: allocationResponseSupport_degree_zero
lemma allocationResponseSupport_degree_zero (B : ℕ) (j t : Fin B → ℕ)
    (T : Finset (Fin B)) (ht : allocationResponseSupport B j t = T)
    (ℓ : Fin B) (hℓ : ℓ ∉ T) : t ℓ = 0 := by
  have hn : j ℓ + t ℓ = 0 := by
    have : ℓ ∉ allocationResponseSupport B j t := ht ▸ hℓ
    simpa [allocationResponseSupport] using this
  omega

/-- Masking inactive capacities preserves the full labeled support coefficient:
its allocations, total degrees, binomial weights and response factors agree.  [For the stated data and conditions](hyp:B,d,h,u,j,k,T,y), [the stated conclusion holds](goal). -/
-- @node: allocationSupportCoeff_activeCapacity
lemma allocationSupportCoeff_activeCapacity (B d : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) (k : ℕ) (T : Finset (Fin B)) (y : Fin B → ℝ) :
    allocationSupportCoeff B d h u j k T y =
      allocationSupportCoeff B d h (activeCapacity B u T) j k T y := by
  unfold allocationSupportCoeff
  let S := Finset.univ.filter (fun t : ∀ ℓ, Fin (u ℓ + 1) =>
    k = ∑ ℓ, (t ℓ).val ∧ allocationResponseSupport B j (fun ℓ => (t ℓ).val) = T)
  have hz (t : ∀ ℓ, Fin (u ℓ + 1)) (ht : t ∈ S) (ℓ : Fin B) (hℓ : ℓ ∉ T) :
      (t ℓ).val = 0 :=
    allocationResponseSupport_degree_zero B j _ T (Finset.mem_filter.mp ht).2.2 ℓ hℓ
  let shrink (t : ∀ ℓ, Fin (u ℓ + 1)) (ht : t ∈ S) :
      ∀ ℓ, Fin (activeCapacity B u T ℓ + 1) := fun ℓ =>
    ⟨(t ℓ).val, by
      by_cases hℓ : ℓ ∈ T
      · simpa [activeCapacity, hℓ] using (t ℓ).isLt
      · simp [activeCapacity, hℓ, hz t ht ℓ hℓ]⟩
  apply Finset.sum_bij shrink
  · intro t ht
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, shrink] using
      (Finset.mem_filter.mp ht).2
  · intro t ht v hv he
    funext ℓ
    apply Fin.ext
    exact congrArg (fun f => (f ℓ).val) he
  · intro v hv
    let t : ∀ ℓ, Fin (u ℓ + 1) := fun ℓ => ⟨(v ℓ).val, by
      have := (v ℓ).isLt
      have hm : activeCapacity B u T ℓ ≤ u ℓ := by
        unfold activeCapacity
        split_ifs <;> omega
      omega⟩
    have ht : t ∈ S := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, t] using
        (Finset.mem_filter.mp hv).2
    refine ⟨t, ht, ?_⟩
    funext ℓ
    apply Fin.ext
    rfl
  · intro t ht
    congr 1
    apply Finset.prod_congr rfl
    intro ℓ _
    by_cases hℓ : ℓ ∈ T
    · simp [activeCapacity, hℓ, shrink]
    · simp [activeCapacity, hℓ, shrink, hz t ht ℓ hℓ]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
