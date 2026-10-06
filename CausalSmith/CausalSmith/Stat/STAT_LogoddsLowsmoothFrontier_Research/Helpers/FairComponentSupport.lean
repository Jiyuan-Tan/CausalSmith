module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ComponentPriorRestriction
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairProductDerivatives

/-! # Fair component bounds from calibrated record support

The support theorem's smoothness and derivative envelope discharge the actual
record inputs to the quadratic Taylor bound. Restricting the hidden sign prior
then transfers that bound to each original-record component.
-/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

attribute [local instance] Classical.propDecidable

/-- [Actual fair block likelihoods satisfy the quadratic Hellinger estimate
using the jointly selected support radius and derivative envelope. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ). Under [the stated assumptions](hyp:hk). -/
-- @node: fair_block_hellinger_from_support
lemma fair_block_hellinger_from_support {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (I : Finset (Fin n)) (t : ℝ) (o : Fin n → Record) (δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ calibEps) :
    (Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i ∈ I, recordCellDensity (fairLaw k σ t δ) (o i)) -
      Real.sqrt (∏ i ∈ I, recordCellDensity (fairComparator k t δ) (o i)))^2 ≤
        calibM^4 * (I.card : ℝ)^4 * 8^I.card * δ^4 := by
  apply fair_component_hellinger_of_record_derivatives k I t o δ calibM ht
    (hδ.trans calib_regularity_spec.1) calib_regularity_spec.2.1
  · intro b σ i hi z hz
    have hzsmall : |z| ≤ calibEps := by
      rw [abs_of_nonneg hz.1]
      exact hz.2.trans hδ
    exact calib_regularity_spec.2.2 k hk σ t z ht hzsmall b
      (o i).2.1 (o i).2.2 (o i).1
  · intro b σ i hi z hz m hm hm'
    have hzsmall : |z| ≤ calibEps := by
      rw [abs_of_nonneg hz.1]
      exact hz.2.trans hδ
    exact (((calib_constants_spec.2.2.2 k hk σ).2 t z ht hzsmall b).2
      (o i).2.1 (o i).2.2 (o i).1).2.2 m hm hm'

/-- [The uniform sign marginal on one component preserves the Taylor bound,
with the exact number of original records in that component. [the documented result](goal) Under [the stated assumptions](hyp:x,l,ht,hδ). Under [the stated assumptions](hyp:hk). -/
-- @node: fair_component_hellinger_from_support
lemma fair_component_hellinger_from_support {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (c : SignComponentBlock k x)
    (l : {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} → Bool × Bool)
    (t δ : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ calibEps) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (Real.sqrt ((Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i : {i : Fin n // block i = c},
          recordCellDensity (fairLaw k (componentSignExtension owner c σ) t δ) (x i.1,l i)) -
      Real.sqrt (∏ i : {i : Fin n // block i = c},
          recordCellDensity (fairComparator k t δ) (x i.1,l i)))^2 ≤
      calibM^4 * (Fintype.card {i : Fin n // block i = c} : ℝ)^4 *
        8^(Fintype.card {i : Fin n // block i = c}) * δ^4 := by
  classical
  dsimp only
  rw [← fairDensity_block_average_restrict k hk x c l t δ ht hδ]
  let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
  let I := Finset.univ.filter (fun i => block i = c)
  let o : Fin n → Record := fun i => (x i, if h : block i = c then l ⟨i,h⟩ else (false,false))
  have hp (P : ObservedLaw) : (∏ i ∈ I, recordCellDensity P (o i)) =
      ∏ i : {i : Fin n // block i = c}, recordCellDensity P (x i.1,l i) := by
    rw [Finset.prod_subtype (p := fun i => block i = c) I (by simp [I])]
    apply Finset.prod_congr rfl
    intro i _
    simp only [o, dif_pos i.2]
    rfl
  have hc : I.card = Fintype.card {i : Fin n // block i = c} := by
    rw [Fintype.card_subtype]
  have h := fair_block_hellinger_from_support k hk I t o δ ht hδ
  simp only [hp, hc] at h
  exact h

end CausalSmith.Stat.LogoddsLowsmoothFrontier
