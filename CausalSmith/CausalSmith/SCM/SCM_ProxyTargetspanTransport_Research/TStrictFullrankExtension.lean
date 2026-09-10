import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.TTargetSpanIff
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Witness
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.unusedDecidableInType false

/-! Strict extension beyond the published full-source-rank regime. -/

namespace CausalSmith.SCM.ProxyTargetspanTransport

variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]

-- @node: fullrank_implies_target_span
/-- Given [the positive latent-shift condition, the full-rank condition](hyp:hM,hrank), [full latent rank of the conditional proxy matrix implies that the target proxy vector lies in its column space](goal). -/
lemma fullrank_implies_target_span (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl) (x : X)
    (hrank : (condProxyMatrix Mdl x).rank = Fintype.card U) :
    (balancingFiber (condProxyMatrix Mdl x) (targetProxyVector Mdl)).Nonempty := by
  let y0 : Y := Classical.choice (Fintype.card_pos_iff.mp
    (lt_of_lt_of_le (by omega : 0 < 2) Mdl.outcome_card))
  have hfac := (observable_factorization Mdl hM x y0).1
  have hrankR : (latentPosterior Mdl x).rank = Fintype.card U := by
    apply Nat.le_antisymm
    · exact Matrix.rank_le_card_height _
    · rw [← hrank, hfac]
      exact Matrix.rank_mul_le_right _ _
  have hsurj : Function.Surjective (latentPosterior Mdl x).mulVec := by
    change Function.Surjective ⇑(latentPosterior Mdl x).mulVecLin
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_top, Module.finrank_pi_fintype]
    simpa [Matrix.rank] using hrankR
  obtain ⟨lam, hlam⟩ := hsurj Mdl.q
  refine ⟨lam, ?_⟩
  change (condProxyMatrix Mdl x).mulVec lam = targetProxyVector Mdl
  rw [hfac, ← Matrix.mulVec_mulVec, hlam]
  exact (observable_factorization Mdl hM x y0).2.1.symm

-- @node: fullrank_source_column_space_eq_proxy_column_space
/-- Given [the positive latent-shift condition, the full-rank condition](hyp:hM,hrank), [under full latent rank, the conditional proxy matrix and the proxy channel have the same column space](goal). -/
lemma fullrank_source_column_space_eq_proxy_column_space (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl) (x : X)
    (hrank : (condProxyMatrix Mdl x).rank = Fintype.card U) :
    {v : W → ℝ | ∃ lam : E → ℝ, (condProxyMatrix Mdl x).mulVec lam = v} =
      {v : W → ℝ | ∃ q : U → ℝ, Mdl.M.mulVec q = v} := by
  let y0 : Y := Classical.choice (Fintype.card_pos_iff.mp
    (lt_of_lt_of_le (by omega : 0 < 2) Mdl.outcome_card))
  have hfac := (observable_factorization Mdl hM x y0).1
  have hrankR : (latentPosterior Mdl x).rank = Fintype.card U := by
    apply Nat.le_antisymm
    · exact Matrix.rank_le_card_height _
    · rw [← hrank, hfac]
      exact Matrix.rank_mul_le_right _ _
  have hsurj : Function.Surjective (latentPosterior Mdl x).mulVec := by
    change Function.Surjective ⇑(latentPosterior Mdl x).mulVecLin
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_top, Module.finrank_pi_fintype]
    simpa [Matrix.rank] using hrankR
  ext v
  constructor
  · rintro ⟨lam, rfl⟩
    exact ⟨(latentPosterior Mdl x).mulVec lam, by rw [hfac, ← Matrix.mulVec_mulVec]⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨lam, hlam⟩ := hsurj q
    exact ⟨lam, by rw [hfac, ← Matrix.mulVec_mulVec, hlam]⟩

-- @node: prop:strict-fullrank-extension
/-- [the explicit rank-deficient witness proves that target-span identification strictly extends the full-source-rank regime](goal). -/
theorem strict_fullrank_extension :
    (∀ {E U W X Y : Type*}
      [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
      [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
      (Mdl : LatentShiftSCM E U W X Y), PositiveLatentShiftClass Mdl → ∀ x : X,
      (condProxyMatrix Mdl x).rank = Fintype.card U →
        {v : W → ℝ | ∃ lam : E → ℝ, (condProxyMatrix Mdl x).mulVec lam = v} =
          {v : W → ℝ | ∃ q : U → ℝ, Mdl.M.mulVec q = v} ∧
        (balancingFiber (condProxyMatrix Mdl x) (targetProxyVector Mdl)).Nonempty) ∧
    PositiveLatentShiftClass rankDeficientSuccessWitness ∧
    (∀ x : Fin 2, (condProxyMatrix rankDeficientSuccessWitness x).rank = 2) ∧
    (∀ x : Fin 2,
      (balancingFiber (condProxyMatrix rankDeficientSuccessWitness x)
        (targetProxyVector rankDeficientSuccessWitness)).Nonempty) ∧
    2 < Fintype.card (Fin 3) := by
  refine ⟨?_, rankDeficientSuccessWitness_positive,
    rankDeficientSuccessWitness_condProxy_rank,
    rankDeficientSuccessWitness_target_span, by decide⟩
  intro E U W X Y _ _ _ _ _ _ _ _ _ _ Mdl hM x hrank
  exact ⟨fullrank_source_column_space_eq_proxy_column_space Mdl hM x hrank,
    fullrank_implies_target_span Mdl hM x hrank⟩

end CausalSmith.SCM.ProxyTargetspanTransport
