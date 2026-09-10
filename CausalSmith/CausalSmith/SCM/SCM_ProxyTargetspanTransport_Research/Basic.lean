import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Fibers
import Causalean.PO.ID.Partial.Basic

set_option linter.unusedDecidableInType false

/-! Shared observable factorization for the finite latent-shift transport model. -/

open scoped BigOperators
open Finset Matrix

namespace CausalSmith.SCM.ProxyTargetspanTransport

variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]

-- @node: lem:observable-factorization
/-- Given [the positive latent-shift condition](hyp:hM), [the observable law factors through the conditional proxy matrix and the latent posterior matrix](goal). -/
lemma observable_factorization (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl) (x : X) (y : Y) :
    condProxyMatrix Mdl x = Mdl.M * latentPosterior Mdl x ∧
    targetProxyVector Mdl = Mdl.M.mulVec Mdl.q ∧
    condOutcomeVector Mdl x y = (latentPosterior Mdl x).vecMul (latentResponse Mdl x y) ∧
    interventionalProb Mdl x y = dotProduct (latentResponse Mdl x y) Mdl.q ∧
    (∀ lam (hlam : lam ∈ balancingFiber (condProxyMatrix Mdl x) (targetProxyVector Mdl)),
      (proxyMomentMatrix Mdl x).mulVec
          (unconditionalWeightMap (observedLaw Mdl) x
            (targetProxyVector Mdl) ⟨lam, hlam⟩) = targetProxyVector Mdl ∧
      dotProduct (outcomeMomentVector Mdl x y)
          (unconditionalWeightMap (observedLaw Mdl) x
            (targetProxyVector Mdl) ⟨lam, hlam⟩) = interventionalProb Mdl x y) ∧
    ∃ h : W → ℝ,
      (proxyMomentMatrix Mdl x).vecMul h = outcomeMomentVector Mdl x y := by
  haveI : Nonempty U := Fintype.card_pos_iff.mp
    (lt_of_lt_of_le (by omega : 0 < 2) Mdl.latent_card)
  have hrho : ∀ e, 0 < sourceTreatmentProb Mdl x e := by
    intro e
    exact Finset.sum_pos (fun u _ => mul_pos (hM.positivity.2.2.2.1 x u)
      (hM.positivity.2.1 u e)) Finset.univ_nonempty
  have hproxyJoint : ∀ e w,
      ∑ y', observedLaw Mdl e w x y' =
        Mdl.pi e * ∑ u, Mdl.M w u * Mdl.a x u * Mdl.S u e := by
    intro e w
    simp only [observedLaw]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    calc
      (∑ y', Mdl.PM e u w x y') =
          ∑ y', Mdl.pi e * Mdl.S u e * Mdl.M w u * Mdl.a x u *
            Mdl.f x y' u w := by
              apply Finset.sum_congr rfl
              intro y' _
              exact hM.factorization e u w x y'
      _ = Mdl.pi e * (Mdl.M w u * Mdl.a x u * Mdl.S u e) := by
        rw [← Finset.mul_sum, Mdl.f_col]
        ring
  have htreatmentJoint : ∀ e,
      ∑ w, ∑ y', observedLaw Mdl e w x y' =
        Mdl.pi e * sourceTreatmentProb Mdl x e := by
    intro e
    simp_rw [hproxyJoint]
    rw [← Finset.mul_sum]
    unfold sourceTreatmentProb
    rw [Finset.sum_comm]
    apply congrArg (Mdl.pi e * ·)
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_mul, ← Finset.sum_mul, Mdl.M_col]
    ring
  have houtcomeJoint : ∀ e,
      ∑ w, observedLaw Mdl e w x y =
        Mdl.pi e * ∑ u, Mdl.a x u * Mdl.S u e * latentResponse Mdl x y u := by
    intro e
    simp only [observedLaw]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    calc
      (∑ w, Mdl.PM e u w x y) =
          ∑ w, Mdl.pi e * Mdl.S u e * Mdl.M w u * Mdl.a x u *
            Mdl.f x y u w := by
              apply Finset.sum_congr rfl
              intro w _
              exact hM.factorization e u w x y
      _ = Mdl.pi e * (Mdl.a x u * Mdl.S u e * latentResponse Mdl x y u) := by
        unfold latentResponse
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
  have hB : condProxyMatrix Mdl x = Mdl.M * latentPosterior Mdl x := by
    ext w e
    simp only [condProxyMatrix, Matrix.mul_apply, latentPosterior]
    rw [hproxyJoint, htreatmentJoint]
    rw [mul_div_mul_left _ _ (ne_of_gt (hM.positivity.1 e))]
    rw [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hb : targetProxyVector Mdl = Mdl.M.mulVec Mdl.q := by
    ext w
    rfl
  have hc : condOutcomeVector Mdl x y =
      (latentPosterior Mdl x).vecMul (latentResponse Mdl x y) := by
    ext e
    simp only [condOutcomeVector, Matrix.vecMul, latentPosterior]
    rw [houtcomeJoint, htreatmentJoint]
    rw [mul_div_mul_left _ _ (ne_of_gt (hM.positivity.1 e))]
    rw [div_eq_mul_inv]
    unfold dotProduct
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have htheta : interventionalProb Mdl x y =
      dotProduct (latentResponse Mdl x y) Mdl.q := by
    unfold interventionalProb latentResponse dotProduct
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    ring
  refine ⟨hB, hb, hc, htheta, ?_, ?_⟩
  · intro lam hlam
    have hR : (latentPosterior Mdl x).mulVec lam = Mdl.q := by
      have hinj : Function.Injective Mdl.M.mulVec := by
        rw [Matrix.mulVec_injective_iff, linearIndependent_iff_card_eq_finrank_span]
        rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols]
        exact hM.proxy_injective.symm
      apply hinj
      rw [Matrix.mulVec_mulVec, ← hB, hlam, ← hb]
    constructor
    · ext w
      have hw := congrFun hlam w
      simp only [proxyMomentMatrix, Matrix.mulVec]
      change (∑ e, (∑ y, observedLaw Mdl e w x y) *
        (lam e / (∑ w', ∑ y, observedLaw Mdl e w' x y))) = _
      rw [← hw]
      simp only [condProxyMatrix, Matrix.mulVec]
      apply Finset.sum_congr rfl
      intro e _
      ring
    · simp only [outcomeMomentVector, unconditionalBalancingMoments,
        unconditionalWeightMap, dotProduct]
      rw [htheta, ← hR, Matrix.dotProduct_mulVec, ← hc]
      simp only [condOutcomeVector, Matrix.vecMul, dotProduct]
      apply Finset.sum_congr rfl
      intro e _
      ring
  · have hsurj : Function.Surjective Mdl.M.vecMul := by
      change Function.Surjective ⇑Mdl.M.vecMulLinear
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_of_le_of_finrank_eq le_top
      rw [finrank_top, Module.finrank_pi_fintype]
      rw [← Matrix.mulVecLin_transpose]
      simp only [Module.finrank_self, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      change Mdl.M.transpose.rank = Fintype.card U
      rw [Matrix.rank_transpose, hM.proxy_injective]
    obtain ⟨h, hh⟩ := hsurj (latentResponse Mdl x y)
    refine ⟨h, ?_⟩
    ext e
    simp only [proxyMomentMatrix, outcomeMomentVector,
      unconditionalBalancingMoments, Matrix.vecMul, dotProduct]
    simp_rw [hproxyJoint]
    rw [houtcomeJoint]
    change h ᵥ* Mdl.M = latentResponse Mdl x y at hh
    rw [← hh]
    unfold Matrix.vecMul dotProduct
    calc
      (∑ i, h i * (Mdl.pi e * ∑ u, Mdl.M i u * Mdl.a x u * Mdl.S u e)) =
          Mdl.pi e * ∑ i, ∑ u, h i * Mdl.M i u * Mdl.a x u * Mdl.S u e := by
            simp_rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro u _
            ring
      _ = Mdl.pi e * ∑ u, ∑ i, h i * Mdl.M i u * Mdl.a x u * Mdl.S u e := by
        rw [Finset.sum_comm]
      _ = Mdl.pi e * ∑ u, Mdl.a x u * Mdl.S u e * ∑ i, h i * Mdl.M i u := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro i _
        ring

end CausalSmith.SCM.ProxyTargetspanTransport
