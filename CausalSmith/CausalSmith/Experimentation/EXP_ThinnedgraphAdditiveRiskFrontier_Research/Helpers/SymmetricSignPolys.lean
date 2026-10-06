module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.DesignBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.WalshChannelEnergy

/-!
# Symmetric hidden-sign polynomials
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Symmetric sign polynomial on a Boolean slice. -/
def symmetricSignPoly (M k : ℕ) (z : Fin M → Bool) : ℝ :=
  (M.choose k : ℝ)⁻¹ * ∑ E ∈ Finset.univ.powersetCard k, ∏ j ∈ E, signOf (z j)

/-- Products of independent centered signs form an orthonormal family.  [For the stated data and conditions](hyp:V,S,T), [the stated conclusion holds](goal). -/
-- @node: signProduct_orthogonality
lemma signProduct_orthogonality {V : Type*} [Fintype V] [DecidableEq V]
    (S T : Finset V) :
    (∫ z, (∏ j ∈ S, signOf (z j)) * (∏ j ∈ T, signOf (z j))
      ∂(halfBernoulli V)) = if S = T then 1 else 0 := by
  open Causalean.Experimentation.DesignBased in
  have hscale (R : Finset V) (z : Assign V) :
      (∏ j ∈ R, signOf (z j)) =
        (2 : ℝ) ^ R.card * centeredMonomial (fun _ => (1 / 2 : ℝ)) R z := by
    unfold centeredMonomial
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    cases h : z j <;> norm_num [signOf, treatInd, h]
  rw [integral_halfBernoulli_eq_bernoulliDesign_E]
  simp_rw [hscale]
  have hfun : (fun z : Assign V =>
      ((2 : ℝ) ^ S.card * Causalean.Experimentation.DesignBased.centeredMonomial
        (fun _ => (1 / 2 : ℝ)) S z) *
      ((2 : ℝ) ^ T.card * Causalean.Experimentation.DesignBased.centeredMonomial
        (fun _ => (1 / 2 : ℝ)) T z)) =
      (fun z => ((2 : ℝ) ^ S.card * 2 ^ T.card) *
        (Causalean.Experimentation.DesignBased.centeredMonomial
          (fun _ => (1 / 2 : ℝ)) S z *
         Causalean.Experimentation.DesignBased.centeredMonomial
          (fun _ => (1 / 2 : ℝ)) T z)) := by funext z; ring
  rw [hfun, Causalean.Experimentation.DesignBased.FiniteDesign.E_const_mul,
    Causalean.Experimentation.DesignBased.bernoulliDesign_E_centeredMonomial_mul]
  by_cases hST : S = T
  · subst T
    simp only [Finset.prod_const]
    norm_num
    rw [← mul_pow, ← mul_pow]
    norm_num
  · simp [hST]

/-- [When both polynomial degrees do not exceed the ambient dimension](hyp:hk,ht), [their Bernoulli inner product is the reciprocal binomial coefficient when the degrees agree and zero otherwise](goal). -/
-- @node: symmetricSignPoly_orthogonality
lemma symmetricSignPoly_orthogonality (M k t : ℕ) (hk : k ≤ M) (ht : t ≤ M) :
    (∫ z, symmetricSignPoly M k z * symmetricSignPoly M t z ∂(halfBernoulli (Fin M))) =
      if k = t then (M.choose k : ℝ)⁻¹ else 0 := by
  rw [integral_halfBernoulli_eq_bernoulliDesign_E]
  unfold symmetricSignPoly
  have hfun : (fun z : Assign (Fin M) =>
      ((M.choose k : ℝ)⁻¹ * ∑ E ∈ Finset.univ.powersetCard k, ∏ j ∈ E, signOf (z j)) *
      ((M.choose t : ℝ)⁻¹ * ∑ F ∈ Finset.univ.powersetCard t, ∏ j ∈ F, signOf (z j))) =
      (fun z => ((M.choose k : ℝ)⁻¹ * (M.choose t : ℝ)⁻¹) *
        ∑ E ∈ Finset.univ.powersetCard k, ∑ F ∈ Finset.univ.powersetCard t,
          (∏ j ∈ E, signOf (z j)) * (∏ j ∈ F, signOf (z j))) := by
    funext z
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hfun, Causalean.Experimentation.DesignBased.FiniteDesign.E_const_mul]
  simp only [Causalean.Experimentation.DesignBased.FiniteDesign.E_sum]
  simp_rw [← integral_halfBernoulli_eq_bernoulliDesign_E, signProduct_orthogonality]
  by_cases hkt : k = t
  · subst t
    have hnonzero : (M.choose k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hk))
    simp only [ite_true]
    have hsum : (∑ E ∈ (Finset.univ : Finset (Fin M)).powersetCard k,
        ∑ F ∈ (Finset.univ : Finset (Fin M)).powersetCard k,
          if E = F then (1 : ℝ) else 0) = M.choose k := by
      calc
        _ = ∑ E ∈ (Finset.univ : Finset (Fin M)).powersetCard k, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro E hE
          simp [hE]
        _ = M.choose k := by simp [Finset.card_powersetCard]
    rw [hsum]
    field_simp
  · rw [if_neg hkt]
    have hsum : (∑ E ∈ (Finset.univ : Finset (Fin M)).powersetCard k,
        ∑ F ∈ (Finset.univ : Finset (Fin M)).powersetCard t,
          if E = F then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro F hF
      have hEF : E ≠ F := by
        intro heq
        have hEk := (Finset.mem_powersetCard.mp hE).2
        have hFt := (Finset.mem_powersetCard.mp hF).2
        exact hkt (hEk.symm.trans (heq ▸ hFt))
      exact if_neg hEF
    rw [hsum, mul_zero]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
