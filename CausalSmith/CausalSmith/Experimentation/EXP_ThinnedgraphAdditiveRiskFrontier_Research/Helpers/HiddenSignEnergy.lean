module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenAllocationOrthogonality
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.SymmetricSignPolys

/-!
# Joint revealed and hidden sign energies

The exact hidden-sign normalization survives adjoining the independent revealed
signs. Finite likelihood expansions therefore have squared norms weighted by
inverse binomial coefficients, without treating hidden row counts as independent.
-/

public section

open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

/-- Independent revealed monomials and symmetric hidden polynomials are mutually
orthogonal, with the exact inverse-binomial hidden normalization.  [For the stated data and conditions](hyp:R,M,k,t,S,T,hk,ht), [the stated conclusion holds](goal). -/
-- @node: hidden_revealed_sign_orthogonality
lemma hidden_revealed_sign_orthogonality (R M k t : ℕ)
    (S T : Finset (Fin R)) (hk : k ≤ M) (ht : t ≤ M) :
    (∫ x : (Fin R → Bool) × (Fin M → Bool),
      ((∏ j ∈ S, signOf (x.1 j)) * symmetricSignPoly M k x.2) *
        ((∏ j ∈ T, signOf (x.1 j)) * symmetricSignPoly M t x.2)
      ∂(halfBernoulli (Fin R)).prod (halfBernoulli (Fin M))) =
      if S = T ∧ k = t then (M.choose k : ℝ)⁻¹ else 0 := by
  classical
  have he (x : (Fin R → Bool) × (Fin M → Bool)) :
      ((∏ j ∈ S, signOf (x.1 j)) * symmetricSignPoly M k x.2) *
        ((∏ j ∈ T, signOf (x.1 j)) * symmetricSignPoly M t x.2) =
      ((∏ j ∈ S, signOf (x.1 j)) * (∏ j ∈ T, signOf (x.1 j))) *
        (symmetricSignPoly M k x.2 * symmetricSignPoly M t x.2) := by ring
  simp_rw [he]
  rw [integral_prod_mul
    (fun z : Fin R → Bool => (∏ j ∈ S, signOf (z j)) * ∏ j ∈ T, signOf (z j))
    (fun z : Fin M → Bool => symmetricSignPoly M k z * symmetricSignPoly M t z),
    signProduct_orthogonality,
    symmetricSignPoly_orthogonality M k t hk ht]
  by_cases hS : S = T <;> by_cases hkt : k = t <;> simp [hS, hkt]

/-- Every joint sign cross product is integrable: the entire observed sign space
is finite and its reference measure is a probability law.  [For the stated data and conditions](hyp:R,M,S,T,k,t), [the stated conclusion holds](goal). -/
-- @node: hidden_revealed_sign_cross_integrable
lemma hidden_revealed_sign_cross_integrable (R M : ℕ)
    (S T : Finset (Fin R)) (k t : ℕ) :
    Integrable (fun x : (Fin R → Bool) × (Fin M → Bool) =>
      ((∏ j ∈ S, signOf (x.1 j)) * symmetricSignPoly M k x.2) *
        ((∏ j ∈ T, signOf (x.1 j)) * symmetricSignPoly M t x.2))
      ((halfBernoulli (Fin R)).prod (halfBernoulli (Fin M))) := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  let : IsProbabilityMeasure (halfBernoulli (Fin R)) := by
    unfold halfBernoulli; infer_instance
  let : IsProbabilityMeasure (halfBernoulli (Fin M)) := by
    unfold halfBernoulli; infer_instance
  exact Integrable.of_finite

/-- A finite expansion indexed by distinct revealed subsets and hidden degrees has
exact squared norm equal to the inverse-binomial weighted coefficient energy.  [For the stated data and conditions](hyp:R,M,G,c), [the stated conclusion holds](goal). -/
-- @node: hidden_revealed_sign_expansion_energy
lemma hidden_revealed_sign_expansion_energy (R M : ℕ)
    (G : Finset (Finset (Fin R) × Fin (M + 1)))
    (c : (Finset (Fin R) × Fin (M + 1)) → ℝ) :
    (∫ x : (Fin R → Bool) × (Fin M → Bool),
      (∑ i ∈ G, c i * ((∏ j ∈ i.1, signOf (x.1 j)) *
        symmetricSignPoly M i.2.val x.2)) ^ 2
      ∂(halfBernoulli (Fin R)).prod (halfBernoulli (Fin M))) =
      ∑ i ∈ G, c i ^ 2 / (M.choose i.2.val : ℝ) := by
  classical
  have he (i j : Finset (Fin R) × Fin (M + 1))
      (x : (Fin R → Bool) × (Fin M → Bool)) :
      (c i * ((∏ a ∈ i.1, signOf (x.1 a)) * symmetricSignPoly M i.2.val x.2)) *
        (c j * ((∏ a ∈ j.1, signOf (x.1 a)) * symmetricSignPoly M j.2.val x.2)) =
      (c i * c j) *
        (((∏ a ∈ i.1, signOf (x.1 a)) * symmetricSignPoly M i.2.val x.2) *
          ((∏ a ∈ j.1, signOf (x.1 a)) * symmetricSignPoly M j.2.val x.2)) := by ring
  rw [hidden_orthogonal_sum_energy]
  · apply Finset.sum_congr rfl
    intro i hi
    simp_rw [pow_two, he]
    rw [integral_const_mul,
      hidden_revealed_sign_orthogonality R M i.2.val i.2.val i.1 i.1
        (by omega) (by omega)]
    simp [div_eq_mul_inv]
  · intro i hi j hj
    simp_rw [he]
    exact (hidden_revealed_sign_cross_integrable R M i.1 j.1 i.2.val j.2.val).const_mul _
  · intro i hi j hj hij
    simp_rw [he]
    rw [integral_const_mul,
      hidden_revealed_sign_orthogonality R M i.2.val j.2.val i.1 j.1
        (by omega) (by omega)]
    have hn : ¬ (i.1 = j.1 ∧ i.2.val = j.2.val) := by
      rintro ⟨h₁, h₂⟩
      exact hij (Prod.ext h₁ (Fin.ext h₂))
    rw [if_neg hn, mul_zero]

/-- For square-integrable response coefficients, the full joint sign-response
expansion has the exact coefficient-norm decomposition used in chi-squared.
The response coefficients may mix positive degrees within each row.  [For the stated data and conditions](hyp:Ω,ν,R,M,G,c,hc), [the stated conclusion holds](goal). -/
-- @node: hidden_revealed_response_expansion_energy
lemma hidden_revealed_response_expansion_energy {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (R M : ℕ)
    (G : Finset (Finset (Fin R) × Fin (M + 1)))
    (c : (Finset (Fin R) × Fin (M + 1)) → Ω → ℝ)
    (hc : ∀ i ∈ G, ∀ j ∈ G, Integrable (fun y => c i y * c j y) ν) :
    (∫ p : ((Fin R → Bool) × (Fin M → Bool)) × Ω,
      (∑ i ∈ G, ((∏ j ∈ i.1, signOf (p.1.1 j)) *
        symmetricSignPoly M i.2.val p.1.2) * c i p.2) ^ 2
      ∂((halfBernoulli (Fin R)).prod (halfBernoulli (Fin M))).prod ν) =
      ∑ i ∈ G, (∫ y, c i y ^ 2 ∂ν) / (M.choose i.2.val : ℝ) := by
  classical
  let b := fun (i : Finset (Fin R) × Fin (M + 1))
    (x : (Fin R → Bool) × (Fin M → Bool)) =>
      (∏ j ∈ i.1, signOf (x.1 j)) * symmetricSignPoly M i.2.val x.2
  have hi (i j : Finset (Fin R) × Fin (M + 1)) :
      Integrable (fun x => b i x * b j x)
        ((halfBernoulli (Fin R)).prod (halfBernoulli (Fin M))) :=
    hidden_revealed_sign_cross_integrable R M i.1 j.1 i.2.val j.2.val
  have ho (i j : Finset (Fin R) × Fin (M + 1)) :
      (∫ x, b i x * b j x
        ∂(halfBernoulli (Fin R)).prod (halfBernoulli (Fin M))) =
      if i.1 = j.1 ∧ i.2.val = j.2.val then (M.choose i.2.val : ℝ)⁻¹ else 0 :=
    hidden_revealed_sign_orthogonality R M i.2.val j.2.val i.1 j.1
      (by omega) (by omega)
  have he (i j : Finset (Fin R) × Fin (M + 1))
      (p : ((Fin R → Bool) × (Fin M → Bool)) × Ω) :
      (b i p.1 * c i p.2) * (b j p.1 * c j p.2) =
        (b i p.1 * b j p.1) * (c i p.2 * c j p.2) := by ring
  change (∫ p : ((Fin R → Bool) × (Fin M → Bool)) × Ω,
    (∑ i ∈ G, b i p.1 * c i p.2) ^ 2 ∂_) = _
  rw [hidden_orthogonal_sum_energy]
  · apply Finset.sum_congr rfl
    intro i hiG
    simp_rw [pow_two, he]
    rw [integral_prod_mul (fun x => b i x * b i x)
      (fun y => c i y * c i y), ho]
    simp only [and_self, ite_true]
    simp only [div_eq_mul_inv, mul_comm]
  · intro i hiG j hjG
    simp_rw [he]
    exact (hi i j).mul_prod (hc i hiG j hjG)
  · intro i hiG j hjG hij
    simp_rw [he]
    rw [integral_prod_mul (fun x => b i x * b j x)
      (fun y => c i y * c j y), ho]
    have hn : ¬ (i.1 = j.1 ∧ i.2.val = j.2.val) := by
      rintro ⟨h₁, h₂⟩
      exact hij (Prod.ext h₁ (Fin.ext h₂))
    rw [if_neg hn, zero_mul]

/-- The degree-zero symmetric hidden polynomial is exactly the constant one,
including the endpoint with no hidden labels.  [For the stated data and conditions](hyp:M,z), [the stated conclusion holds](goal). -/
-- @node: symmetricSignPoly_zero
lemma symmetricSignPoly_zero (M : ℕ) (z : Fin M → Bool) :
    symmetricSignPoly M 0 z = 1 := by
  simp [symmetricSignPoly]

/-- Removing the constant likelihood term gives precisely the nonconstant
coefficient energy, with its exact inverse-binomial factors.  [For the stated data and conditions](hyp:Ω,ν,R,M,G,c,hzero,hc0,hc), [the stated conclusion holds](goal). -/
-- @node: hidden_revealed_response_nonconstant_energy
lemma hidden_revealed_response_nonconstant_energy {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (R M : ℕ)
    (G : Finset (Finset (Fin R) × Fin (M + 1)))
    (c : (Finset (Fin R) × Fin (M + 1)) → Ω → ℝ)
    (hzero : (∅, 0) ∈ G) (hc0 : ∀ y, c (∅, 0) y = 1)
    (hc : ∀ i ∈ G, ∀ j ∈ G, Integrable (fun y => c i y * c j y) ν) :
    (∫ p : ((Fin R → Bool) × (Fin M → Bool)) × Ω,
      ((∑ i ∈ G, ((∏ j ∈ i.1, signOf (p.1.1 j)) *
        symmetricSignPoly M i.2.val p.1.2) * c i p.2) - 1) ^ 2
      ∂((halfBernoulli (Fin R)).prod (halfBernoulli (Fin M))).prod ν) =
      ∑ i ∈ G.erase (∅, 0), (∫ y, c i y ^ 2 ∂ν) / (M.choose i.2.val : ℝ) := by
  classical
  have he (p : ((Fin R → Bool) × (Fin M → Bool)) × Ω) :
      (∑ i ∈ G, ((∏ j ∈ i.1, signOf (p.1.1 j)) *
        symmetricSignPoly M i.2.val p.1.2) * c i p.2) - 1 =
      ∑ i ∈ G.erase (∅, 0), ((∏ j ∈ i.1, signOf (p.1.1 j)) *
        symmetricSignPoly M i.2.val p.1.2) * c i p.2 := by
    have hs := Finset.sum_erase_add G
      (fun i : Finset (Fin R) × Fin (M + 1) =>
        ((∏ j ∈ i.1, signOf (p.1.1 j)) *
          symmetricSignPoly M i.2.val p.1.2) * c i p.2) hzero
    simp only [Finset.prod_empty, Fin.val_zero, symmetricSignPoly_zero, hc0,
      one_mul] at hs
    linarith
  simp_rw [he]
  exact hidden_revealed_response_expansion_energy ν R M (G.erase (∅, 0)) c
    (fun i hi j hj => hc i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj))

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
