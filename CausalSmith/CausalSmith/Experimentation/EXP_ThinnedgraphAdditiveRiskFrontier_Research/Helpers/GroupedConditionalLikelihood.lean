module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.SymmetricConditionalLikelihood

/-!
# Total-hidden-degree coefficients of the actual conditional likelihood

Regroup the exact labeled posterior expansion by total hidden degree. The
coefficient fibers keep all row capacities and binomial slot multiplicities.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Every admissible row degree vector has total degree at most the number of
hidden labels, without any assumption of independent row treatments.  [For the stated data and conditions](hyp:n,B,d,H,k,hk), [the stated conclusion holds](goal). -/
-- @node: hiddenRowDegree_total_le
lemma hiddenRowDegree_total_le (n B d : ℕ) (H : OffDiag (Fin n) → Bool)
    (k : Fin B → ℕ)
    (hk : k ∈ Fintype.piFinset
      (fun ℓ : Fin B => Finset.range (capacity n B d H ℓ + 1))) :
    (∑ ℓ, k ℓ) ≤ undiscovered n B d H := by
  apply Finset.sum_le_sum
  intro ℓ _
  have := Finset.mem_range.mp (Fintype.mem_piFinset.mp hk ℓ)
  omega

/-- The response coefficient for a revealed-subset family and a total hidden
degree, with the exact capacity-constrained binomial multiplicities. -/
-- @node: groupedHiddenWalshCoeff
def groupedHiddenWalshCoeff (n B d : ℕ) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (J : Fin B → Finset (Fin n)) (t : ℕ) (y : Fin B → ℝ) : ℝ :=
  ∑ k ∈ (Fintype.piFinset
    (fun ℓ : Fin B => Finset.range (capacity n B d H ℓ + 1))).filter
      (fun k => t = ∑ ℓ, k ℓ),
    (∏ ℓ, (Nat.choose (capacity n B d H ℓ) (k ℓ) : ℝ)) *
      ∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)

/-- The same actual coefficient indexed by bounded row degrees, exactly matching
 the allocation-energy lemmas' finite domain.  [For the stated data and conditions](hyp:n,B,d,h,H,J,t,y), [the stated conclusion holds](goal). -/
-- @node: groupedHiddenWalshCoeff_eq_bounded
lemma groupedHiddenWalshCoeff_eq_bounded (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (J : Fin B → Finset (Fin n))
    (t : ℕ) (y : Fin B → ℝ) :
    groupedHiddenWalshCoeff n B d h H J t y =
      ∑ k ∈ Finset.univ.filter
        (fun k : ∀ ℓ : Fin B, Fin (capacity n B d H ℓ + 1) =>
          t = ∑ ℓ, (k ℓ).val),
        (∏ ℓ, (Nat.choose (capacity n B d H ℓ) (k ℓ).val : ℝ)) *
          ∏ ℓ, walshCoeff d h ((J ℓ).card + (k ℓ).val) (y ℓ) := by
  unfold groupedHiddenWalshCoeff
  symm
  apply Finset.sum_bij (fun k _ ℓ => (k ℓ).val)
  · intro k hk
    refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hk).2⟩
    exact Fintype.mem_piFinset.mpr (fun ℓ => Finset.mem_range.mpr (k ℓ).isLt)
  · intro a ha b hb hab
    funext ℓ
    exact Fin.ext (congrFun hab ℓ)
  · intro k hk
    have hbound (ℓ : Fin B) : k ℓ < capacity n B d H ℓ + 1 :=
      Finset.mem_range.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hk).1 ℓ)
    refine ⟨fun ℓ => ⟨k ℓ, hbound ℓ⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2⟩
  · intro k hk
    rfl

/-- Regrouping row allocations gives exactly one symmetric sign polynomial per
total hidden degree; no row allocation weight is dropped.  [For the stated data and conditions](hyp:n,B,d,h,H,J,y,x), [the stated conclusion holds](goal). -/
-- @node: hiddenWalsh_row_sum_eq_degree_sum
lemma hiddenWalsh_row_sum_eq_degree_sum (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (J : Fin B → Finset (Fin n))
    (y : Fin B → ℝ) (x : Fin (undiscovered n B d H) → Bool) :
    (∑ k ∈ Fintype.piFinset
      (fun ℓ : Fin B => Finset.range (capacity n B d H ℓ + 1)),
      (∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)) *
        ((∏ ℓ, (Nat.choose (capacity n B d H ℓ) (k ℓ) : ℝ)) *
          symmetricSignPoly (undiscovered n B d H) (∑ ℓ, k ℓ) x)) =
    ∑ t ∈ Finset.range (undiscovered n B d H + 1),
      symmetricSignPoly (undiscovered n B d H) t x *
        groupedHiddenWalshCoeff n B d h H J t y := by
  simp only [groupedHiddenWalshCoeff, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have ht : (∑ ℓ, k ℓ) ∈ Finset.range (undiscovered n B d H + 1) :=
    Finset.mem_range.mpr (by have := hiddenRowDegree_total_le n B d H k hk; omega)
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', ht, if_true]
  ring

/-- The actual likelihood on positive reference support, now indexed by revealed
monomials and total hidden degree as in the nonconstant energy decomposition.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,z,s₀,y,hy), [the stated conclusion holds](goal). -/
-- @node: blockDensity_grouped_hidden_walsh_expansion
lemma blockDensity_grouped_hidden_walsh_expansion (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ)) :
    blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) =
      ∑ J ∈ Fintype.piFinset
        (fun ℓ : Fin B => (revealedSources n B d H ℓ).powerset),
        (∏ ℓ, ∏ j ∈ J ℓ, signOf (z j)) *
          ∑ t ∈ Finset.range (undiscovered n B d H + 1),
            symmetricSignPoly (undiscovered n B d H) t
              (fun i => z (hiddenSourceLabelEmbedding n B d hfit H
                ((hiddenSourceEnumeration n B d hfit H s₀).symm i))) *
              groupedHiddenWalshCoeff n B d h H J t y := by
  rw [blockDensity_symmetric_hidden_selection_expansion n B d hd hfit h H z s₀ y hy]
  simp_rw [hiddenWalsh_row_sum_eq_degree_sum]

/-- The grouped likelihood density keeps the actual labels and the reference-zero
extension while making the hidden-degree coefficient fibers explicit. -/
-- @node: groupedHiddenWalshDensity
def groupedHiddenWalshDensity (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) : ℝ :=
  if hs : Nonempty (CompatiblePartition n B d hz.1) then
    if ∀ ℓ, 0 < refDensity d h (y ℓ) then
      (∏ ℓ, refDensity d h (y ℓ)) *
        (∑ J ∈ Fintype.piFinset
          (fun ℓ : Fin B => (revealedSources n B d hz.1 ℓ).powerset),
          (∏ ℓ, ∏ j ∈ J ℓ, signOf (hz.2 j)) *
            ∑ t ∈ Finset.range (undiscovered n B d hz.1 + 1),
              symmetricSignPoly (undiscovered n B d hz.1) t
                (fun i => hz.2 (hiddenSourceLabelEmbedding n B d hfit hz.1
                  ((hiddenSourceEnumeration n B d hfit hz.1 hs.some).symm i))) *
                groupedHiddenWalshCoeff n B d h hz.1 J t y)
    else 0
  else 0

/-- Regrouping preserves the entire posterior density, including incompatible
graphs and zero reference-density endpoints.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,hz,y), [the stated conclusion holds](goal). -/
-- @node: symmetricHiddenWalshDensity_eq_grouped
lemma symmetricHiddenWalshDensity_eq_grouped (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) :
    symmetricHiddenWalshDensity n B d hfit h hz y =
      groupedHiddenWalshDensity n B d hfit h hz y := by
  by_cases hs : Nonempty (CompatiblePartition n B d hz.1)
  · have hH : ValidRetainedGraph n B d hz.1 := ⟨hfit, hs.some.1, hs.some.2⟩
    rw [symmetricHiddenWalshDensity_eq_blockDensity n B d hd hfit h hz hH,
      groupedHiddenWalshDensity, dif_pos hs]
    split_ifs with hy
    · rw [← blockDensity_grouped_hidden_walsh_expansion
        n B d hd hfit h hz.1 hz.2 hs.some y hy]
      exact (mul_div_cancel₀ _ (ne_of_gt (Finset.prod_pos (fun ℓ _ => hy ℓ)))).symm
    · obtain ⟨ℓ, hℓ⟩ := not_forall.mp hy
      have hz0 : refDensity d h (y ℓ) = 0 :=
        le_antisymm (not_lt.mp hℓ) (refDensity_nonneg d h (y ℓ))
      exact blockDensity_zero_of_reference_zero
        n B d hd hfit h hz.1 hz.2 hs.some y ℓ hz0
  · simp only [symmetricHiddenWalshDensity, groupedHiddenWalshDensity, dif_neg hs]

/-- The actual conditional law uses the grouped likelihood with the full graph
and assignment marginal, retaining every observed coordinate.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq,H), [the stated conclusion holds](goal). -/
lemma conditionalBlockLaw_grouped_hidden_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool) :
    conditionalBlockLaw n B d (thinnedDesign (Fin n) q) true h H =
      (retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H})⁻¹ •
        (((graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
          (volume.withDensity (fun y => ENNReal.ofReal
            (groupedHiddenWalshDensity n B d hfit h hz y))).map
              (fun y => (hz.1, hz.2, y)))).restrict {x | x.1 = H}).map Prod.snd := by
  rw [conditionalBlockLaw_symmetric_hidden_walsh_representation n B d h q hn hB hd hfit hh hq]
  simp_rw [symmetricHiddenWalshDensity_eq_grouped n B d hd]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
