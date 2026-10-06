module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.GroupedConditionalLikelihood

/-!
# Revealed-label indexing of the conditional Walsh likelihood

Disjoint revealed rows identify their subset families bijectively with subsets
of the union of revealed labels. This puts the actual posterior likelihood in
the label-monomial indexing used by the joint sign energy decomposition.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Compatibility assigns each revealed source to a unique row.  [For the stated data and conditions](hyp:n,B,d,H,s), [the stated conclusion holds](goal). -/
-- @node: revealedSources_pairwise_disjoint
lemma revealedSources_pairwise_disjoint (n B d : ℕ) (H : OffDiag (Fin n) → Bool)
    (s : CompatiblePartition n B d H) :
    Pairwise (fun a b : Fin B => Disjoint
      (revealedSources n B d H a) (revealedSources n B d H b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro j hja hjb
  have ha := revealedSources_subset_partitionSourceLabels n B d s.1 H s.2 a hja
  have hb := revealedSources_subset_partitionSourceLabels n B d s.1 H s.2 b hjb
  obtain ⟨h₁, h₁a⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨h₂, h₂b⟩ := (Finset.mem_filter.mp hb).2
  exact hab (h₁a.symm.trans h₂b)

/-- Intersecting the union of a disjoint row-subset family with one row recovers
exactly that row's selected labels.  [For the stated data and conditions](hyp:ι,α,R,J,hR,hJ,a), [the stated conclusion holds](goal). -/
-- @node: disjoint_rowSubset_union_inter
lemma disjoint_rowSubset_union_inter {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] (R J : ι → Finset α)
    (hR : Pairwise (fun a b => Disjoint (R a) (R b)))
    (hJ : ∀ a, J a ⊆ R a) (a : ι) :
    (Finset.univ.biUnion J) ∩ R a = J a := by
  ext j
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨b, hj⟩, hra⟩
    by_cases hba : b = a
    · simpa [hba] using hj
    · exact False.elim (Finset.disjoint_left.mp (hR hba) (hJ b hj) hra)
  · intro hj
    exact ⟨⟨a, hj⟩, hJ a hj⟩

/-- Every subset of a row union is recovered from its intersections with the rows.  [For the stated data and conditions](hyp:ι,α,R,J,hJ), [the stated conclusion holds](goal). -/
-- @node: rowSubset_inter_union
lemma rowSubset_inter_union {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] (R : ι → Finset α) (J : Finset α)
    (hJ : J ⊆ Finset.univ.biUnion R) :
    Finset.univ.biUnion (fun a => J ∩ R a) = J := by
  ext j
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨a, hj, _⟩
    exact hj
  · intro hj
    obtain ⟨a, _, hra⟩ := Finset.mem_biUnion.mp (hJ hj)
    exact ⟨a, hj, hra⟩

/-- Summing over disjoint row-subset families equals summing over subsets of
all revealed labels, with row intersections as the inverse map.  [For the stated data and conditions](hyp:ι,α,R,hR,f), [the stated conclusion holds](goal). -/
-- @node: disjoint_rowSubset_sum_reindex
lemma disjoint_rowSubset_sum_reindex {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] (R : ι → Finset α)
    (hR : Pairwise (fun a b => Disjoint (R a) (R b)))
    (f : (ι → Finset α) → ℝ) :
    (∑ J ∈ Fintype.piFinset (fun a => (R a).powerset), f J) =
      ∑ J ∈ (Finset.univ.biUnion R).powerset, f (fun a => J ∩ R a) := by
  apply Finset.sum_bij (fun J _ => Finset.univ.biUnion J)
  · intro J hJ
    apply Finset.mem_powerset.mpr
    intro j hj
    obtain ⟨a, ha, hja⟩ := Finset.mem_biUnion.mp hj
    exact Finset.mem_biUnion.mpr ⟨a, ha,
      Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hJ a) hja⟩
  · intro J hJ K hK he
    funext a
    have hsubJ := fun a => Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hJ a)
    have hsubK := fun a => Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hK a)
    rw [← disjoint_rowSubset_union_inter R J hR hsubJ a,
      ← disjoint_rowSubset_union_inter R K hR hsubK a, he]
  · intro J hJ
    refine ⟨fun a => J ∩ R a, ?_, rowSubset_inter_union R J (Finset.mem_powerset.mp hJ)⟩
    exact Fintype.mem_piFinset.mpr (fun a =>
      Finset.mem_powerset.mpr Finset.inter_subset_right)
  · intro J hJ
    congr 1
    funext a
    exact (disjoint_rowSubset_union_inter R J hR
      (fun a => Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hJ a)) a).symm

/-- Products over a row-subset family are precisely monomials in its union of
original revealed labels.  [For the stated data and conditions](hyp:ι,α,R,J,hR,hJ,z), [the stated conclusion holds](goal). -/
-- @node: disjoint_rowSubset_signProduct
lemma disjoint_rowSubset_signProduct {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] (R J : ι → Finset α)
    (hR : Pairwise (fun a b => Disjoint (R a) (R b)))
    (hJ : ∀ a, J a ⊆ R a) (z : α → Bool) :
    (∏ a, ∏ j ∈ J a, signOf (z j)) =
      ∏ j ∈ Finset.univ.biUnion J, signOf (z j) := by
  symm
  apply Finset.prod_biUnion
  intro a _ b _ hab
  exact (hR hab).mono (hJ a) (hJ b)

/-- The grouped actual likelihood is a sum of distinct revealed-label monomials
and symmetric hidden polynomials with the exact row-intersection coefficients.  [For the stated data and conditions](hyp:n,B,d,h,H,s,z,y,x), [the stated conclusion holds](goal). -/
-- @node: groupedHiddenWalsh_sum_labelSubsets
lemma groupedHiddenWalsh_sum_labelSubsets (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (s : CompatiblePartition n B d H)
    (z : Assign (Fin n)) (y : Fin B → ℝ)
    (x : Fin (undiscovered n B d H) → Bool) :
    (∑ J ∈ Fintype.piFinset
      (fun ℓ : Fin B => (revealedSources n B d H ℓ).powerset),
      (∏ ℓ, ∏ j ∈ J ℓ, signOf (z j)) *
        ∑ t ∈ Finset.range (undiscovered n B d H + 1),
          symmetricSignPoly (undiscovered n B d H) t x *
            groupedHiddenWalshCoeff n B d h H J t y) =
    ∑ J ∈ (Finset.univ.biUnion (revealedSources n B d H)).powerset,
      (∏ j ∈ J, signOf (z j)) *
        ∑ t ∈ Finset.range (undiscovered n B d H + 1),
          symmetricSignPoly (undiscovered n B d H) t x *
            groupedHiddenWalshCoeff n B d h H
              (fun ℓ => J ∩ revealedSources n B d H ℓ) t y := by
  rw [disjoint_rowSubset_sum_reindex _ (revealedSources_pairwise_disjoint n B d H s)]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [disjoint_rowSubset_signProduct _ _ (revealedSources_pairwise_disjoint n B d H s)
    (fun _ => Finset.inter_subset_right),
    rowSubset_inter_union _ J (Finset.mem_powerset.mp hJ)]

/-- The actual posterior density with each revealed monomial indexed by its
source-label subset, retaining the reference-zero extension. -/
-- @node: labelSubsetHiddenWalshDensity
def labelSubsetHiddenWalshDensity (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) : ℝ :=
  if hs : Nonempty (CompatiblePartition n B d hz.1) then
    if ∀ ℓ, 0 < refDensity d h (y ℓ) then
      (∏ ℓ, refDensity d h (y ℓ)) *
        (∑ J ∈ (Finset.univ.biUnion (revealedSources n B d hz.1)).powerset,
          (∏ j ∈ J, signOf (hz.2 j)) *
            ∑ t ∈ Finset.range (undiscovered n B d hz.1 + 1),
              symmetricSignPoly (undiscovered n B d hz.1) t
                (fun i => hz.2 (hiddenSourceLabelEmbedding n B d hfit hz.1
                  ((hiddenSourceEnumeration n B d hfit hz.1 hs.some).symm i))) *
                groupedHiddenWalshCoeff n B d h hz.1
                  (fun ℓ => J ∩ revealedSources n B d hz.1 ℓ) t y)
    else 0
  else 0

/-- The label-subset density equals the actual grouped density on every graph
and response, including impossible graphs and reference-density zeros.  [For the stated data and conditions](hyp:n,B,d,hfit,h,hz,y), [the stated conclusion holds](goal). -/
-- @node: groupedHiddenWalshDensity_eq_labelSubset
lemma groupedHiddenWalshDensity_eq_labelSubset (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) :
    groupedHiddenWalshDensity n B d hfit h hz y =
      labelSubsetHiddenWalshDensity n B d hfit h hz y := by
  unfold groupedHiddenWalshDensity labelSubsetHiddenWalshDensity
  split_ifs with hs hy
  · rw [groupedHiddenWalsh_sum_labelSubsets n B d h hz.1 hs.some]
  all_goals rfl

/-- Conditioning the original mixture on the complete retained graph now gives
the distinct revealed-label expansion required by sign orthogonality.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq,H), [the stated conclusion holds](goal). -/
lemma conditionalBlockLaw_labelSubset_hidden_walsh_representation
    (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool) :
    conditionalBlockLaw n B d (thinnedDesign (Fin n) q) true h H =
      (retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H})⁻¹ •
        (((graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
          (volume.withDensity (fun y => ENNReal.ofReal
            (labelSubsetHiddenWalshDensity n B d hfit h hz y))).map
              (fun y => (hz.1, hz.2, y)))).restrict {x | x.1 = H}).map Prod.snd := by
  rw [conditionalBlockLaw_grouped_hidden_walsh_representation n B d h q hn hB hd hfit hh hq]
  simp_rw [groupedHiddenWalshDensity_eq_labelSubset]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
