import Causalean.Graph.FiniteDensity.Leaf

/-!
# Reverse-topological elimination outside a parent-closed set

This module iterates normalized leaf elimination.  A parent-closed set retains all factors that
can influence it, so factors outside it may be removed in reverse topological order.  The result
is stated both for an arbitrary retained set and for the complement marginal of a full density.
-/

open scoped ENNReal
open Set Function
open MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : Causalean.DAG V}

/-- A [finite DAG](hyp:G) and a [finite node set](hyp:A) determine [the property that the set
contains every parent of each of its nodes](goal). -/
def ParentClosed (G : Causalean.DAG V) (A : Finset V) : Prop :=
  ∀ ⦃i⦄, i ∈ A → G.parents i ⊆ A

/-- A [parent-closed retained set](hyp:hA), its [disjointness from an eliminable set](hyp:hAT), and
[a nonempty eliminable set](hyp:hT) [produce an eliminable node that is a leaf of their union](goal). -/
theorem exists_leaf_in_union_of_parentClosed
    {A T : Finset V} (hA : ParentClosed G A) (hAT : Disjoint A T) (hT : T.Nonempty) :
    ∃ k ∈ T, IsLeafIn G k (A ∪ T) := by
  -- Choose a `topoOrder`-maximal node of `T`; parent-closure excludes edges from it into `A`.
  obtain ⟨k, hkT, hkmax⟩ := Finset.exists_max_image T G.topoOrder hT
  refine ⟨k, hkT, Finset.mem_union_right A hkT, ?_⟩
  intro l hlU hlk hkl
  rcases Finset.mem_union.mp hlU with hlA | hlT
  · have hkA : k ∈ A := hA hlA (G.mem_parents.mpr hkl)
    exact (Finset.disjoint_left.mp hAT hkA hkT)
  · exact (not_lt_of_ge (hkmax l hlT)) (G.topoOrder_lt k l hkl)

/-- A [DAG factorization](hyp:B), a [parent-closed retained set](hyp:hA), and its [disjointness
from an eliminable set](hyp:hAT) [show that integrating every eliminable coordinate removes all
of their factors](goal). -/
theorem Factorization.lmarginal_partialDensity_union_eq
    (B : Factorization G X μ) {A T : Finset V}
    (hA : ParentClosed G A) (hAT : Disjoint A T) :
    (∫⋯∫⁻_T, B.partialDensity (A ∪ T) ∂μ) = B.partialDensity A := by
  -- Induct on `T`, peel a reverse-topological leaf via `lmarginal_erase'`, and use
  -- leaf elimination.
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    by_cases hT : T.Nonempty
    · obtain ⟨k, hkT, hleaf⟩ :=
        exists_leaf_in_union_of_parentClosed hA hAT hT
      rw [MeasureTheory.lmarginal_erase' _
        (B.measurable_partialDensity (A ∪ T)) hkT]
      simp_rw [B.lintegral_partialDensity_leaf hleaf]
      have hkA : k ∉ A := fun hkA ↦ Finset.disjoint_left.mp hAT hkA hkT
      have herase : (A ∪ T).erase k = A ∪ T.erase k := by
        ext i
        simp only [Finset.mem_erase, Finset.mem_union]
        constructor
        · rintro ⟨hik, hiA | hiT⟩
          · exact Or.inl hiA
          · exact Or.inr ⟨hik, hiT⟩
        · rintro (hiA | ⟨hik, hiT⟩)
          · exact ⟨fun hik ↦ hkA (hik ▸ hiA), Or.inl hiA⟩
          · exact ⟨hik, Or.inr hiT⟩
      rw [herase]
      exact ih (T.erase k) (Finset.erase_ssubset hkT)
        (Disjoint.mono_right (Finset.erase_subset k T) hAT)
    · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      subst T
      simp

/-- A [DAG factorization](hyp:B) and a [parent-closed retained set](hyp:hA) [show that integrating
the observational density outside the set leaves precisely its retained factor product](goal). -/
theorem Factorization.lmarginal_compl_observationalDensity_eq
    (B : Factorization G X μ) {A : Finset V} (hA : ParentClosed G A) :
    (∫⋯∫⁻_(Finset.univ \ A), B.observationalDensity ∂μ) = B.partialDensity A := by
  -- Rewrite `univ` as `A ∪ (univ \ A)` and invoke the union elimination theorem.
  have huniv : A ∪ (Finset.univ \ A) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ A)
  calc
    (∫⋯∫⁻_(Finset.univ \ A), B.observationalDensity ∂μ) =
        (∫⋯∫⁻_(Finset.univ \ A),
          B.partialDensity (A ∪ (Finset.univ \ A)) ∂μ) := by
      rw [huniv]
      rfl
    _ = B.partialDensity A :=
      B.lmarginal_partialDensity_union_eq hA Finset.disjoint_sdiff

/-- A [DAG factorization](hyp:B), a [parent-closed retained set](hyp:hA), an [intervention target
outside that set](hyp:hj), and a [normalized replacement density](hyp:q) [show that integrating
the intervention density outside the set leaves the same retained factor product](goal). -/
theorem Factorization.lmarginal_compl_interventionDensity_eq
    (B : Factorization G X μ) {A : Finset V} (hA : ParentClosed G A)
    {j : V} (hj : j ∉ A) (q : InterventionDensity j X μ) :
    (∫⋯∫⁻_(Finset.univ \ A), B.interventionDensity j q ∂μ) = B.partialDensity A := by
  -- Rewrite the density as `(B.intervene j q).observationalDensity` and note its factors
  -- agree on `A`.
  calc
    (∫⋯∫⁻_(Finset.univ \ A), B.interventionDensity j q ∂μ) =
        (∫⋯∫⁻_(Finset.univ \ A),
          (B.intervene j q).observationalDensity ∂μ) := by
      rw [B.observationalDensity_intervene]
    _ = (B.intervene j q).partialDensity A :=
      (B.intervene j q).lmarginal_compl_observationalDensity_eq hA
    _ = B.partialDensity A := by
      unfold Factorization.partialDensity
      funext v
      apply Finset.prod_congr rfl
      intro i hi
      have hij : i ≠ j := by
        intro hij
        subst i
        exact hj hi
      simp only [Factorization.intervene, hij, ↓reduceIte]

end Causalean.Graph.FiniteDensity
