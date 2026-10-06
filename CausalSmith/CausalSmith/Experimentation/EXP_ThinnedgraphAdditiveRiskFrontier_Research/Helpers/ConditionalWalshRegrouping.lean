module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ConditionalWalshBridge
/-!
# Revealed and hidden label regrouping of the actual Walsh likelihood

Split each completed row into its fixed revealed labels and original hidden
labels, then group hidden selections by degree before posterior averaging.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Reindex selected Walsh coordinates without changing their cardinalities.  [For the stated data and conditions](hyp:ι,κ,e,a,x), [the stated conclusion holds](goal). -/
-- @node: labeled_walsh_subset_sum_reindex
lemma labeled_walsh_subset_sum_reindex {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (e : ι ↪ κ) (a : ℕ → ℝ) (x : κ → ℝ) :
    (∑ E : Finset ι, a E.card * ∏ j ∈ E, x (e j)) =
      ∑ E ∈ (Finset.univ.image e).powerset, a E.card * ∏ j ∈ E, x j := by
  classical
  rw [Finset.powerset_image, Finset.sum_image
    (Finset.image_injOn_powerset_of_injOn (fun _ _ _ _ h => e.injective h))]
  simp only [Finset.card_image_of_injective _ e.injective,
    Finset.prod_image (fun _ _ _ _ h => e.injective h), Finset.powerset_univ]

/-- Split selected labels uniquely across disjoint revealed and hidden sets.  [For the stated data and conditions](hyp:ι,R,U,hRU,f), [the stated conclusion holds](goal). -/
-- @node: labeled_walsh_powerset_split
lemma labeled_walsh_powerset_split {ι : Type*} [DecidableEq ι] (R U : Finset ι)
    (hRU : Disjoint R U) (f : Finset ι → ℝ) :
    (∑ E ∈ (R ∪ U).powerset, f E) =
      ∑ J ∈ R.powerset, ∑ K ∈ U.powerset, f (J ∪ K) := by
  rw [← Finset.sum_product R.powerset U.powerset (fun i => f (i.1 ∪ i.2))]
  symm
  apply Finset.sum_bij (fun i _ => i.1 ∪ i.2)
  · intro i hi
    obtain ⟨hJ, hK⟩ := Finset.mem_product.mp hi
    exact Finset.mem_powerset.mpr (Finset.union_subset_union
      (Finset.mem_powerset.mp hJ) (Finset.mem_powerset.mp hK))
  · intro i hi j hj he
    obtain ⟨hI₁, hI₂⟩ := Finset.mem_product.mp hi
    obtain ⟨hJ₁, hJ₂⟩ := Finset.mem_product.mp hj
    have hI₁ := Finset.mem_powerset.mp hI₁
    have hI₂ := Finset.mem_powerset.mp hI₂
    have hJ₁ := Finset.mem_powerset.mp hJ₁
    have hJ₂ := Finset.mem_powerset.mp hJ₂
    apply Prod.ext <;> ext x
    · have hn : x ∈ R → x ∉ U := fun hx hu => Finset.disjoint_left.mp hRU hx hu
      have hm := congrArg (fun S : Finset ι => x ∈ S) he
      simp only [Finset.mem_union] at hm
      constructor
      · intro hx
        rcases hm.mp (Or.inl hx) with h | h
        · exact h
        · exact False.elim (hn (hI₁ hx) (hJ₂ h))
      · intro hx
        rcases hm.mpr (Or.inl hx) with h | h
        · exact h
        · exact False.elim (hn (hJ₁ hx) (hI₂ h))
    · have hn : x ∈ U → x ∉ R := fun hx hr => Finset.disjoint_left.mp hRU hr hx
      have hm := congrArg (fun S : Finset ι => x ∈ S) he
      simp only [Finset.mem_union] at hm
      constructor
      · intro hx
        rcases hm.mp (Or.inr hx) with h | h
        · exact False.elim (hn (hI₂ hx) (hJ₁ h))
        · exact h
      · intro hx
        rcases hm.mpr (Or.inr hx) with h | h
        · exact False.elim (hn (hJ₂ hx) (hI₁ h))
        · exact h
  · intro E hE
    refine ⟨(E ∩ R, E ∩ U), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩
    · rw [← Finset.inter_union_distrib_left]
      exact Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hE)
  · intro i hi
    rfl

/-- A completed row Walsh expansion indexed by original population labels.  [For the stated data and conditions](hyp:n,B,d,hfit,h,s,z,ℓ,w), [the stated conclusion holds](goal). -/
-- @node: partitionRowSigns_walsh_sum_labels
lemma partitionRowSigns_walsh_sum_labels (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (h : ℝ) (s : SourcePartition B d) (z : Assign (Fin n)) (ℓ : Fin B) (w : ℝ) :
    (∑ E : Finset (Fin d), walshCoeff d h E.card w *
      ∏ j ∈ E, signOf (partitionRowSigns n B d hfit s z ℓ j)) =
    ∑ E ∈ (partitionSourceLabels n B d s ℓ).powerset,
      walshCoeff d h E.card w * ∏ j ∈ E, signOf (z j) := by
  let e : Fin d ↪ Fin n :=
    (Finset.equivFinOfCardEq (partitionSourceLabels_card n B d hfit s ℓ)).symm.toEmbedding.trans
      ⟨Subtype.val, Subtype.val_injective⟩
  have he : Finset.univ.image e = partitionSourceLabels n B d s ℓ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      exact ((Finset.equivFinOfCardEq (partitionSourceLabels_card n B d hfit s ℓ)).symm k).2
    · intro hj
      refine ⟨(Finset.equivFinOfCardEq (partitionSourceLabels_card n B d hfit s ℓ)) ⟨j,hj⟩, ?_⟩
      simp [e]
  simpa only [he, partitionRowSigns, e, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, Function.Embedding.coeFn_mk] using
    labeled_walsh_subset_sum_reindex e (fun k => walshCoeff d h k w) (fun j => signOf (z j))

/-- Compatibility decomposes each completed row into its fixed revealed sources
and its original hidden sources.  [For the stated data and conditions](hyp:n,B,d,H,s,ℓ), [the stated conclusion holds](goal). -/
-- @node: partitionSourceLabels_eq_revealed_union_hidden
lemma partitionSourceLabels_eq_revealed_union_hidden (n B d : ℕ)
    (H : OffDiag (Fin n) → Bool) (s : CompatiblePartition n B d H) (ℓ : Fin B) :
    partitionSourceLabels n B d s.1 ℓ =
      revealedSources n B d H ℓ ∪ partitionHiddenLabels n B d s.1 H ℓ := by
  exact (Finset.union_sdiff_of_subset
    (revealedSources_subset_partitionSourceLabels n B d s.1 H s.2 ℓ)).symm

/-- Revealed and hidden source selections are disjoint within every completed row.  [For the stated data and conditions](hyp:n,B,d,H,s,ℓ), [the stated conclusion holds](goal). -/
-- @node: partition_revealed_hidden_disjoint
lemma partition_revealed_hidden_disjoint (n B d : ℕ)
    (H : OffDiag (Fin n) → Bool) (s : SourcePartition B d) (ℓ : Fin B) :
    Disjoint (revealedSources n B d H ℓ) (partitionHiddenLabels n B d s H ℓ) := by
  exact Finset.disjoint_left.mpr (fun j hj hU => (Finset.mem_sdiff.mp hU).2 hj)

/-- The actual completed-row Walsh sum, with the revealed monomial separated and
hidden original-label subsets grouped by their selected degree. -/
-- @node: completedRowWalshSum
def completedRowWalshSum (n B d : ℕ) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (s : SourcePartition B d) (z : Assign (Fin n)) (ℓ : Fin B) (w : ℝ) : ℝ :=
  ∑ J ∈ (revealedSources n B d H ℓ).powerset,
    (∏ j ∈ J, signOf (z j)) *
      ∑ k ∈ Finset.range (capacity n B d H ℓ + 1), walshCoeff d h (J.card + k) w *
        ∑ E ∈ (partitionHiddenLabels n B d s H ℓ).powersetCard k,
          ∏ j ∈ E, signOf (z j)

/-- Exact revealed/hidden splitting and degree regrouping for a compatible row.  [For the stated data and conditions](hyp:n,B,d,hfit,h,H,s,z,ℓ,w), [the stated conclusion holds](goal). -/
-- @node: partitionRowSigns_walsh_sum_regrouped
lemma partitionRowSigns_walsh_sum_regrouped (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (s : CompatiblePartition n B d H) (z : Assign (Fin n)) (ℓ : Fin B) (w : ℝ) :
    (∑ E : Finset (Fin d), walshCoeff d h E.card w *
      ∏ j ∈ E, signOf (partitionRowSigns n B d hfit s.1 z ℓ j)) =
      completedRowWalshSum n B d h H s.1 z ℓ w := by
  rw [partitionRowSigns_walsh_sum_labels,
    partitionSourceLabels_eq_revealed_union_hidden n B d H s ℓ,
    labeled_walsh_powerset_split _ _ (partition_revealed_hidden_disjoint n B d H s.1 ℓ)]
  unfold completedRowWalshSum
  apply Finset.sum_congr rfl
  intro J hJ
  have hJU (E : Finset (Fin n)) (hE : E ∈ (partitionHiddenLabels n B d s.1 H ℓ).powerset) :
      Disjoint J E :=
    (partition_revealed_hidden_disjoint n B d H s.1 ℓ).mono
      (Finset.mem_powerset.mp hJ) (Finset.mem_powerset.mp hE)
  calc
    _ = (∏ j ∈ J, signOf (z j)) *
        ∑ E ∈ (partitionHiddenLabels n B d s.1 H ℓ).powerset,
          walshCoeff d h (J.card + E.card) w * ∏ j ∈ E, signOf (z j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.card_union_of_disjoint (hJU E hE), Finset.prod_union (hJU E hE)]
      ring
    _ = _ := by
      congr 1
      rw [Finset.sum_powerset, partitionHiddenLabels_card n B d hfit s.1 H s.2 ℓ]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [(Finset.mem_powersetCard.mp hE).2]

/-- The posterior average of the actual likelihood, regrouped into revealed
monomials and hidden degree selections while preserving original labels.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,z,s₀,y,hy), [the stated conclusion holds](goal). -/
-- @node: blockDensity_completion_regrouped_walsh_expansion
lemma blockDensity_completion_regrouped_walsh_expansion (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ)) :
    blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) =
      (Fintype.card (HiddenCompletion n B d H) : ℝ)⁻¹ *
        ∑ g : HiddenCompletion n B d H,
          ∏ ℓ, completedRowWalshSum n B d h H
            (hiddenCompletionPartition n B d hfit H s₀ g).1 z ℓ (y ℓ) := by
  rw [blockDensity_completion_walsh_expansion n B d hd hfit h H z s₀ y hy]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  exact partitionRowSigns_walsh_sum_regrouped n B d hfit h H _ z ℓ (y ℓ)


/-- Expanding the completed likelihood across rows separates the fixed revealed
monomial and coefficient product from the selected hidden-label monomials.  [For the stated data and conditions](hyp:n,B,d,h,H,s,z,y), [the stated conclusion holds](goal). -/
-- @node: completedRowWalshSum_product_expansion
lemma completedRowWalshSum_product_expansion (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (s : SourcePartition B d)
    (z : Assign (Fin n)) (y : Fin B → ℝ) :
    (∏ ℓ, completedRowWalshSum n B d h H s z ℓ (y ℓ)) =
      ∑ J ∈ Fintype.piFinset (fun ℓ : Fin B => (revealedSources n B d H ℓ).powerset),
        (∏ ℓ, ∏ j ∈ J ℓ, signOf (z j)) *
        ∑ k ∈ Fintype.piFinset (fun ℓ : Fin B => Finset.range (capacity n B d H ℓ + 1)),
          (∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)) *
            ∏ ℓ, ∑ E ∈ (partitionHiddenLabels n B d s H ℓ).powersetCard (k ℓ),
              ∏ j ∈ E, signOf (z j) := by
  classical
  simp only [completedRowWalshSum]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact Finset.prod_mul_distrib

/-- The exact uniform-completion moment of hidden selected-label monomials.
The row degrees are fixed, while their original labels remain jointly allocated. -/
-- @node: completionHiddenSelectionMoment
def completionHiddenSelectionMoment (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s₀ : CompatiblePartition n B d H)
    (z : Assign (Fin n)) (k : Fin B → ℕ) : ℝ :=
  (Fintype.card (HiddenCompletion n B d H) : ℝ)⁻¹ *
    ∑ g : HiddenCompletion n B d H,
      ∏ ℓ, ∑ E ∈ (partitionHiddenLabels n B d
        (hiddenCompletionPartition n B d hfit H s₀ g).1 H ℓ).powersetCard (k ℓ),
        ∏ j ∈ E, signOf (z j)

/-- Move the posterior average onto hidden monomials after expanding across rows.
All revealed selections and response coefficients are fixed by the full record.  [For the stated data and conditions](hyp:n,B,d,hfit,h,H,s₀,z,y), [the stated conclusion holds](goal). -/
-- @node: completion_walsh_average_selection_expansion
lemma completion_walsh_average_selection_expansion (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (s₀ : CompatiblePartition n B d H) (z : Assign (Fin n)) (y : Fin B → ℝ) :
    (Fintype.card (HiddenCompletion n B d H) : ℝ)⁻¹ *
      (∑ g : HiddenCompletion n B d H,
        ∏ ℓ, completedRowWalshSum n B d h H
          (hiddenCompletionPartition n B d hfit H s₀ g).1 z ℓ (y ℓ)) =
    ∑ J ∈ Fintype.piFinset (fun ℓ : Fin B => (revealedSources n B d H ℓ).powerset),
      (∏ ℓ, ∏ j ∈ J ℓ, signOf (z j)) *
      ∑ k ∈ Fintype.piFinset (fun ℓ : Fin B => Finset.range (capacity n B d H ℓ + 1)),
        (∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)) *
          completionHiddenSelectionMoment n B d hfit H s₀ z k := by
  classical
  simp_rw [completedRowWalshSum_product_expansion]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
  simp only [completionHiddenSelectionMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro g hg
  ring

/-- The actual density ratio with its posterior average confined to the hidden
selected-label moment; no graph or treatment coordinate has been discarded.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,z,s₀,y,hy), [the stated conclusion holds](goal). -/
-- @node: blockDensity_completion_selection_expansion
lemma blockDensity_completion_selection_expansion (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ)) :
    blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) =
    ∑ J ∈ Fintype.piFinset (fun ℓ : Fin B => (revealedSources n B d H ℓ).powerset),
      (∏ ℓ, ∏ j ∈ J ℓ, signOf (z j)) *
      ∑ k ∈ Fintype.piFinset (fun ℓ : Fin B => Finset.range (capacity n B d H ℓ + 1)),
        (∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)) *
          completionHiddenSelectionMoment n B d hfit H s₀ z k := by
  rw [blockDensity_completion_regrouped_walsh_expansion n B d hd hfit h H z s₀ y hy,
    completion_walsh_average_selection_expansion]

/-- The actual posterior density after splitting revealed selections and grouping
hidden selections by degree, extended by zero on the reference-zero set. -/
-- @node: regroupedCompletionWalshDensity
def regroupedCompletionWalshDensity (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) : ℝ :=
  if hs : Nonempty (CompatiblePartition n B d hz.1) then
    if ∀ ℓ, 0 < refDensity d h (y ℓ) then
      (∏ ℓ, refDensity d h (y ℓ)) *
        (∑ J ∈ Fintype.piFinset
          (fun ℓ : Fin B => (revealedSources n B d hz.1 ℓ).powerset),
          (∏ ℓ, ∏ j ∈ J ℓ, signOf (hz.2 j)) *
          ∑ k ∈ Fintype.piFinset
            (fun ℓ : Fin B => Finset.range (capacity n B d hz.1 ℓ + 1)),
            (∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)) *
              completionHiddenSelectionMoment n B d hfit hz.1 hs.some hz.2 k)
    else 0
  else 0

/-- Regrouping gives the actual conditional response density on every compatible
retained graph, including zero reference-density endpoints.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,hz,hH,y), [the stated conclusion holds](goal). -/
-- @node: regroupedCompletionWalshDensity_eq_blockDensity
lemma regroupedCompletionWalshDensity_eq_blockDensity (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n))
    (hH : ValidRetainedGraph n B d hz.1) (y : Fin B → ℝ) :
    regroupedCompletionWalshDensity n B d hfit h hz y =
      blockDensity n B d true h hz.1 hz.2 y := by
  have hs : Nonempty (CompatiblePartition n B d hz.1) := by
    obtain ⟨_, s, hs⟩ := hH
    exact ⟨⟨s, hs⟩⟩
  rw [regroupedCompletionWalshDensity, dif_pos hs]
  split_ifs with hy
  · rw [← blockDensity_completion_selection_expansion
      n B d hd hfit h hz.1 hz.2 hs.some y hy]
    exact mul_div_cancel₀ _ (ne_of_gt (Finset.prod_pos (fun ℓ _ => hy ℓ)))
  · obtain ⟨ℓ, hℓ⟩ := not_forall.mp hy
    have hz0 : refDensity d h (y ℓ) = 0 :=
      le_antisymm (not_lt.mp hℓ) (refDensity_nonneg d h (y ℓ))
    exact (blockDensity_zero_of_reference_zero
      n B d hd hfit h hz.1 hz.2 hs.some y ℓ hz0).symm

/-- The reduced actual law uses the regrouped density and retains the complete
graph together with every assignment coordinate.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq), [the stated conclusion holds](goal). -/
lemma reducedBlockLaw_regrouped_completion_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1) :
    reducedBlockLaw n B d (thinnedDesign (Fin n) q) true h =
      (graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
        (volume.withDensity (fun y => ENNReal.ofReal
          (regroupedCompletionWalshDensity n B d hfit h hz y))).map
            (fun y => (hz.1, hz.2, y))) := by
  rw [reducedBlockLaw_completion_walsh_representation n B d h q hn hB hd hfit hh hq]
  apply Measure.bind_congr_right
  have hv : ∀ᵐ hz ∂(graphAssignMarginal n B d (thinnedDesign (Fin n) q)),
      ValidRetainedGraph n B d hz.1 :=
    (ae_map_iff (by fun_prop) (by measurability)).mp
      (retainedGraphMarginal_valid n B d (thinnedDesign (Fin n) q) hfit)
  filter_upwards [hv] with hz hH
  simp_rw [completionWalshDensity_eq_blockDensity n B d hd hfit h hz hH,
    regroupedCompletionWalshDensity_eq_blockDensity n B d hd hfit h hz hH]

/-- Conditioning on the entire detailed graph uses exactly the regrouped
posterior likelihood, with no independence substitution for hidden treatments.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq,H), [the stated conclusion holds](goal). -/
lemma conditionalBlockLaw_regrouped_completion_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool) :
    conditionalBlockLaw n B d (thinnedDesign (Fin n) q) true h H =
      (retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H})⁻¹ •
        (((graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
          (volume.withDensity (fun y => ENNReal.ofReal
            (regroupedCompletionWalshDensity n B d hfit h hz y))).map
              (fun y => (hz.1, hz.2, y)))).restrict {x | x.1 = H}).map Prod.snd := by
  rw [conditionalBlockLaw,
    reducedBlockLaw_regrouped_completion_walsh_representation n B d h q hn hB hd hfit hh hq]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
