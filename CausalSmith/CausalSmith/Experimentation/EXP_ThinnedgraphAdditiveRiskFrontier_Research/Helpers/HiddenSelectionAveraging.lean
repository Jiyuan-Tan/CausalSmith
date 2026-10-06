module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ConditionalWalshRegrouping

/-!
# Original hidden-label selection averages

Reindex the completion likelihood by capacity-constrained words on the original
hidden source type. Permutations of those labels preserve the posterior average.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Embed an original hidden source in the observed population coordinates. -/
-- @node: hiddenSourceLabelEmbedding
def hiddenSourceLabelEmbedding (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) : HiddenSource n B d H ↪ Fin n where
  toFun j := ⟨j.1.val, by have := j.1.isLt; omega⟩
  inj' := by intro i j hij; apply Subtype.ext; exact Fin.ext (congrArg (fun v : Fin n => v.val) hij)

/-- A completed row's hidden labels are exactly its hidden-word fiber.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s₀,g,ℓ), [the stated conclusion holds](goal). -/
-- @node: partitionHiddenLabels_eq_word_fiber
lemma partitionHiddenLabels_eq_word_fiber (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s₀ : CompatiblePartition n B d H)
    (g : HiddenCompletion n B d H) (ℓ : Fin B) :
    partitionHiddenLabels n B d (hiddenCompletionPartition n B d hfit H s₀ g).1 H ℓ =
      (Finset.univ.filter (fun j => g.1 j = ℓ)).map
        (hiddenSourceLabelEmbedding n B d hfit H) := by
  ext j
  rw [partitionHiddenLabels_mem_iff n B d _ H
    (hiddenCompletionPartition n B d hfit H s₀ g).2]
  constructor
  · rintro ⟨⟨hj, hrow⟩, hhidden⟩
    have hr := (sourceReveals_false_iff n B d H j hj).mpr hhidden
    refine Finset.mem_map.mpr ⟨⟨⟨j.val,hj⟩,hr⟩, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        hiddenCompletionPartition, hiddenCompletionExtension, dif_pos hr] using hrow
    · rfl
  · rintro hmap
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hmap
    refine ⟨⟨v.1.isLt, ?_⟩, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        hiddenSourceLabelEmbedding, Function.Embedding.coeFn_mk,
        hiddenCompletionPartition, hiddenCompletionExtension, dif_pos v.2] using hv
    · exact (sourceReveals_false_iff n B d H _ v.1.isLt).mp v.2

/-- Selected-subset monomials commute with an injective relabeling.  [For the stated data and conditions](hyp:ι,κ,e,S,k,x), [the stated conclusion holds](goal). -/
-- @node: powersetCard_monomial_sum_map
lemma powersetCard_monomial_sum_map {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (S : Finset ι) (k : ℕ) (x : κ → ℝ) :
    (∑ E ∈ (S.map e).powersetCard k, ∏ j ∈ E, x j) =
      ∑ E ∈ S.powersetCard k, ∏ j ∈ E, x (e j) := by
  rw [Finset.powersetCard_map]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro E hE
  change (∏ j ∈ E.map e, x j) = _
  rw [Finset.prod_map]

/-- The exact completion average expressed solely on original hidden labels. -/
-- @node: hiddenWordSelectionAverage
def hiddenWordSelectionAverage (n B d : ℕ) (H : OffDiag (Fin n) → Bool)
    (x : HiddenSource n B d H → ℝ) (k : Fin B → ℕ) : ℝ :=
  (Fintype.card (HiddenCompletion n B d H) : ℝ)⁻¹ *
    ∑ g : HiddenCompletion n B d H,
      ∏ ℓ, ∑ E ∈ (Finset.univ.filter (fun j => g.1 j = ℓ)).powersetCard (k ℓ),
        ∏ j ∈ E, x j

/-- The hidden moment in the actual likelihood is the original-label word average.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s₀,z,k), [the stated conclusion holds](goal). -/
-- @node: completionHiddenSelectionMoment_eq_word_average
lemma completionHiddenSelectionMoment_eq_word_average (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (H : OffDiag (Fin n) → Bool)
    (s₀ : CompatiblePartition n B d H) (z : Assign (Fin n)) (k : Fin B → ℕ) :
    completionHiddenSelectionMoment n B d hfit H s₀ z k =
      hiddenWordSelectionAverage n B d H
        (fun j => signOf (z (hiddenSourceLabelEmbedding n B d hfit H j))) k := by
  unfold completionHiddenSelectionMoment hiddenWordSelectionAverage
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  rw [partitionHiddenLabels_eq_word_fiber,
    powersetCard_monomial_sum_map]

/-- Relabeling a word carries each row fiber bijectively to its relabeled fiber.  [For the stated data and conditions](hyp:ι,κ,e,g,ℓ), [the stated conclusion holds](goal). -/
-- @node: hidden_word_fiber_relabel
lemma hidden_word_fiber_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq (Fin B)]
    (e : ι ≃ κ) (g : ι → Fin B) (ℓ : Fin B) :
    (Finset.univ.filter (fun j => g (e.symm j) = ℓ)) =
      (Finset.univ.filter (fun j => g j = ℓ)).map e.toEmbedding := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.toEmbedding_apply]
  constructor
  · intro hj
    exact ⟨e.symm j, hj, e.apply_symm_apply j⟩
  · rintro ⟨i, hi, rfl⟩
    simpa using hi

/-- Permutations of original hidden labels preserve every row capacity. -/
-- @node: hiddenCompletionRelabel
def hiddenCompletionRelabel (n B d : ℕ) (H : OffDiag (Fin n) → Bool)
    (e : Equiv.Perm (HiddenSource n B d H)) :
    HiddenCompletion n B d H ≃ HiddenCompletion n B d H where
  toFun g := ⟨fun j => g.1 (e.symm j), by
    intro ℓ
    rw [hidden_word_fiber_relabel, Finset.card_map]
    exact g.2 ℓ⟩
  invFun g := ⟨fun j => g.1 (e j), by
    intro ℓ
    change (Finset.univ.filter (fun j => g.1 (e.symm.symm j) = ℓ)).card = _
    rw [hidden_word_fiber_relabel, Finset.card_map]
    exact g.2 ℓ⟩
  left_inv g := by apply Subtype.ext; funext j; exact congrArg g.1 (e.symm_apply_apply j)
  right_inv g := by apply Subtype.ext; funext j; exact congrArg g.1 (e.apply_symm_apply j)

/-- The jointly constrained hidden-label posterior is exchangeable; no rowwise
independence of hidden assignments is used.  [For the stated data and conditions](hyp:n,B,d,H,e,x,k), [the stated conclusion holds](goal). -/
-- @node: hiddenWordSelectionAverage_relabel
lemma hiddenWordSelectionAverage_relabel (n B d : ℕ) (H : OffDiag (Fin n) → Bool)
    (e : Equiv.Perm (HiddenSource n B d H))
    (x : HiddenSource n B d H → ℝ) (k : Fin B → ℕ) :
    hiddenWordSelectionAverage n B d H (fun j => x (e j)) k =
      hiddenWordSelectionAverage n B d H x k := by
  unfold hiddenWordSelectionAverage
  congr 1
  apply Fintype.sum_equiv (hiddenCompletionRelabel n B d H e)
  intro g
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  change (∑ E ∈ (Finset.univ.filter (fun j => g.1 j = ℓ)).powersetCard (k ℓ),
    ∏ j ∈ E, x (e j)) =
    ∑ E ∈ (Finset.univ.filter (fun j => g.1 (e.symm j) = ℓ)).powersetCard (k ℓ),
      ∏ j ∈ E, x j
  rw [hidden_word_fiber_relabel, powersetCard_monomial_sum_map]
  rfl

/-- Exact hidden-source word expansion of the actual likelihood, invariant under
any permutation of the unrevealed original labels.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,z,s₀,y,hy,e), [the stated conclusion holds](goal). -/
-- @node: blockDensity_hidden_word_selection_expansion
lemma blockDensity_hidden_word_selection_expansion (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ))
    (e : Equiv.Perm (HiddenSource n B d H)) :
    blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) =
    ∑ J ∈ Fintype.piFinset (fun ℓ : Fin B => (revealedSources n B d H ℓ).powerset),
      (∏ ℓ, ∏ j ∈ J ℓ, signOf (z j)) *
      ∑ k ∈ Fintype.piFinset (fun ℓ : Fin B => Finset.range (capacity n B d H ℓ + 1)),
        (∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)) *
          hiddenWordSelectionAverage n B d H
            (fun j => signOf (z (hiddenSourceLabelEmbedding n B d hfit H (e j)))) k := by
  rw [blockDensity_completion_selection_expansion n B d hd hfit h H z s₀ y hy]
  simp_rw [completionHiddenSelectionMoment_eq_word_average,
    hiddenWordSelectionAverage_relabel n B d H e
      (fun j => signOf (z (hiddenSourceLabelEmbedding n B d hfit H j)))]


/-- The posterior response density using exchangeable original hidden-label words,
extended by zero at incompatible graphs and reference-density zeros. -/
-- @node: hiddenWordWalshDensity
def hiddenWordWalshDensity (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) : ℝ :=
  if Nonempty (CompatiblePartition n B d hz.1) then
    if ∀ ℓ, 0 < refDensity d h (y ℓ) then
      (∏ ℓ, refDensity d h (y ℓ)) *
        (∑ J ∈ Fintype.piFinset
          (fun ℓ : Fin B => (revealedSources n B d hz.1 ℓ).powerset),
          (∏ ℓ, ∏ j ∈ J ℓ, signOf (hz.2 j)) *
          ∑ k ∈ Fintype.piFinset
            (fun ℓ : Fin B => Finset.range (capacity n B d hz.1 ℓ + 1)),
            (∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)) *
              hiddenWordSelectionAverage n B d hz.1
                (fun j => signOf (hz.2 (hiddenSourceLabelEmbedding n B d hfit hz.1 j))) k)
    else 0
  else 0

/-- The exchangeable word expansion gives the full actual response density,
including every zero-density endpoint.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,hz,hH,y), [the stated conclusion holds](goal). -/
-- @node: hiddenWordWalshDensity_eq_blockDensity
lemma hiddenWordWalshDensity_eq_blockDensity (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n))
    (hH : ValidRetainedGraph n B d hz.1) (y : Fin B → ℝ) :
    hiddenWordWalshDensity n B d hfit h hz y =
      blockDensity n B d true h hz.1 hz.2 y := by
  have hs : Nonempty (CompatiblePartition n B d hz.1) := by
    obtain ⟨_, s, hs⟩ := hH
    exact ⟨⟨s, hs⟩⟩
  rw [hiddenWordWalshDensity, if_pos hs]
  split_ifs with hy
  · have he := blockDensity_hidden_word_selection_expansion
      n B d hd hfit h hz.1 hz.2 hs.some y hy (Equiv.refl _)
    simp only [Equiv.refl_apply] at he
    rw [← he]
    exact mul_div_cancel₀ _ (ne_of_gt (Finset.prod_pos (fun ℓ _ => hy ℓ)))
  · obtain ⟨ℓ, hℓ⟩ := not_forall.mp hy
    have hz0 : refDensity d h (y ℓ) = 0 :=
      le_antisymm (not_lt.mp hℓ) (refDensity_nonneg d h (y ℓ))
    exact (blockDensity_zero_of_reference_zero
      n B d hd hfit h hz.1 hz.2 hs.some y ℓ hz0).symm

/-- The reduced law retains its detailed graph and entire assignment while using
the original hidden-label word likelihood.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq), [the stated conclusion holds](goal). -/
lemma reducedBlockLaw_hidden_word_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1) :
    reducedBlockLaw n B d (thinnedDesign (Fin n) q) true h =
      (graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
        (volume.withDensity (fun y => ENNReal.ofReal
          (hiddenWordWalshDensity n B d hfit h hz y))).map
            (fun y => (hz.1, hz.2, y))) := by
  rw [reducedBlockLaw_regrouped_completion_walsh_representation n B d h q hn hB hd hfit hh hq]
  apply MeasureTheory.Measure.bind_congr_right
  have hv : ∀ᵐ hz ∂(graphAssignMarginal n B d (thinnedDesign (Fin n) q)),
      ValidRetainedGraph n B d hz.1 :=
    (MeasureTheory.ae_map_iff (by fun_prop) (by measurability)).mp
      (retainedGraphMarginal_valid n B d (thinnedDesign (Fin n) q) hfit)
  filter_upwards [hv] with hz hH
  simp_rw [regroupedCompletionWalshDensity_eq_blockDensity n B d hd hfit h hz hH,
    hiddenWordWalshDensity_eq_blockDensity n B d hd hfit h hz hH]

/-- The conditional law given the complete detailed retained graph is the word
likelihood; ancillary assignment coordinates are retained in the marginal.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq,H), [the stated conclusion holds](goal). -/
lemma conditionalBlockLaw_hidden_word_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool) :
    conditionalBlockLaw n B d (thinnedDesign (Fin n) q) true h H =
      (retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H})⁻¹ •
        (((graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
          (volume.withDensity (fun y => ENNReal.ofReal
            (hiddenWordWalshDensity n B d hfit h hz y))).map
              (fun y => (hz.1, hz.2, y)))).restrict {x | x.1 = H}).map Prod.snd := by
  rw [conditionalBlockLaw,
    reducedBlockLaw_hidden_word_walsh_representation n B d h q hn hB hd hfit hh hq]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
