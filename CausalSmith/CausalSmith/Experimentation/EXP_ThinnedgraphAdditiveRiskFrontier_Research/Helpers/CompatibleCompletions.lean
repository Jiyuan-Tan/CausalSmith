module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.PosteriorResponseBridge

/-!
# Compatible partitions as capacity-constrained hidden-label words

Restriction to the original unrevealed source labels is a bijection between
compatible source partitions and words with the observed remaining row capacities.
The inverse fixes every revealed label at its observed row. Detailed retained
edge subsets remain in the compatibility predicate throughout.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Compatible completions of the entire detailed retained graph. -/
-- @node: CompatiblePartition
abbrev CompatiblePartition (n B d : ℕ) (H : OffDiag (Fin n) → Bool) :=
  {s : SourcePartition B d // ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2}

/-- Original source labels whose association was not revealed. -/
-- @node: HiddenSource
abbrev HiddenSource (n B d : ℕ) (H : OffDiag (Fin n) → Bool) :=
  {j : Fin (B * d) // sourceReveals n B d H j = false}

/-- Row words on original hidden labels with exactly the remaining row capacities. -/
-- @node: HiddenCompletion
abbrev HiddenCompletion (n B d : ℕ) (H : OffDiag (Fin n) → Bool) :=
  {g : HiddenSource n B d H → Fin B // ∀ ℓ,
    (Finset.univ.filter (fun j => g j = ℓ)).card = capacity n B d H ℓ}

/-- The Boolean reveal statistic is false exactly when the original label has no retained edge.  [For the stated data and conditions](hyp:n,B,d,H,j,hj), [the stated conclusion holds](goal). -/
-- @node: sourceReveals_false_iff
lemma sourceReveals_false_iff (n B d : ℕ) (H : OffDiag (Fin n) → Bool)
    (j : Fin n) (hj : j.val < B * d) :
    sourceReveals n B d H ⟨j.val, hj⟩ = false ↔
      ¬ ∃ i : Fin n, ∃ hji : j ≠ i, H ⟨(j,i),hji⟩ = true := by
  simp only [sourceReveals, decide_eq_false_iff_not]
  constructor
  · intro hn he
    exact hn ⟨j, rfl, he⟩
  · intro hn
    rintro ⟨v, hv, he⟩
    have hvj : v = j := Fin.ext hv
    subst v
    exact hn he

/-- Any two compatible completions agree on every revealed original source label.  [For the stated data and conditions](hyp:n,B,d,H,s,t,j,hj), [the stated conclusion holds](goal). -/
-- @node: compatiblePartition_agree_revealed
lemma compatiblePartition_agree_revealed (n B d : ℕ)
    (H : OffDiag (Fin n) → Bool) (s t : CompatiblePartition n B d H)
    (j : Fin (B * d)) (hj : sourceReveals n B d H j ≠ false) : s.1.1 j = t.1.1 j := by
  have hj' : ∃ v : Fin n, v.val = j.val ∧
      ∃ i : Fin n, ∃ hvi : v ≠ i, H ⟨(v,i),hvi⟩ = true := by
    by_contra hn
    exact hj (by simp [sourceReveals, hn])
  obtain ⟨v, hv, i, hvi, he⟩ := hj'
  obtain ⟨⟨hs, ℓ, hsℓ, hiℓ⟩, _⟩ := s.2 ⟨(v,i),hvi⟩ he
  obtain ⟨⟨ht, k, htk, hik⟩, _⟩ := t.2 ⟨(v,i),hvi⟩ he
  have hsj : (⟨v.val, hs⟩ : Fin (B * d)) = j := Fin.ext hv
  have htj : (⟨v.val, ht⟩ : Fin (B * d)) = j := Fin.ext hv
  rw [hsj] at hsℓ
  rw [htj] at htk
  exact hsℓ.trans ((recipientBlock_unique n B d i ℓ k hiℓ hik).trans htk.symm)

/-- Restricting a compatible partition to original hidden labels gives the observed capacity.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s,ℓ), [the stated conclusion holds](goal). -/
-- @node: compatiblePartition_hidden_fiber_card
lemma compatiblePartition_hidden_fiber_card (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (H : OffDiag (Fin n) → Bool)
    (s : CompatiblePartition n B d H) (ℓ : Fin B) :
    (Finset.univ.filter (fun j : HiddenSource n B d H => s.1.1 j.1 = ℓ)).card =
      capacity n B d H ℓ := by
  let e : {j : HiddenSource n B d H // s.1.1 j.1 = ℓ} ≃
      {j : Fin n // j ∈ partitionHiddenLabels n B d s.1 H ℓ} := {
    toFun := fun j => ⟨⟨j.1.1.val, by have := j.1.1.isLt; omega⟩,
      (partitionHiddenLabels_mem_iff n B d s.1 H s.2 ℓ _).mpr
        ⟨⟨j.1.1.isLt, j.2⟩,
          (sourceReveals_false_iff n B d H _ j.1.1.isLt).mp j.1.2⟩⟩
    invFun := fun j =>
      let hj := (partitionHiddenLabels_mem_iff n B d s.1 H s.2 ℓ j.1).mp j.2
      ⟨⟨⟨j.1.val, hj.1.choose⟩,
        (sourceReveals_false_iff n B d H j.1 hj.1.choose).mpr hj.2⟩, hj.1.choose_spec⟩
    left_inv := by intro j; rfl
    right_inv := by intro j; rfl }
  have hc := Fintype.card_congr e
  simpa [Fintype.card_subtype, partitionHiddenLabels_card n B d hfit s.1 H s.2 ℓ]
    using hc

/-- The actual hidden word of a compatible completion. -/
-- @node: compatiblePartitionRestriction
def compatiblePartitionRestriction (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s : CompatiblePartition n B d H) :
    HiddenCompletion n B d H :=
  ⟨fun j => s.1.1 j.1, compatiblePartition_hidden_fiber_card n B d hfit H s⟩

/-- Extend a hidden word by keeping all revealed labels at their observed row. -/
-- @node: hiddenCompletionExtension
def hiddenCompletionExtension (n B d : ℕ) (H : OffDiag (Fin n) → Bool)
    (s₀ : CompatiblePartition n B d H) (g : HiddenCompletion n B d H) :
    Fin (B * d) → Fin B :=
  fun j => if hj : sourceReveals n B d H j = false then g.1 ⟨j,hj⟩ else s₀.1.1 j

/-- Restriction along a subtype preserves the cardinality of the corresponding filtered set.  [For the stated data and conditions](hyp:n,B,d,H,f,ℓ), [the stated conclusion holds](goal). -/
-- @node: hiddenSource_filter_card
lemma hiddenSource_filter_card (n B d : ℕ) (H : OffDiag (Fin n) → Bool)
    (f : Fin (B * d) → Fin B) (ℓ : Fin B) :
    ((Finset.univ.filter (fun j => f j = ℓ)).filter
      (fun j => sourceReveals n B d H j = false)).card =
    (Finset.univ.filter (fun j : HiddenSource n B d H => f j.1 = ℓ)).card := by
  let e : {j : Fin (B * d) // f j = ℓ ∧ sourceReveals n B d H j = false} ≃
      {j : HiddenSource n B d H // f j.1 = ℓ} := {
    toFun := fun j => ⟨⟨j.1,j.2.2⟩,j.2.1⟩
    invFun := fun j => ⟨j.1.1,j.2,j.1.2⟩
    left_inv := by intro j; rfl
    right_inv := by intro j; rfl }
  simpa only [Fintype.card_subtype, Finset.filter_filter] using Fintype.card_congr e

/-- The extended word still assigns exactly d original source labels to each row.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s₀,g,ℓ), [the stated conclusion holds](goal). -/
-- @node: hiddenCompletionExtension_fiber_card
lemma hiddenCompletionExtension_fiber_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s₀ : CompatiblePartition n B d H)
    (g : HiddenCompletion n B d H) (ℓ : Fin B) :
    (Finset.univ.filter (fun j => hiddenCompletionExtension n B d H s₀ g j = ℓ)).card = d := by
  have hc (f : Fin (B * d) → Fin B) :=
    Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun j => f j = ℓ))
      (fun j => sourceReveals n B d H j = false)
  have hh : ((Finset.univ.filter (fun j =>
      hiddenCompletionExtension n B d H s₀ g j = ℓ)).filter
        (fun j => sourceReveals n B d H j = false)).card = capacity n B d H ℓ := by
    rw [hiddenSource_filter_card]
    have he (j : HiddenSource n B d H) :
        hiddenCompletionExtension n B d H s₀ g j.1 = g.1 j := dif_pos j.2
    simpa only [he] using g.2 ℓ
  have hh₀ : ((Finset.univ.filter (fun j => s₀.1.1 j = ℓ)).filter
      (fun j => sourceReveals n B d H j = false)).card = capacity n B d H ℓ := by
    rw [hiddenSource_filter_card]
    exact compatiblePartition_hidden_fiber_card n B d hfit H s₀ ℓ
  have hr : (Finset.univ.filter (fun j =>
      hiddenCompletionExtension n B d H s₀ g j = ℓ)).filter
        (fun j => ¬ sourceReveals n B d H j = false) =
      (Finset.univ.filter (fun j => s₀.1.1 j = ℓ)).filter
        (fun j => ¬ sourceReveals n B d H j = false) := by
    ext j
    by_cases hj : sourceReveals n B d H j = false <;>
      simp [hiddenCompletionExtension, hj]
  have h₀ := hc s₀.1.1
  have h := hc (hiddenCompletionExtension n B d H s₀ g)
  rw [hh₀, s₀.1.2 ℓ] at h₀
  rw [hh, hr] at h
  omega

/-- Extension is compatible with every detailed retained edge. -/
-- @node: hiddenCompletionPartition
def hiddenCompletionPartition (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s₀ : CompatiblePartition n B d H)
    (g : HiddenCompletion n B d H) : CompatiblePartition n B d H :=
  ⟨⟨hiddenCompletionExtension n B d H s₀ g,
      hiddenCompletionExtension_fiber_card n B d hfit H s₀ g⟩, by
    intro e he
    obtain ⟨⟨hj, ℓ, hs, hi⟩, hne⟩ := s₀.2 e he
    refine ⟨⟨hj, ℓ, ?_, hi⟩, hne⟩
    have hr : sourceReveals n B d H ⟨e.val.1.val,hj⟩ ≠ false := by
      intro hr
      exact (sourceReveals_false_iff n B d H e.val.1 hj).mp hr
        ⟨e.val.2,e.2,he⟩
    simpa only [hiddenCompletionExtension, dif_neg hr] using hs⟩

/-- Compatible partitions and capacity-constrained words on the original hidden labels
are in bijection; every revealed source remains fixed. -/
-- @node: compatiblePartitionEquivHiddenCompletion
def compatiblePartitionEquivHiddenCompletion (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s₀ : CompatiblePartition n B d H) :
    CompatiblePartition n B d H ≃ HiddenCompletion n B d H where
  toFun := compatiblePartitionRestriction n B d hfit H
  invFun := hiddenCompletionPartition n B d hfit H s₀
  left_inv := by
    intro s
    apply Subtype.ext
    apply Subtype.ext
    funext j
    change (if hj : sourceReveals n B d H j = false then s.1.1 j else s₀.1.1 j) = s.1.1 j
    split_ifs with hj
    · rfl
    · exact compatiblePartition_agree_revealed n B d H s₀ s j hj
  right_inv := by
    intro g
    apply Subtype.ext
    funext j
    exact dif_pos j.2

/-- Reindex the uniform compatible-partition average by actual hidden-label words.  [For the stated data and conditions](hyp:α,n,B,d,hfit,H,s₀,F), [the stated conclusion holds](goal). -/
-- @node: compatiblePartition_average_eq_hiddenCompletion
lemma compatiblePartition_average_eq_hiddenCompletion {α : Type*} [MeasurableSpace α]
    (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (H : OffDiag (Fin n) → Bool)
    (s₀ : CompatiblePartition n B d H) (F : CompatiblePartition n B d H → Measure α) :
    (Fintype.card (CompatiblePartition n B d H) : ℝ≥0∞)⁻¹ • (∑ s, F s) =
      (Fintype.card (HiddenCompletion n B d H) : ℝ≥0∞)⁻¹ •
        (∑ g : HiddenCompletion n B d H, F (hiddenCompletionPartition n B d hfit H s₀ g)) := by
  let e := compatiblePartitionEquivHiddenCompletion n B d hfit H s₀
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e F (fun g => F (e.symm g)) (fun s => by simp)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
