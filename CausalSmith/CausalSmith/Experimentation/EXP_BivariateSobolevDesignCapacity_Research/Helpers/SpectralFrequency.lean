module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CapacityHandle
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Sort
-- private import
import all Init.Data.List.Sort.Basic

/-! # Elementary properties of the ordered spectral frequencies

The positive frequencies on the first coordinate supply an explicit finite family inside
every sufficiently large frequency box.  This proves that the ordered prefix lookup is in
range and hence that every selected frequency is a nonzero representative supported on at
most two coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
attribute [local instance] Classical.propDecidable

/-- The positive frequency of size `m + 1` on the first coordinate. -/
@[no_expose]
def firstCoordinateFrequency (d m : ℕ) : Fin d → ℤ :=
  fun j => if j.val = 0 then (m + 1 : ℕ) else 0

/-- In positive dimension, the first-coordinate frequency has singleton support. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma frequencySupport_firstCoordinateFrequency {d m : ℕ} (hd : 0 < d) :
    frequencySupport (firstCoordinateFrequency d m) = {⟨0, hd⟩} := by
  ext j
  by_cases hj : j.val = 0
  · have heq : j = (⟨0, hd⟩ : Fin d) := Fin.ext hj
    subst j
    simp [frequencySupport, firstCoordinateFrequency]
    omega
  · have hne : j ≠ (⟨0, hd⟩ : Fin d) := fun h => hj (congrArg Fin.val h)
    simp [frequencySupport, firstCoordinateFrequency, hj, hne]

/-- In positive dimension, every first-coordinate frequency is a prescribed representative. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma firstCoordinateFrequency_isRepresentative {d m : ℕ} (hd : 0 < d) :
    IsFrequencyRepresentative (firstCoordinateFrequency d m) := by
  rw [IsFrequencyRepresentative, frequencySupport_firstCoordinateFrequency hd]
  refine ⟨by simp, by simp, ⟨⟨0, hd⟩, ?_, ?_⟩⟩
  · simp [firstCoordinateFrequency]
  · intro l hl
    exact False.elim ((Nat.not_lt_zero l.val) hl)

/-- Frequencies of distinct positive sizes on the first coordinate are distinct. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma firstCoordinateFrequency_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (firstCoordinateFrequency d) := by
  intro a b hab
  have h := congrFun hab ⟨0, hd⟩
  simpa [firstCoordinateFrequency] using h

/-- The first `J` positive first-coordinate frequencies lie in the radius-`J` box. This uses [the hm hypothesis](hyp:hm), [the stated conclusion](goal). -/
lemma firstCoordinateFrequency_mem_frequencyBox {d J m : ℕ} (hm : m < J) :
    firstCoordinateFrequency d m ∈ frequencyBox d J := by
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro j
  simp only [firstCoordinateFrequency]
  split_ifs
  · constructor
    · omega
    · exact_mod_cast Nat.succ_le_iff.mpr hm
  · constructor <;> omega

/-- The strict spectral comparator is false on equal frequencies. This uses [the stated conclusion](goal). -/
lemma frequencyBefore_self_eq_false {d : ℕ} (k : Fin d → ℤ) :
    frequencyBefore k k = false := by
  simp [frequencyBefore]

-- The following private proofs use the implementation equations made available by
-- `import all Init.Data.List.Sort.Basic`; the public sorting API assumes a reflexive comparator.
private lemma merge_eq_merge_of_cross_eq {α : Type*} (cmp cmp' : α → α → Bool)
    (l₁ l₂ : List α)
    (hcmp : ∀ a ∈ l₁, ∀ b ∈ l₂, cmp a b = cmp' a b) :
    l₁.merge l₂ cmp = l₁.merge l₂ cmp' := by
  cases l₁ with
  | nil => simp only [List.merge.eq_1]
  | cons a as =>
    cases l₂ with
    | nil => rw [List.merge.eq_2 _ _ (by simp), List.merge.eq_2 _ _ (by simp)]
    | cons b bs =>
      rw [List.merge.eq_3, List.merge.eq_3, hcmp a (by simp) b (by simp)]
      split
      · congr 1
        exact merge_eq_merge_of_cross_eq cmp cmp' as (b :: bs)
          (fun x hx y hy => hcmp x (by simp [hx]) y hy)
      · congr 1
        exact merge_eq_merge_of_cross_eq cmp cmp' (a :: as) bs
          (fun x hx y hy => hcmp x hx y (by simp [hy]))
termination_by l₁.length + l₂.length
decreasing_by all_goals simp_all

private lemma mergeSort_eq_mergeSort_of_nodup {α : Type*} (cmp cmp' : α → α → Bool)
    (l : List α) (hnodup : l.Nodup)
    (hcmp : ∀ a b, a ≠ b → cmp a b = cmp' a b) :
    l.mergeSort cmp = l.mergeSort cmp' := by
  cases l with
  | nil => simp only [List.mergeSort_nil]
  | cons a tail =>
    cases tail with
    | nil => simp only [List.mergeSort_singleton]
    | cons b xs =>
      let packed : {l : List α // l.length = (a :: b :: xs).length} :=
        ⟨a :: b :: xs, rfl⟩
      let left := (List.MergeSort.Internal.splitInTwo packed).1.val
      let right := (List.MergeSort.Internal.splitInTwo packed).2.val
      have hleft : left.Nodup := by
        dsimp [left]
        rw [List.MergeSort.Internal.splitInTwo_fst]
        exact hnodup.sublist (List.take_sublist _ _)
      have hright : right.Nodup := by
        dsimp [right]
        rw [List.MergeSort.Internal.splitInTwo_snd]
        exact hnodup.sublist (List.drop_sublist _ _)
      have hdisjoint : left.Disjoint right := by
        dsimp [left, right]
        rw [List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd]
        exact List.disjoint_take_drop hnodup le_rfl
      rw [List.mergeSort.eq_3, List.mergeSort.eq_3]
      rw [mergeSort_eq_mergeSort_of_nodup cmp cmp' left hleft hcmp,
        mergeSort_eq_mergeSort_of_nodup cmp cmp' right hright hcmp]
      apply merge_eq_merge_of_cross_eq
      intro x hx y hy
      apply hcmp
      intro hxy
      have hxl : x ∈ left := (List.mergeSort_perm left cmp').mem_iff.mp hx
      have hyr : y ∈ right := (List.mergeSort_perm right cmp').mem_iff.mp hy
      exact hdisjoint hxl (hxy ▸ hyr)
termination_by l.length
decreasing_by all_goals simp_all [left, right, packed,
  List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd]; omega

@[no_expose]
private def strictComparatorLE {α : Type*} [DecidableEq α]
    (cmp : α → α → Bool) : α → α → Bool :=
  fun a b => decide (a = b) || cmp a b

/-- A transitive strict comparator that compares every pair of distinct entries makes merge sort
strictly pairwise sorted on every noduplicated input. This uses [the htrans hypothesis](hyp:htrans), [the hcompare hypothesis](hyp:hcompare), [the hnodup hypothesis](hyp:hnodup), [the stated conclusion](goal). -/
lemma pairwise_mergeSort_of_nodup_of_strictTotal {α : Type*} [DecidableEq α]
    (cmp : α → α → Bool)
    (htrans : ∀ a b c, cmp a b = true → cmp b c = true → cmp a c = true)
    (hcompare : ∀ a b, a ≠ b → cmp a b = true ∨ cmp b a = true)
    (l : List α) (hnodup : l.Nodup) :
    (l.mergeSort cmp).Pairwise fun a b => cmp a b = true := by
  let cmpLE := strictComparatorLE cmp
  have htransLE : ∀ a b c, cmpLE a b = true → cmpLE b c = true → cmpLE a c = true := by
    intro a b c hab hbc
    simp only [cmpLE, strictComparatorLE, Bool.or_eq_true, decide_eq_true_eq] at hab hbc ⊢
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (htrans _ _ _ hab hbc)
  have htotalLE : ∀ a b, (cmpLE a b || cmpLE b a) = true := by
    intro a b
    by_cases hab : a = b
    · subst b
      simp [cmpLE, strictComparatorLE]
    · rcases hcompare a b hab with hab' | hba'
      · simp [cmpLE, strictComparatorLE, hab']
      · simp [cmpLE, strictComparatorLE, hba']
  have hsortLE := List.pairwise_mergeSort htransLE htotalLE l
  have heq : l.mergeSort cmp = l.mergeSort cmpLE := by
    apply mergeSort_eq_mergeSort_of_nodup cmp cmpLE l hnodup
    intro a b hab
    simp [cmpLE, strictComparatorLE, hab]
  rw [← heq] at hsortLE
  rw [List.pairwise_iff_getElem] at hsortLE ⊢
  intro i j hi hj hij
  have hle := hsortLE i j hi hj hij
  have hne : (l.mergeSort cmp)[i] ≠ (l.mergeSort cmp)[j] := by
    have hout : (l.mergeSort cmp).Nodup := List.nodup_mergeSort.mpr hnodup
    have hpne := List.nodup_iff_pairwise_ne.mp hout
    exact (List.pairwise_iff_getElem.mp hpne) i j hi hj hij
  simp only [cmpLE, strictComparatorLE, Bool.or_eq_true, decide_eq_true_eq] at hle
  exact hle.resolve_left hne

/-- The strict spectral comparator is transitive. This uses [the hab hypothesis](hyp:hab), [the hbc hypothesis](hyp:hbc), [the stated conclusion](goal). -/
lemma frequencyBefore_transitive {d : ℕ} (a b c : Fin d → ℤ)
    (hab : frequencyBefore a b = true) (hbc : frequencyBefore b c = true) :
    frequencyBefore a c = true := by
  apply decide_eq_true
  have hab' := of_decide_eq_true hab
  have hbc' := of_decide_eq_true hbc
  rcases hab' with hab' | ⟨habc, hab'⟩
  · rcases hbc' with hbc' | ⟨hbcc, _⟩
    · exact Or.inl (hab'.trans hbc')
    · exact Or.inl (hbcc ▸ hab')
  · rcases hbc' with hbc' | ⟨hbcc, hbc'⟩
    · exact Or.inl (habc ▸ hbc')
    · have hlex : (List.finRange d).map a < (List.finRange d).map c :=
        lt_trans ((List.lt_iff_lex_lt _ _).mpr hab') ((List.lt_iff_lex_lt _ _).mpr hbc')
      exact Or.inr ⟨habc.trans hbcc, (List.lt_iff_lex_lt _ _).mp hlex⟩

/-- A frequency is determined by its coordinate list. This uses [the stated conclusion](goal). -/
lemma frequencyCoordinateList_injective (d : ℕ) :
    Function.Injective (fun k : Fin d → ℤ => (List.finRange d).map k) := by
  intro k l hkl
  funext i
  have h := congrArg (fun xs : List ℤ => xs.getD i.val 0) hkl
  rw [List.getD_eq_getElem _ _ (by simp [i.isLt]),
    List.getD_eq_getElem _ _ (by simp [i.isLt])] at h
  simp only [List.getElem_map, List.getElem_finRange] at h
  convert h using 1 <;> congr

/-- Distinct frequencies are comparable by the strict spectral comparator. This uses [the hab hypothesis](hyp:hab), [the stated conclusion](goal). -/
lemma frequencyBefore_comparable_of_ne {d : ℕ} (a b : Fin d → ℤ) (hab : a ≠ b) :
    frequencyBefore a b = true ∨ frequencyBefore b a = true := by
  unfold frequencyBefore
  rcases lt_trichotomy (frequencyComplexity a) (frequencyComplexity b) with hlt | heq | hgt
  · exact Or.inl (decide_eq_true (Or.inl hlt))
  · have hlist : (List.finRange d).map a ≠ (List.finRange d).map b :=
      fun h => hab (frequencyCoordinateList_injective d h)
    rcases trichotomous_of (List.Lex (· < ·)) ((List.finRange d).map a)
        ((List.finRange d).map b) with hlex | hsame | hlex
    · exact Or.inl (decide_eq_true (Or.inr ⟨heq, hlex⟩))
    · exact (hlist hsame).elim
    · exact Or.inr (decide_eq_true (Or.inr ⟨heq.symm, hlex⟩))
  · exact Or.inr (decide_eq_true (Or.inl hgt))

/-- Every ordered frequency box is strictly pairwise sorted by the prescribed comparator. This uses [the stated conclusion](goal). -/
lemma orderedFrequencyBox_pairwise_frequencyBefore (d J : ℕ) :
    (orderedFrequencyBox d J).Pairwise fun a b => frequencyBefore a b = true := by
  unfold orderedFrequencyBox
  apply pairwise_mergeSort_of_nodup_of_strictTotal frequencyBefore frequencyBefore_transitive
    frequencyBefore_comparable_of_ne
  exact (frequencyBox d J).nodup_toList.filter _

/-- A frequency placed before another by the spectral comparator has no larger complexity. This uses [the h hypothesis](hyp:h), [the stated conclusion](goal). -/
lemma frequencyComplexity_le_of_frequencyBefore_eq_true {d : ℕ} {k l : Fin d → ℤ}
    (h : frequencyBefore k l = true) :
    frequencyComplexity k ≤ frequencyComplexity l := by
  have horder := of_decide_eq_true h
  rcases horder with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

/-- In positive dimension, the representative part of the radius-`J` box has at least `J`
elements. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma card_representative_frequencyBox_ge {d J : ℕ} (hd : 0 < d) :
    J ≤ ((frequencyBox d J).filter IsFrequencyRepresentative).card := by
  let A := (Finset.range J).image (firstCoordinateFrequency d)
  have hcard : A.card = J := by
    rw [Finset.card_image_of_injective _ (firstCoordinateFrequency_injective hd),
      Finset.card_range]
  have hsub : A ⊆ (frequencyBox d J).filter IsFrequencyRepresentative := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨firstCoordinateFrequency_mem_frequencyBox (Finset.mem_range.mp hm),
      firstCoordinateFrequency_isRepresentative hd⟩
  calc
    J = A.card := hcard.symm
    _ ≤ ((frequencyBox d J).filter IsFrequencyRepresentative).card :=
      Finset.card_le_card hsub

/-- In positive dimension, the ordered radius-`J` box contains at least `J` entries. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma orderedFrequencyBox_length_ge {d J : ℕ} (hd : 0 < d) :
    J ≤ (orderedFrequencyBox d J).length := by
  let l := (frequencyBox d J).toList.filter
    (fun k => decide (IsFrequencyRepresentative k))
  have hnodup : l.Nodup := (frequencyBox d J).nodup_toList.filter _
  have hcard := List.toFinset_card_of_nodup hnodup
  have htoFinset : l.toFinset = (frequencyBox d J).filter IsFrequencyRepresentative := by
    symm
    simpa only [l, Finset.toList_toFinset] using
      (List.filter_toFinset (frequencyBox d J).toList IsFrequencyRepresentative)
  rw [htoFinset] at hcard
  rw [orderedFrequencyBox, List.length_mergeSort, ← hcard]
  exact card_representative_frequencyBox_ge hd

/-- The lookup defining the `index`-th feature frequency is in range in positive dimension. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma featureFrequency_index_lt {d index : ℕ} (hd : 0 < d) :
    index < (orderedFrequencyBox d (index + 1)).length := by
  exact lt_of_lt_of_le (Nat.lt_succ_self index) (orderedFrequencyBox_length_ge hd)

/-- In positive dimension, the feature-frequency lookup never uses its zero fallback. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma featureFrequency_eq_getElem {d index : ℕ} (hd : 0 < d) :
    featureFrequency d index =
      (orderedFrequencyBox d (index + 1))[index]'(featureFrequency_index_lt hd) := by
  unfold featureFrequency
  exact List.getD_eq_getElem _ _ (featureFrequency_index_lt hd)

/-- In positive dimension, every selected feature frequency belongs to its defining box and is
a prescribed representative. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma featureFrequency_mem_frequencyBox_and_isRepresentative {d index : ℕ} (hd : 0 < d) :
    featureFrequency d index ∈ frequencyBox d (index + 1) ∧
      IsFrequencyRepresentative (featureFrequency d index) := by
  have hmem : featureFrequency d index ∈ orderedFrequencyBox d (index + 1) := by
    rw [featureFrequency_eq_getElem hd]
    exact List.getElem_mem (featureFrequency_index_lt hd)
  change featureFrequency d index ∈
    ((frequencyBox d (index + 1)).toList.filter
      (fun k => decide (IsFrequencyRepresentative k))).mergeSort frequencyBefore at hmem
  have hfilter := (List.mergeSort_perm
    ((frequencyBox d (index + 1)).toList.filter
      (fun k => decide (IsFrequencyRepresentative k))) frequencyBefore).mem_iff.mp hmem
  simp only [List.mem_filter, Finset.mem_toList] at hfilter
  exact ⟨hfilter.1, of_decide_eq_true hfilter.2⟩

/-- In positive dimension, every selected feature frequency is a prescribed representative. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma featureFrequency_isRepresentative {d index : ℕ} (hd : 0 < d) :
    IsFrequencyRepresentative (featureFrequency d index) :=
  (featureFrequency_mem_frequencyBox_and_isRepresentative hd).2

/-- Every selected feature frequency has nonempty support. This uses [the hd hypothesis](hyp:hd), [the stated conclusion](goal). -/
lemma featureFrequency_support_nonempty {d index : ℕ} (hd : 0 < d) :
    1 ≤ (frequencySupport (featureFrequency d index)).card :=
  (featureFrequency_isRepresentative hd).1

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
