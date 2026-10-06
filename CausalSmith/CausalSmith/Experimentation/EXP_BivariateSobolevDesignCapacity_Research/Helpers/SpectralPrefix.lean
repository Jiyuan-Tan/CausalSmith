module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SpectralFrequency

/-! # Stability of finite spectral prefixes

Two-coordinate witnesses bound the complexity of each selected frequency. Frequencies
outside its defining box have strictly greater complexity, so enlarging the box preserves
all earlier entries, including the lexicographic order at ties.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
attribute [local instance] Classical.propDecidable

/-- [ A family of two-coordinate representatives with controlled complexity. -/
-- @node: prefixPairFrequency
def prefixPairFrequency (d m : ℕ) : Fin d → ℤ :=
  fun j => if j.val = 0 then (m + 1 : ℕ) else if j.val = 1 then 1 else 0

/-- The witness family has exactly the first two coordinates in its support.](goal) Under [the stated conditions](hyp:hd). This uses [the stated conclusion](goal). -/
-- @node: prefixPairFrequency_support
lemma prefixPairFrequency_support {d m : ℕ} (hd : 2 ≤ d) :
    frequencySupport (prefixPairFrequency d m) = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
  ext j
  simp only [frequencySupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases h0 : j.val = 0
  · have hj : j = (⟨0, by omega⟩ : Fin d) := Fin.ext h0
    rw [hj]
    simp [prefixPairFrequency]
    omega
  · by_cases h1 : j.val = 1
    · have hj : j = (⟨1, by omega⟩ : Fin d) := Fin.ext h1
      rw [hj]
      simp [prefixPairFrequency]
    · have hn0 : j ≠ (⟨0, by omega⟩ : Fin d) := fun h => h0 (congrArg Fin.val h)
      have hn1 : j ≠ (⟨1, by omega⟩ : Fin d) := fun h => h1 (congrArg Fin.val h)
      simp [prefixPairFrequency, h0, h1, hn0, hn1]

/-- [ The witness family consists of distinct representatives.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: prefixPairFrequency_representative
lemma prefixPairFrequency_representative {d m : ℕ} (hd : 2 ≤ d) :
    IsFrequencyRepresentative (prefixPairFrequency d m) := by
  rw [IsFrequencyRepresentative, prefixPairFrequency_support hd]
  refine ⟨by simp, by simp, ⟨⟨0, by omega⟩, ?_, ?_⟩⟩
  · simp [prefixPairFrequency]
  · intro l hl
    exact False.elim ((Nat.not_lt_zero l.val) hl)

/-- [ Distinct witness sizes give distinct frequencies.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: prefixPairFrequency_injective
lemma prefixPairFrequency_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (prefixPairFrequency d) := by
  intro a b hab
  have h := congrFun hab ⟨0, by omega⟩
  simpa [prefixPairFrequency] using h

/-- [ The first `J` witnesses belong to the radius-`J` frequency box.](goal) Under [the stated conditions](hyp:hm). -/
-- @node: prefixPairFrequency_mem_box
lemma prefixPairFrequency_mem_box {d J m : ℕ} (hm : m < J) :
    prefixPairFrequency d m ∈ frequencyBox d J := by
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro j
  simp only [prefixPairFrequency]
  split_ifs <;> constructor <;> omega

/-- [ The exact witness complexity uses the averaged two-coordinate normalization.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: prefixPairFrequency_complexity
lemma prefixPairFrequency_complexity {d m : ℕ} (hd : 2 ≤ d) :
    frequencyComplexity (prefixPairFrequency d m) = ((m + 1 : ℝ) ^ 2 + 1) / 2 := by
  rw [frequencyComplexity, prefixPairFrequency_support hd]
  have hc2 : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin d)).card = 2 := by simp
  rw [hc2]
  have hsum : (∑ j : Fin d, (prefixPairFrequency d m j : ℝ) ^ 2) =
      ∑ j ∈ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin d)),
        (prefixPairFrequency d m j : ℝ) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hj0 : j.val ≠ 0 := by
      intro h
      apply hj
      exact Finset.mem_insert.mpr (Or.inl (Fin.ext h))
    have hj1 : j.val ≠ 1 := by
      intro h
      apply hj
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext h)))
    simp [prefixPairFrequency, hj0, hj1]
  unfold frequencySq
  rw [hsum]
  simp [prefixPairFrequency]

/-- [ The witness family supplies `J` representatives below a strict outside-box cutoff.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: prefix_low_complexity_card
lemma prefix_low_complexity_card {d J : ℕ} (hd : 2 ≤ d) :
    J ≤ ((frequencyBox d J).filter fun k => IsFrequencyRepresentative k ∧
      frequencyComplexity k ≤ ((J : ℝ) ^ 2 + 1) / 2).card := by
  let A := (Finset.range J).image (prefixPairFrequency d)
  have hc : A.card = J := by
    rw [Finset.card_image_of_injective _ (prefixPairFrequency_injective hd), Finset.card_range]
  calc
    J = A.card := hc.symm
    _ ≤ _ := ?_
  apply Finset.card_le_card
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
  have hmJ : m + 1 ≤ J := by simpa using Finset.mem_range.mp hm
  have hreal : (m + 1 : ℝ) ≤ J := by exact_mod_cast hmJ
  refine Finset.mem_filter.mpr ⟨prefixPairFrequency_mem_box (Finset.mem_range.mp hm),
    prefixPairFrequency_representative hd, ?_⟩
  rw [prefixPairFrequency_complexity hd]
  nlinarith [sq_nonneg ((J : ℝ) - (m + 1 : ℝ))]

/-- Membership in the sorted box is exactly boundedness and representative status. [The asserted mathematical result follows](goal). -/
-- @node: mem_orderedFrequencyBox_iff
lemma mem_orderedFrequencyBox_iff {d J : ℕ} {k : Fin d → ℤ} :
    k ∈ orderedFrequencyBox d J ↔ k ∈ frequencyBox d J ∧ IsFrequencyRepresentative k := by
  unfold orderedFrequencyBox
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp

/-- [ Sorted frequency boxes have no duplicate entries.](goal) -/
-- @node: orderedFrequencyBox_nodup
lemma orderedFrequencyBox_nodup (d J : ℕ) : (orderedFrequencyBox d J).Nodup := by
  unfold orderedFrequencyBox
  exact List.nodup_mergeSort.mpr ((frequencyBox d J).nodup_toList.filter _)

/-- Enough low-complexity witnesses bound the complexity of an indexed sorted entry. Under [the stated conditions](hyp:hd,hiJ,hJK,hi), [the asserted mathematical result follows](goal). -/
-- @node: orderedFrequencyBox_entry_complexity_le
lemma orderedFrequencyBox_entry_complexity_le {d J K i : ℕ} (hd : 2 ≤ d)
    (hiJ : i < J) (hJK : J ≤ K) (hi : i < (orderedFrequencyBox d K).length) :
    frequencyComplexity ((orderedFrequencyBox d K)[i]) ≤ ((J : ℝ) ^ 2 + 1) / 2 := by
  classical
  by_contra h
  have hlt := lt_of_not_ge h
  let A := (frequencyBox d J).filter fun k => IsFrequencyRepresentative k ∧
    frequencyComplexity k ≤ ((J : ℝ) ^ 2 + 1) / 2
  have hsub : A ⊆ ((orderedFrequencyBox d K).take i).toFinset := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hbox, hrep, hbound⟩
    have hboxK : k ∈ frequencyBox d K := by
      simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc] at hbox ⊢
      intro j
      have hj := hbox j
      constructor <;> omega
    have hmem : k ∈ orderedFrequencyBox d K :=
      mem_orderedFrequencyBox_iff.mpr ⟨hboxK, hrep⟩
    rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, hkj⟩
    have hji : j < i := by
      by_contra hji
      have hij : i ≤ j := le_of_not_gt hji
      have horder : frequencyComplexity ((orderedFrequencyBox d K)[i]) ≤
          frequencyComplexity ((orderedFrequencyBox d K)[j]) := by
        rcases hij.eq_or_lt with rfl | hij
        · exact le_rfl
        · exact frequencyComplexity_le_of_frequencyBefore_eq_true
            ((List.pairwise_iff_getElem.mp (orderedFrequencyBox_pairwise_frequencyBefore d K))
              i j hi hj hij)
      rw [hkj] at horder
      exact (not_le_of_gt hlt) (horder.trans hbound)
    apply List.mem_toFinset.mpr
    have ht : j < ((orderedFrequencyBox d K).take i).length := by simp; omega
    have he : ((orderedFrequencyBox d K).take i)[j] = k := by
      simpa using hkj
    exact he ▸ List.getElem_mem ht
  have hc := Finset.card_le_card hsub
  have hcard : (((orderedFrequencyBox d K).take i).toFinset).card = i := by
    rw [List.toFinset_card_of_nodup ((orderedFrequencyBox_nodup d K).take (i := i)),
      List.length_take]
    exact min_eq_left hi.le
  rw [hcard] at hc
  have hw := prefix_low_complexity_card (J := J) hd
  change J ≤ A.card at hw
  omega

/-- [ Any supported representative outside a box exceeds the witness cutoff strictly.](goal) Under [the stated conditions](hyp:hJ,hk,hout). -/
-- @node: outside_frequencyBox_complexity_gt
lemma outside_frequencyBox_complexity_gt {d J : ℕ} (hJ : 0 < J)
    {k : Fin d → ℤ} (hk : IsFrequencyRepresentative k) (hout : k ∉ frequencyBox d J) :
    ((J : ℝ) ^ 2 + 1) / 2 < frequencyComplexity k := by
  have hex : ∃ j : Fin d, ¬ (-(J : ℤ) ≤ k j ∧ k j ≤ J) := by
    simpa only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] using hout
  rcases hex with ⟨j, hj⟩
  have hcoord : ((J + 1 : ℕ) : ℝ) ^ 2 ≤ (k j : ℝ) ^ 2 := by
    have hz : (J + 1 : ℤ) ≤ k j ∨ k j ≤ -(J + 1 : ℤ) := by omega
    rcases hz with hz | hz
    · have hz' : (J : ℝ) + 1 ≤ k j := by exact_mod_cast hz
      push_cast
      nlinarith [sq_nonneg ((k j : ℝ) - ((J : ℝ) + 1))]
    · have hz' : (k j : ℝ) ≤ -((J : ℝ) + 1) := by exact_mod_cast hz
      push_cast
      nlinarith [sq_nonneg ((k j : ℝ) + ((J : ℝ) + 1))]
  have hsum : (k j : ℝ) ^ 2 ≤ frequencySq k :=
    Finset.single_le_sum (fun l _ => sq_nonneg (k l : ℝ)) (Finset.mem_univ j)
  have hcpos : 0 < ((frequencySupport k).card : ℝ) := by exact_mod_cast hk.1
  have hctwo : ((frequencySupport k).card : ℝ) ≤ 2 := by exact_mod_cast hk.2.1
  have hJ' : 0 < (J : ℝ) := by exact_mod_cast hJ
  unfold frequencyComplexity
  apply (lt_div_iff₀ hcpos).mpr
  have hcut : 0 ≤ ((J : ℝ) ^ 2 + 1) / 2 := by positivity
  have hprod := mul_le_mul_of_nonneg_left hctwo hcut
  push_cast at hcoord
  nlinarith

/-- [ Enlarging a box leaves its low-complexity sorted portion unchanged.](goal) Under [the stated conditions](hyp:hJ,hJK). -/
-- @node: orderedFrequencyBox_low_filter_eq
lemma orderedFrequencyBox_low_filter_eq {d J K : ℕ} (hJ : 0 < J) (hJK : J ≤ K) :
    (orderedFrequencyBox d J).filter
      (fun k => decide (frequencyComplexity k ≤ ((J : ℝ) ^ 2 + 1) / 2)) =
    (orderedFrequencyBox d K).filter
      (fun k => decide (frequencyComplexity k ≤ ((J : ℝ) ^ 2 + 1) / 2)) := by
  classical
  let R := fun a b : Fin d → ℤ => frequencyBefore a b = true
  let : Std.Irrefl R := ⟨fun a h => by simp [R, frequencyBefore_self_eq_false] at h⟩
  let : Std.Antisymm R := ⟨fun a b hab hba => by
    have h := frequencyBefore_transitive a b a hab hba
    simp [frequencyBefore_self_eq_false] at h⟩
  apply List.Pairwise.eq_of_mem_iff
    ((orderedFrequencyBox_pairwise_frequencyBefore d J).filter _)
    ((orderedFrequencyBox_pairwise_frequencyBefore d K).filter _)
  intro k
  simp only [List.mem_filter, mem_orderedFrequencyBox_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hk, hr⟩, hc⟩
    refine ⟨⟨?_, hr⟩, hc⟩
    simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc] at hk ⊢
    intro j
    have hj := hk j
    constructor <;> omega
  · rintro ⟨⟨_, hr⟩, hc⟩
    refine ⟨⟨?_, hr⟩, hc⟩
    by_contra hout
    exact (not_le_of_gt (outside_frequencyBox_complexity_gt hJ hr hout)) hc

/-- [ Filtering a list preserves an index if all entries up to that index pass the test.](goal) Under [the stated conditions](hyp:hi,hp). -/
-- @node: getElem_filter_eq_of_prefix
lemma getElem_filter_eq_of_prefix {α : Type*} (p : α → Bool) (l : List α) (i : ℕ)
    (hi : i < l.length) (hp : ∀ j (hj : j < l.length), j ≤ i → p l[j] = true) :
    ∃ hif : i < (l.filter p).length, (l.filter p)[i]'hif = l[i] := by
  induction i generalizing l with
  | zero =>
    cases l with
    | nil => simp at hi
    | cons a l =>
      have ha : p a = true := hp 0 (by simp) le_rfl
      simp only [List.filter_cons, ha, ite_true]
      exact ⟨by simp, rfl⟩
  | succ i ih =>
    cases l with
    | nil => simp at hi
    | cons a l =>
      have ha : p a = true := hp 0 (by simp) (Nat.zero_le _)
      have hi' : i < l.length := by simpa using hi
      have hp' : ∀ j (hj : j < l.length), j ≤ i → p l[j] = true := by
        intro j hj hji
        exact hp (j + 1) (by simpa using hj) (by omega)
      rcases ih l hi' hp' with ⟨hif, heq⟩
      simp only [List.filter_cons, ha, ite_true]
      exact ⟨by simpa using hif, heq⟩

/-- [ Every selected frequency has exactly the same index in every larger box.](goal) Under [the stated conditions](hyp:hd,hK). -/
-- @node: featureFrequency_eq_getElem_larger_box
lemma featureFrequency_eq_getElem_larger_box {d i K : ℕ} (hd : 2 ≤ d)
    (hK : i + 1 ≤ K) :
    ∃ hiK : i < (orderedFrequencyBox d K).length,
      featureFrequency d i = (orderedFrequencyBox d K)[i]'hiK := by
  let p := fun k : Fin d → ℤ =>
    decide (frequencyComplexity k ≤ (((i + 1 : ℕ) : ℝ) ^ 2 + 1) / 2)
  have hiJ := featureFrequency_index_lt (d := d) (index := i) (by omega)
  have hiK : i < (orderedFrequencyBox d K).length :=
    lt_of_lt_of_le (by omega : i < K) (orderedFrequencyBox_length_ge (by omega))
  have hpJ : ∀ j (hj : j < (orderedFrequencyBox d (i + 1)).length),
      j ≤ i → p ((orderedFrequencyBox d (i + 1))[j]) = true := by
    intro j hj hji
    apply decide_eq_true
    have hb := orderedFrequencyBox_entry_complexity_le hd (by omega : j < i + 1) le_rfl hj
    linarith
  have heqfilter : (orderedFrequencyBox d (i + 1)).filter p =
      (orderedFrequencyBox d K).filter p := by
    exact orderedFrequencyBox_low_filter_eq (d := d) (by omega : 0 < i + 1) hK
  rcases getElem_filter_eq_of_prefix p _ i hiJ hpJ with ⟨hifJ, heqJ⟩
  have hbK := orderedFrequencyBox_entry_complexity_le hd
    (by omega : i < i + 1) hK hiK
  have hpK : ∀ j (hj : j < (orderedFrequencyBox d K).length),
      j ≤ i → p ((orderedFrequencyBox d K)[j]) = true := by
    intro j hj hji
    apply decide_eq_true
    have hjb : frequencyComplexity ((orderedFrequencyBox d K)[j]) ≤
        frequencyComplexity ((orderedFrequencyBox d K)[i]) := by
      rcases hji.eq_or_lt with rfl | hji
      · exact le_rfl
      · exact frequencyComplexity_le_of_frequencyBefore_eq_true
          ((List.pairwise_iff_getElem.mp (orderedFrequencyBox_pairwise_frequencyBefore d K))
            j i hj hiK hji)
    linarith
  rcases getElem_filter_eq_of_prefix p _ i hiK hpK with ⟨hifK, heqK⟩
  refine ⟨hiK, ?_⟩
  rw [featureFrequency_eq_getElem (by omega), ← heqJ]
  simpa only [heqfilter] using heqK

/-- [ The indexed frequency sequence is strictly sorted globally, including ties.](goal) Under [the stated conditions](hyp:hd,hij). -/
-- @node: featureFrequency_strict_order
lemma featureFrequency_strict_order {d i j : ℕ} (hd : 2 ≤ d) (hij : i < j) :
    frequencyBefore (featureFrequency d i) (featureFrequency d j) = true := by
  rcases featureFrequency_eq_getElem_larger_box hd (by omega : i + 1 ≤ j + 1) with
    ⟨hi, hei⟩
  rw [hei, featureFrequency_eq_getElem (by omega)]
  exact (List.pairwise_iff_getElem.mp (orderedFrequencyBox_pairwise_frequencyBefore d (j + 1)))
    i j hi (featureFrequency_index_lt (by omega)) hij

/-- [ Global prefix stability prevents any frequency from being enumerated twice.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: featureFrequency_injective
lemma featureFrequency_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (featureFrequency d) := by
  intro i j heq
  rcases lt_trichotomy i j with hij | hij | hji
  · have h := featureFrequency_strict_order hd hij
    rw [heq, frequencyBefore_self_eq_false] at h
    contradiction
  · exact hij
  · have h := featureFrequency_strict_order hd hji
    rw [heq, frequencyBefore_self_eq_false] at h
    contradiction

/-- Every finite integer frequency lies in a positive-radius box. [The asserted mathematical result follows](goal). -/
-- @node: frequency_mem_positive_box
lemma frequency_mem_positive_box {d : ℕ} (k : Fin d → ℤ) :
    ∃ J : ℕ, 0 < J ∧ k ∈ frequencyBox d J := by
  let J := ∑ j : Fin d, (k j).natAbs
  refine ⟨J + 1, by omega, ?_⟩
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le]
  intro j
  have hj : (k j).natAbs ≤ J :=
    Finset.single_le_sum (fun l _ => Nat.zero_le (k l).natAbs) (Finset.mem_univ j)
  have hj' : (k j).natAbs ≤ J + 1 := by omega
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hj'

/-- In a sorted box, enough entries below a cutoff bound the indexed entry by that cutoff. Under [the stated conditions](hyp:hi,hf), [the asserted mathematical result follows](goal). -/
-- @node: orderedFrequencyBox_entry_le_of_filter_length
lemma orderedFrequencyBox_entry_le_of_filter_length {d J i : ℕ} {c : ℝ}
    (hi : i < (orderedFrequencyBox d J).length)
    (hf : i < ((orderedFrequencyBox d J).filter
      (fun k => decide (frequencyComplexity k ≤ c))).length) :
    frequencyComplexity ((orderedFrequencyBox d J)[i]) ≤ c := by
  classical
  by_contra h
  have hlt := lt_of_not_ge h
  let l := orderedFrequencyBox d J
  let A := (l.filter (fun k => decide (frequencyComplexity k ≤ c))).toFinset
  have hsub : A ⊆ (l.take i).toFinset := by
    intro k hk
    have hmem := List.mem_filter.mp (List.mem_toFinset.mp hk)
    have hc := of_decide_eq_true hmem.2
    rcases List.mem_iff_getElem.mp hmem.1 with ⟨j, hj, hej⟩
    have hji : j < i := by
      by_contra hji
      have hij : i ≤ j := le_of_not_gt hji
      have hb : frequencyComplexity (l[i]) ≤ frequencyComplexity (l[j]) := by
        rcases hij.eq_or_lt with rfl | hij
        · exact le_rfl
        · exact frequencyComplexity_le_of_frequencyBefore_eq_true
            ((List.pairwise_iff_getElem.mp (orderedFrequencyBox_pairwise_frequencyBefore d J))
              i j hi hj hij)
      rw [hej] at hb
      exact (not_le_of_gt hlt) (hb.trans hc)
    apply List.mem_toFinset.mpr
    have ht : j < (l.take i).length := by simp; omega
    have he : (l.take i)[j] = k := by simpa using hej
    exact he ▸ List.getElem_mem ht
  have hc := Finset.card_le_card hsub
  have hleft : A.card = (l.filter (fun k => decide (frequencyComplexity k ≤ c))).length :=
    List.toFinset_card_of_nodup ((orderedFrequencyBox_nodup d J).filter _)
  have hright : (l.take i).toFinset.card = i := by
    rw [List.toFinset_card_of_nodup ((orderedFrequencyBox_nodup d J).take (i := i)),
      List.length_take]
    exact min_eq_left hi.le
  rw [hleft, hright] at hc
  exact (not_le_of_gt hf) hc

/-- [ The indexed sequence enumerates every prescribed representative.](goal) Under [the stated conditions](hyp:hd,hk). -/
-- @node: featureFrequency_surjective_representatives
lemma featureFrequency_surjective_representatives {d : ℕ} (hd : 2 ≤ d)
    (k : Fin d → ℤ) (hk : IsFrequencyRepresentative k) :
    ∃ i : ℕ, featureFrequency d i = k := by
  rcases frequency_mem_positive_box k with ⟨R, hR, hkR⟩
  -- Choose a radius also large enough that the entire predecessor set is inside the box.
  let J := max R (Nat.ceil (frequencySq k) + 2)
  have hRJ : R ≤ J := le_max_left _ _
  have hJ : 0 < J := lt_of_lt_of_le hR hRJ
  have hkJ : k ∈ frequencyBox d J := by
    simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc] at hkR ⊢
    intro l
    have hl := hkR l
    constructor <;> omega
  have hsum : 0 ≤ frequencySq k := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcc : frequencyComplexity k ≤ frequencySq k := by
    have hc : (1 : ℝ) ≤ (frequencySupport k).card := by exact_mod_cast hk.1
    unfold frequencyComplexity
    exact div_le_self hsum hc
  have hceil : frequencySq k ≤ (Nat.ceil (frequencySq k) : ℝ) := Nat.le_ceil _
  have hrad : (Nat.ceil (frequencySq k) : ℝ) + 2 ≤ J := by
    exact_mod_cast (le_max_right R (Nat.ceil (frequencySq k) + 2))
  have hcut : frequencyComplexity k ≤ ((J : ℝ) ^ 2 + 1) / 2 := by
    nlinarith [sq_nonneg ((J : ℝ) - 1)]
  have hmem : k ∈ orderedFrequencyBox d J := mem_orderedFrequencyBox_iff.mpr ⟨hkJ, hk⟩
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hei⟩
  let K := max J (i + 1)
  have hJK : J ≤ K := le_max_left _ _
  let p := fun l : Fin d → ℤ => decide (frequencyComplexity l ≤ ((J : ℝ) ^ 2 + 1) / 2)
  have hp : ∀ j (hj : j < (orderedFrequencyBox d J).length),
      j ≤ i → p ((orderedFrequencyBox d J)[j]) = true := by
    intro j hj hji
    apply decide_eq_true
    have hb : frequencyComplexity ((orderedFrequencyBox d J)[j]) ≤ frequencyComplexity k := by
      rcases hji.eq_or_lt with rfl | hji
      · rw [hei]
      · have ho := frequencyComplexity_le_of_frequencyBefore_eq_true
          ((List.pairwise_iff_getElem.mp (orderedFrequencyBox_pairwise_frequencyBefore d J))
            j i hj hi hji)
        simpa only [hei] using ho
    exact hb.trans hcut
  rcases getElem_filter_eq_of_prefix p _ i hi hp with ⟨hif, hef⟩
  have heqf : (orderedFrequencyBox d J).filter p = (orderedFrequencyBox d K).filter p :=
    orderedFrequencyBox_low_filter_eq hJ hJK
  have hifK : i < ((orderedFrequencyBox d K).filter p).length := by
    simpa only [← heqf] using hif
  have hKi : i < (orderedFrequencyBox d K).length :=
    lt_of_lt_of_le hifK (List.length_filter_le _ _)
  -- The selected index in the larger box is the same low-frequency filtered index.
  have hpK : ∀ j (hj : j < (orderedFrequencyBox d K).length),
      j ≤ i → p ((orderedFrequencyBox d K)[j]) = true := by
    intro j hj hji
    apply decide_eq_true
    have hlast : frequencyComplexity ((orderedFrequencyBox d K)[i]) ≤
        ((J : ℝ) ^ 2 + 1) / 2 := by
      exact orderedFrequencyBox_entry_le_of_filter_length hKi hifK
    have hb : frequencyComplexity ((orderedFrequencyBox d K)[j]) ≤
        frequencyComplexity ((orderedFrequencyBox d K)[i]) := by
      rcases hji.eq_or_lt with rfl | hji
      · exact le_rfl
      · exact frequencyComplexity_le_of_frequencyBefore_eq_true
          ((List.pairwise_iff_getElem.mp (orderedFrequencyBox_pairwise_frequencyBefore d K))
            j i hj hKi hji)
    exact hb.trans hlast
  rcases getElem_filter_eq_of_prefix p _ i hKi hpK with ⟨_, hefK⟩
  rcases featureFrequency_eq_getElem_larger_box hd (le_max_right J (i + 1)) with ⟨_, heK⟩
  refine ⟨i, heK.trans ?_⟩
  rw [← hefK]
  simpa only [← heqf, hef] using hei

/-- [ A single finite box computes exactly the entire global prefix requested by rounding.](goal) Under [the stated conditions](hyp:hd,hNJ). -/
-- @node: featureFrequency_prefix_eq_take
lemma featureFrequency_prefix_eq_take {d N J : ℕ} (hd : 2 ≤ d) (hNJ : N ≤ J) :
    List.ofFn (fun i : Fin N => featureFrequency d i.val) =
      (orderedFrequencyBox d J).take N := by
  have hlen : N ≤ (orderedFrequencyBox d J).length :=
    hNJ.trans (orderedFrequencyBox_length_ge (by omega))
  apply List.ext_getElem
  · simp [List.length_take, min_eq_left hlen]
  · intro i hi₁ hi₂
    have hiN : i < N := by simpa using hi₁
    rcases featureFrequency_eq_getElem_larger_box hd (by omega : i + 1 ≤ J) with
      ⟨hiJ, heq⟩
    simpa only [List.getElem_ofFn, List.getElem_take] using heq

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
