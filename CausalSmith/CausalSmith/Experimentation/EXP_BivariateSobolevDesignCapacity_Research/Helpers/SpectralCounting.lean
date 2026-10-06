module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SpectralPrefix

/-! # Finite counts through a spectral complexity cutoff

A square-root box contains every supported frequency below a given complexity.
The resulting finite count bounds the global indices of both real rows, including ties.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
attribute [local instance] Classical.propDecidable

/-- [ Each coordinate of a supported frequency is bounded by its averaged energy.](goal) Under [the stated conditions](hyp:hk). -/
-- @node: frequency_coordinate_sq_le_two_complexity
lemma frequency_coordinate_sq_le_two_complexity {d : ℕ} {k : Fin d → ℤ}
    (hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2)
    (j : Fin d) : (k j : ℝ) ^ 2 ≤ 2 * frequencyComplexity k := by
  have hpos : 0 < ((frequencySupport k).card : ℝ) := by exact_mod_cast hk.1
  have htwo : ((frequencySupport k).card : ℝ) ≤ 2 := by exact_mod_cast hk.2
  have hnonneg : 0 ≤ frequencyComplexity k := by
    unfold frequencyComplexity frequencySq
    positivity
  have heq : frequencyComplexity k * (frequencySupport k).card = frequencySq k := by
    exact div_mul_cancel₀ _ (ne_of_gt hpos)
  have hsingle : (k j : ℝ) ^ 2 ≤ frequencySq k :=
    Finset.single_le_sum (fun l _ => sq_nonneg (k l : ℝ)) (Finset.mem_univ j)
  nlinarith [mul_le_mul_of_nonneg_left htwo hnonneg]

/-- [ The square-root box contains every frequency of support one or two below the cutoff.](goal) Under [the stated conditions](hyp:hk,hu). -/
-- @node: frequency_mem_complexity_box
lemma frequency_mem_complexity_box {d : ℕ} {k : Fin d → ℤ} {u : ℝ}
    (hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2)
    (hu : frequencyComplexity k ≤ u) :
    k ∈ frequencyBox d (Nat.ceil (Real.sqrt (2 * u))) := by
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le]
  intro j
  have hs : (k j : ℝ) ^ 2 ≤ 2 * u :=
    (frequency_coordinate_sq_le_two_complexity hk j).trans (by linarith)
  have hb := (Real.abs_le_sqrt hs).trans (Nat.le_ceil (Real.sqrt (2 * u)))
  exact_mod_cast hb

/-- [ Integer magnitudes respect the floor of the real square-root bound.](goal) Under [the stated conditions](hyp:h). -/
-- @node: frequency_natAbs_le_floor_sqrt
lemma frequency_natAbs_le_floor_sqrt {a : ℤ} {v : ℝ} (h : (a : ℝ) ^ 2 ≤ v) :
    a.natAbs ≤ Nat.floor (Real.sqrt v) := by
  apply (Nat.le_floor_iff (Real.sqrt_nonneg v)).mpr
  have hb : ((|a| : ℤ) : ℝ) ≤ Real.sqrt v := by exact_mod_cast Real.abs_le_sqrt h
  rw [Int.abs_eq_natAbs] at hb
  simpa only [Int.cast_natCast] using hb

/-- [ A support-one frequency has exactly its single coordinate's squared complexity.](goal) Under [the stated conditions](hyp:hj). -/
-- @node: frequencyComplexity_single_support
lemma frequencyComplexity_single_support {d : ℕ} {k : Fin d → ℤ} {j : Fin d}
    (hj : frequencySupport k = {j}) : frequencyComplexity k = (k j : ℝ) ^ 2 := by
  have hz (l : Fin d) (hl : l ≠ j) : k l = 0 := by
    by_contra h
    have hm : l ∈ frequencySupport k := by simp [frequencySupport, h]
    simp [hj, hl] at hm
  simp only [frequencyComplexity, hj, Finset.card_singleton, Nat.cast_one, div_one,
    frequencySq]
  exact Finset.sum_eq_single j (fun l _ hl => by simp [hz l hl]) (by simp)

/-- The representatives through a complexity cutoff, including every tie. -/
-- @node: spectralCutoffRepresentatives
def spectralCutoffRepresentatives (d : ℕ) (u : ℝ) : Finset (Fin d → ℤ) :=
  (frequencyBox d (Nat.ceil (Real.sqrt (2 * u)))).filter
    (fun k => IsFrequencyRepresentative k ∧ frequencyComplexity k ≤ u)

/-- The finite cutoff set captures precisely all representatives below its cutoff. [The asserted mathematical result follows](goal). -/
-- @node: mem_spectralCutoffRepresentatives
lemma mem_spectralCutoffRepresentatives {d : ℕ} {u : ℝ} {k : Fin d → ℤ} :
    k ∈ spectralCutoffRepresentatives d u ↔
      IsFrequencyRepresentative k ∧ frequencyComplexity k ≤ u := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨hk, hu⟩
    exact Finset.mem_filter.mpr ⟨frequency_mem_complexity_box ⟨hk.1, hk.2.1⟩ hu, hk, hu⟩

/-- The entire global prefix up to an indexed frequency lies below its complexity. Under [the stated conditions](hyp:hd,hji), [the asserted mathematical result follows](goal). -/
-- @node: featureFrequency_prefix_mem_cutoff
lemma featureFrequency_prefix_mem_cutoff {d i j : ℕ} (hd : 2 ≤ d) (hji : j ≤ i) :
    featureFrequency d j ∈ spectralCutoffRepresentatives d
      (frequencyComplexity (featureFrequency d i)) := by
  apply mem_spectralCutoffRepresentatives.mpr
  refine ⟨featureFrequency_isRepresentative (by omega), ?_⟩
  rcases hji.eq_or_lt with rfl | hji
  · exact le_rfl
  · exact frequencyComplexity_le_of_frequencyBefore_eq_true
      (featureFrequency_strict_order hd hji)

/-- [ Counting the global prefix bounds both real-row indices, even at complexity ties.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: featureFrequency_real_rows_le_cutoff_count
lemma featureFrequency_real_rows_le_cutoff_count {d i : ℕ} (hd : 2 ≤ d) :
    2 * i + 2 ≤ 2 * (spectralCutoffRepresentatives d
      (frequencyComplexity (featureFrequency d i))).card := by
  let A := (Finset.range (i + 1)).image (featureFrequency d)
  have hc : A.card = i + 1 := by
    rw [Finset.card_image_of_injective _ (featureFrequency_injective hd), Finset.card_range]
  have hsub : A ⊆ spectralCutoffRepresentatives d
      (frequencyComplexity (featureFrequency d i)) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    exact featureFrequency_prefix_mem_cutoff hd (by simpa using Finset.mem_range.mp hj)
  have hb := Finset.card_le_card hsub
  rw [hc] at hb
  omega

/-- [ The first nonzero coordinate of a singleton representative is positive.](goal) Under [the stated conditions](hyp:hk,hj). -/
-- @node: representative_single_positive
lemma representative_single_positive {d : ℕ} {k : Fin d → ℤ} {j : Fin d}
    (hk : IsFrequencyRepresentative k) (hj : frequencySupport k = {j}) : 0 < k j := by
  rcases hk.2.2 with ⟨t, ht, _⟩
  have hm : t ∈ frequencySupport k := by simp [frequencySupport, ne_of_gt ht]
  have htj : t = j := by simpa [hj] using hm
  simpa only [htj] using ht

/-- [ The smaller support coordinate of a pair representative is positive.](goal) Under [the stated conditions](hyp:hk,hjl,hj). -/
-- @node: representative_pair_positive
lemma representative_pair_positive {d : ℕ} {k : Fin d → ℤ} {j l : Fin d}
    (hk : IsFrequencyRepresentative k) (hjl : j < l)
    (hj : frequencySupport k = {j, l}) : 0 < k j := by
  rcases hk.2.2 with ⟨t, ht, hprev⟩
  have hm : t ∈ frequencySupport k := by simp [frequencySupport, ne_of_gt ht]
  have hmem : t = j ∨ t = l := by simpa [hj] using hm
  rcases hmem with rfl | rfl
  · exact ht
  · have hz := hprev j hjl
    have hnj : k j ≠ 0 := by
      have hmem : j ∈ frequencySupport k := by simp [hj]
      simpa [frequencySupport] using hmem
    exact False.elim (hnj hz)

/-- [ Every representative has either a singleton or an increasing two-coordinate support.](goal) Under [the stated conditions](hyp:hk). -/
-- @node: representative_support_cases
lemma representative_support_cases {d : ℕ} {k : Fin d → ℤ}
    (hk : IsFrequencyRepresentative k) :
    (∃ j, frequencySupport k = {j}) ∨
      ∃ j l, j < l ∧ frequencySupport k = {j, l} := by
  by_cases hc : (frequencySupport k).card = 1
  · exact Or.inl (Finset.card_eq_one.mp hc)
  · have hlow := hk.1
    have hhigh := hk.2.1
    rcases Finset.card_eq_two.mp (by omega : (frequencySupport k).card = 2) with
      ⟨j, l, hne, heq⟩
    rcases lt_or_gt_of_ne hne with hjl | hlj
    · exact Or.inr ⟨j, l, hjl, heq⟩
    · exact Or.inr ⟨l, j, hlj, by simpa [Finset.pair_comm] using heq⟩

/-- [ Single-coordinate integer frequencies with positive amplitude. -/
-- @node: spectralSingleEncoding
def spectralSingleEncoding {d R : ℕ} (a : Fin d × Fin R) : Fin d → ℤ :=
  fun t => if t = a.1 then (a.2.val + 1 : ℕ) else 0

/-- Two-coordinate representatives, with a positive first amplitude and a signed second one. -/
-- @node: spectralPairEncoding
def spectralPairEncoding {d L : ℕ}
    (a : {jl : Fin d × Fin d // jl.1 < jl.2} × (Fin L × Fin L) × Bool) : Fin d → ℤ :=
  fun t => if t = a.1.val.1 then (a.2.1.1.val + 1 : ℕ)
    else if t = a.1.val.2 then
      (if a.2.2 then -((a.2.1.2.val + 1 : ℕ) : ℤ) else (a.2.1.2.val + 1 : ℕ))
    else 0

/-- Every positive integer of bounded magnitude has a positive-amplitude index.](goal) Under [the stated conditions](hyp:ha,hb). This uses [the stated conclusion](goal). -/
-- @node: positive_integer_amplitude_index
lemma positive_integer_amplitude_index {a : ℤ} {R : ℕ} (ha : 0 < a)
    (hb : a.natAbs ≤ R) : ∃ r : Fin R, (r.val + 1 : ℕ) = a := by
  have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr (ne_of_gt ha)
  refine ⟨⟨a.natAbs - 1, by omega⟩, ?_⟩
  have hn : a.natAbs - 1 + 1 = a.natAbs := by omega
  rw [hn, Int.natCast_natAbs, abs_of_pos ha]

/-- [ Every nonzero bounded integer is a signed positive-amplitude index.](goal) Under [the stated conditions](hyp:ha,hb). -/
-- @node: signed_integer_amplitude_index
lemma signed_integer_amplitude_index {a : ℤ} {L : ℕ} (ha : a ≠ 0)
    (hb : a.natAbs ≤ L) : ∃ r : Fin L, ∃ b : Bool,
      (if b then -((r.val + 1 : ℕ) : ℤ) else (r.val + 1 : ℕ)) = a := by
  have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  let r : Fin L := ⟨a.natAbs - 1, by omega⟩
  have hn : r.val + 1 = a.natAbs := by dsimp [r]; omega
  by_cases hneg : a < 0
  · refine ⟨r, true, ?_⟩
    simp only [ite_true, hn, Int.natCast_natAbs, abs_of_neg hneg, neg_neg]
  · refine ⟨r, false, ?_⟩
    simp only [Bool.false_eq_true, ite_false, hn, Int.natCast_natAbs,
      abs_of_nonneg (by omega : 0 ≤ a)]

/-- [ A singleton representative below the cutoff is in the finite main-effect encoding.](goal) Under [the stated conditions](hyp:hk,hu,hj). -/
-- @node: cutoff_single_in_encoding
lemma cutoff_single_in_encoding {d : ℕ} {u : ℝ} {k : Fin d → ℤ}
    (hk : IsFrequencyRepresentative k) (hu : frequencyComplexity k ≤ u)
    {j : Fin d} (hj : frequencySupport k = {j}) :
    k ∈ (Finset.univ : Finset (Fin d × Fin (Nat.floor (Real.sqrt u)))).image
      spectralSingleEncoding := by
  have hsq : (k j : ℝ) ^ 2 ≤ u := by rwa [frequencyComplexity_single_support hj] at hu
  rcases positive_integer_amplitude_index (representative_single_positive hk hj)
    (frequency_natAbs_le_floor_sqrt hsq) with ⟨r, hr⟩
  apply Finset.mem_image.mpr
  refine ⟨(j, r), Finset.mem_univ _, ?_⟩
  funext t
  by_cases ht : t = j
  · subst t
    simp [spectralSingleEncoding, hr]
  · have hz : k t = 0 := by
      by_contra h
      have hm : t ∈ frequencySupport k := by simp [frequencySupport, h]
      simp [hj, ht] at hm
    simp [spectralSingleEncoding, ht, hz]

/-- [ A pair representative below the cutoff is in the finite signed pair encoding.](goal) Under [the stated conditions](hyp:hk,hu,hjl,hj). -/
-- @node: cutoff_pair_in_encoding
lemma cutoff_pair_in_encoding {d : ℕ} {u : ℝ} {k : Fin d → ℤ}
    (hk : IsFrequencyRepresentative k) (hu : frequencyComplexity k ≤ u)
    {j l : Fin d} (hjl : j < l) (hj : frequencySupport k = {j, l}) :
    k ∈ (Finset.univ : Finset
      ({jl : Fin d × Fin d // jl.1 < jl.2} ×
        (Fin (Nat.floor (Real.sqrt (2 * u))) × Fin (Nat.floor (Real.sqrt (2 * u)))) × Bool)).image
      spectralPairEncoding := by
  have hb (t : Fin d) : (k t).natAbs ≤ Nat.floor (Real.sqrt (2 * u)) :=
    frequency_natAbs_le_floor_sqrt
      ((frequency_coordinate_sq_le_two_complexity ⟨hk.1, hk.2.1⟩ t).trans (by linarith))
  rcases positive_integer_amplitude_index (representative_pair_positive hk hjl hj) (hb j)
    with ⟨a, ha⟩
  have hl : k l ≠ 0 := by
    have hm : l ∈ frequencySupport k := by simp [hj]
    simpa [frequencySupport] using hm
  rcases signed_integer_amplitude_index hl (hb l) with ⟨b, neg, hb'⟩
  apply Finset.mem_image.mpr
  refine ⟨(⟨(j, l), hjl⟩, (a, b), neg), Finset.mem_univ _, ?_⟩
  funext t
  by_cases htj : t = j
  · subst t
    simp [spectralPairEncoding, ha]
  · by_cases htl : t = l
    · subst t
      simpa only [spectralPairEncoding, htj, if_false, if_true] using hb'
    · have hz : k t = 0 := by
        by_contra h
        have hm : t ∈ frequencySupport k := by simp [frequencySupport, h]
        simp [hj, htj, htl] at hm
      simp [spectralPairEncoding, htj, htl, hz]

/-- There are exactly binomially many increasing coordinate pairs. [The asserted mathematical result follows](goal). -/
-- @node: ordered_coordinate_pair_card
lemma ordered_coordinate_pair_card (d : ℕ) :
    Fintype.card {jl : Fin d × Fin d // jl.1 < jl.2} = pairCount d := by
  rw [Fintype.card_subtype]
  simpa only [Fintype.card_fin, pairCount] using
    (Fintype.card_product_filter_lt (α := Fin d))

/-- [ Main effects and signed pairs give the finite cutoff-count bound
before scalar simplification.](goal) -/
-- @node: spectralCutoffRepresentatives_card_le
lemma spectralCutoffRepresentatives_card_le (d : ℕ) (u : ℝ) :
    (spectralCutoffRepresentatives d u).card ≤
      d * Nat.floor (Real.sqrt u) +
        2 * pairCount d * Nat.floor (Real.sqrt (2 * u)) ^ 2 := by
  let A := (Finset.univ : Finset (Fin d × Fin (Nat.floor (Real.sqrt u)))).image
    spectralSingleEncoding
  let B := (Finset.univ : Finset
    ({jl : Fin d × Fin d // jl.1 < jl.2} ×
      (Fin (Nat.floor (Real.sqrt (2 * u))) × Fin (Nat.floor (Real.sqrt (2 * u)))) × Bool)).image
    spectralPairEncoding
  have hsub : spectralCutoffRepresentatives d u ⊆ A ∪ B := by
    intro k hk
    rcases mem_spectralCutoffRepresentatives.mp hk with ⟨hr, hu⟩
    rcases representative_support_cases hr with ⟨j, hj⟩ | ⟨j, l, hjl, hj⟩
    · exact Finset.mem_union.mpr (Or.inl (cutoff_single_in_encoding hr hu hj))
    · exact Finset.mem_union.mpr (Or.inr (cutoff_pair_in_encoding hr hu hjl hj))
  have ha : A.card ≤ d * Nat.floor (Real.sqrt u) := by
    simpa [A] using Finset.card_image_le (s := (Finset.univ :
      Finset (Fin d × Fin (Nat.floor (Real.sqrt u))))) (f := spectralSingleEncoding)
  have hb : B.card ≤ 2 * pairCount d * Nat.floor (Real.sqrt (2 * u)) ^ 2 := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset
      ({jl : Fin d × Fin d // jl.1 < jl.2} ×
        (Fin (Nat.floor (Real.sqrt (2 * u))) × Fin (Nat.floor (Real.sqrt (2 * u)))) × Bool)))
      (f := spectralPairEncoding)
    simpa only [B, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, ordered_coordinate_pair_card, pow_two, mul_comm, mul_left_comm,
      mul_assoc] using h
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le A B).trans (Nat.add_le_add ha hb))

/-- A nonzero integer frequency has averaged squared complexity at least one. Under [the stated conditions](hyp:hk), [the asserted mathematical result follows](goal). -/
-- @node: one_le_frequencyComplexity
lemma one_le_frequencyComplexity {d : ℕ} {k : Fin d → ℤ}
    (hk : 1 ≤ (frequencySupport k).card) : 1 ≤ frequencyComplexity k := by
  have hpos : 0 < ((frequencySupport k).card : ℝ) := by exact_mod_cast hk
  have hc : ((frequencySupport k).card : ℝ) ≤ frequencySq k := by
    calc
      _ = ∑ j ∈ frequencySupport k, (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ frequencySupport k, (k j : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hne : k j ≠ 0 := by simpa [frequencySupport] using hj
        have hz : 1 ≤ k j ∨ k j ≤ -1 := by omega
        rcases hz with hz | hz
        · have hr : (1 : ℝ) ≤ k j := by exact_mod_cast hz
          nlinarith [sq_nonneg ((k j : ℝ) - 1)]
        · have hr : (k j : ℝ) ≤ -1 := by exact_mod_cast hz
          nlinarith [sq_nonneg ((k j : ℝ) + 1)]
      _ ≤ frequencySq k := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => sq_nonneg (k j : ℝ))
  exact (le_div_iff₀ hpos).mpr (by simpa using hc)

/-- [ In dimension at least two, the coordinate count is at most twice the pair count.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: spectral_dimension_le_two_pairCount
lemma spectral_dimension_le_two_pairCount {d : ℕ} (hd : 2 ≤ d) :
    (d : ℝ) ≤ 2 * pairCount d := by
  have heq := Nat.descFactorial_eq_factorial_mul_choose d 2
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    mul_one, Nat.factorial_succ, Nat.factorial_zero] at heq
  have hreal : ((d : ℝ) - 1) * d = 2 * (pairCount d : ℝ) := by
    have hc := congrArg (Nat.cast : ℕ → ℝ) heq
    simpa [Nat.cast_sub (by omega : 1 ≤ d), pairCount] using hc
  have hdim : (2 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

/-- [ The two real rows for every conjugate pair have total cutoff count at most twelve
 times the pair count and the complexity cutoff.](goal) Under [the stated conditions](hyp:hd,hu). -/
-- @node: spectral_real_cutoff_count_le
lemma spectral_real_cutoff_count_le {d : ℕ} {u : ℝ} (hd : 2 ≤ d) (hu : 1 ≤ u) :
    2 * ((spectralCutoffRepresentatives d u).card : ℝ) ≤ 12 * pairCount d * u := by
  have hc : ((spectralCutoffRepresentatives d u).card : ℝ) ≤
      (d : ℝ) * Nat.floor (Real.sqrt u) +
        2 * pairCount d * (Nat.floor (Real.sqrt (2 * u)) : ℝ) ^ 2 := by
    exact_mod_cast spectralCutoffRepresentatives_card_le d u
  have hsqrt : Real.sqrt u ≤ u := by
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ u)
    have hnonneg := Real.sqrt_nonneg u
    nlinarith [sq_nonneg (Real.sqrt u - 1)]
  have hr := (Nat.floor_le (Real.sqrt_nonneg u)).trans hsqrt
  have hl := Nat.floor_le (Real.sqrt_nonneg (2 * u))
  have hlpos : (0 : ℝ) ≤ Nat.floor (Real.sqrt (2 * u)) := by positivity
  have hl2 : (Nat.floor (Real.sqrt (2 * u)) : ℝ) ^ 2 ≤ 2 * u := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ 2 * u)
    nlinarith [Real.sqrt_nonneg (2 * u)]
  have hdB := spectral_dimension_le_two_pairCount hd
  have hdpos : (0 : ℝ) ≤ d := by positivity
  have hBpos : (0 : ℝ) ≤ pairCount d := by positivity
  have hm := mul_le_mul_of_nonneg_left hr hdpos
  have hp := mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ 2 * pairCount d)
  have hdBu := mul_le_mul_of_nonneg_right hdB (by linarith : 0 ≤ u)
  nlinarith

/-- [ Both real row indices of an indexed frequency obey the explicit twelve-pair cutoff.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: featureFrequency_real_rows_le_complexity
lemma featureFrequency_real_rows_le_complexity {d i : ℕ} (hd : 2 ≤ d) :
    (2 * i + 2 : ℝ) ≤ 12 * pairCount d * frequencyComplexity (featureFrequency d i) := by
  have hr : (2 * i + 2 : ℝ) ≤
      2 * ((spectralCutoffRepresentatives d
        (frequencyComplexity (featureFrequency d i))).card : ℝ) := by
    exact_mod_cast featureFrequency_real_rows_le_cutoff_count (i := i) hd
  exact hr.trans (spectral_real_cutoff_count_le hd
    (one_le_frequencyComplexity (featureFrequency_support_nonempty (by omega))))

/-- Negating a frequency preserves its support. [The asserted mathematical result follows](goal). -/
-- @node: frequencySupport_neg
lemma frequencySupport_neg {d : ℕ} (k : Fin d → ℤ) :
    frequencySupport (-k) = frequencySupport k := by
  ext j
  simp [frequencySupport]

/-- [ Opposite frequencies have the same averaged squared complexity.](goal) -/
-- @node: frequencyComplexity_neg
lemma frequencyComplexity_neg {d : ℕ} (k : Fin d → ℤ) :
    frequencyComplexity (-k) = frequencyComplexity k := by
  simp [frequencyComplexity, frequencySupport_neg, frequencySq]

/-- Every supported nonzero frequency has exactly a prescribed orientation up to sign. Under [the stated conditions](hyp:hk), [the asserted mathematical result follows](goal). -/
-- @node: representative_or_neg_of_supported
lemma representative_or_neg_of_supported {d : ℕ} {k : Fin d → ℤ}
    (hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2) :
    IsFrequencyRepresentative k ∨ IsFrequencyRepresentative (-k) := by
  have hne : (frequencySupport k).Nonempty := Finset.card_pos.mp (by omega)
  let j := (frequencySupport k).min' hne
  have hjmem : j ∈ frequencySupport k := Finset.min'_mem _ _
  have hjnz : k j ≠ 0 := by simpa [frequencySupport] using hjmem
  have hprev : ∀ l : Fin d, l < j → k l = 0 := by
    intro l hlj
    by_contra h
    have hlmem : l ∈ frequencySupport k := by simp [frequencySupport, h]
    have hjl : j ≤ l := Finset.min'_le _ l hlmem
    exact (not_le_of_gt hlj) hjl
  rcases lt_or_gt_of_ne hjnz with hneg | hpos
  · right
    refine ⟨by simpa [frequencySupport_neg] using hk.1,
      by simpa [frequencySupport_neg] using hk.2, j, ?_, ?_⟩
    · simpa using neg_pos.mpr hneg
    · intro l hl
      simp [hprev l hl]
  · exact Or.inl ⟨hk.1, hk.2, j, hpos, hprev⟩

/-- [ Every support-one or support-two frequency occurs in the global real-row enumeration
up to the unique choice of conjugate orientation.](goal) Under [the stated conditions](hyp:hd,hk). -/
-- @node: supported_frequency_eq_feature_or_neg
lemma supported_frequency_eq_feature_or_neg {d : ℕ} (hd : 2 ≤ d) (k : Fin d → ℤ)
    (hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2) :
    ∃ i : ℕ, k = featureFrequency d i ∨ k = -featureFrequency d i := by
  rcases representative_or_neg_of_supported hk with hr | hr
  · rcases featureFrequency_surjective_representatives hd k hr with ⟨i, hi⟩
    exact ⟨i, Or.inl hi.symm⟩
  · rcases featureFrequency_surjective_representatives hd (-k) hr with ⟨i, hi⟩
    refine ⟨i, Or.inr ?_⟩
    simpa using congrArg Neg.neg hi.symm

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
