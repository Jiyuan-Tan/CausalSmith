module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ActiveLabelEnergyBound
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.RowEnergyCounts

/-!
# Exact row factors in the revealed-label energy envelope

Remove masked inactive rows and reindex the original revealed-label subsets by
families of subsets of the disjoint revealed rows. All original labels remain
in the bijection; only their rowwise energy factors are simplified.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The constant Walsh coefficient has unit reference energy.  [For the stated data and conditions](hyp:d,h), [the stated conclusion holds](goal). -/
-- @node: gamma_zero_energy
lemma gamma_zero_energy (d : ℕ) (h : ℝ) : gamma d h 0 = 1 := by
  unfold gamma
  calc
    _ = ∫ w, refDensity d h w := by
      apply integral_congr_ae
      filter_upwards [] with w
      by_cases hz : refDensity d h w = 0
      · simp [hz]
      · have hp := lt_of_le_of_ne (refDensity_nonneg d h w) (Ne.symm hz)
        rw [walshCoeff_zero d h w hp]
        ring
    _ = 1 := (refDensity_integrable_normalized d h).2

/-- On disjoint active rows, the masked product consists of the unrestricted
revealed-degree factors and the positive-degree hidden factors; all other rows
contribute exactly one.  [For the stated data and conditions](hyp:B,d,h,u,j), [the stated conclusion holds](goal). -/
-- @node: activeSupportEnergyBound_row_factors
lemma activeSupportEnergyBound_row_factors (B d : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) :
    activeSupportEnergyBound B d h u j =
      let A := Finset.univ.filter (fun ℓ => j ℓ ≠ 0)
      ∑ E ∈ (Finset.univ \ A).powerset,
        (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
          ((∏ ℓ ∈ A, ∑ t : Fin (u ℓ + 1),
            ((u ℓ).choose t.val : ℝ) * gamma d h (j ℓ + t.val)) *
           (∏ ℓ ∈ E, ∑ t : Fin (u ℓ + 1),
            if 0 < t.val then ((u ℓ).choose t.val : ℝ) * gamma d h t.val else 0)) := by
  classical
  unfold activeSupportEnergyBound
  dsimp only
  apply Finset.sum_congr rfl
  intro E hE
  congr 1
  let A := Finset.univ.filter (fun ℓ => j ℓ ≠ 0)
  let R (ℓ : Fin B) := ∑ t : Fin (u ℓ + 1),
    ((u ℓ).choose t.val : ℝ) * gamma d h (j ℓ + t.val)
  let U (ℓ : Fin B) := ∑ t : Fin (u ℓ + 1),
    if 0 < t.val then ((u ℓ).choose t.val : ℝ) * gamma d h t.val else 0
  have hEA : ∀ ℓ ∈ E, ℓ ∉ A := by
    intro ℓ hℓ
    exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hE hℓ)).2
  calc
    _ = ∏ ℓ : Fin B, (if ℓ ∈ A then R ℓ else 1) *
        (if ℓ ∈ E then U ℓ else 1) := by
      apply Finset.prod_congr rfl
      intro ℓ _
      by_cases hA : ℓ ∈ A
      · have hj : j ℓ ≠ 0 := (Finset.mem_filter.mp hA).2
        have hn : ℓ ∉ E := fun hℓ => hEA ℓ hℓ hA
        have hc : activeCapacity B u (A ∪ E) ℓ = u ℓ := by
          simp [activeCapacity, hA]
        change (∑ t : Fin (activeCapacity B u (A ∪ E) ℓ + 1),
          if (if j ℓ ≠ 0 then True else if ℓ ∈ A ∪ E then 0 < t.val else t.val = 0) then
            ((activeCapacity B u (A ∪ E) ℓ).choose t.val : ℝ) *
              gamma d h (j ℓ + t.val) else 0) = _
        rw [hc]
        simp [hj, hA, hn, R]
      · have hj : j ℓ = 0 := by simpa [A] using hA
        by_cases hℓ : ℓ ∈ E
        · have hc : activeCapacity B u (A ∪ E) ℓ = u ℓ := by
            simp [activeCapacity, hℓ]
          change (∑ t : Fin (activeCapacity B u (A ∪ E) ℓ + 1),
            if (if j ℓ ≠ 0 then True else if ℓ ∈ A ∪ E then 0 < t.val else t.val = 0) then
              ((activeCapacity B u (A ∪ E) ℓ).choose t.val : ℝ) *
                gamma d h (j ℓ + t.val) else 0) = _
          rw [hc]
          simp [hj, hA, hℓ, U]
        · have hc : activeCapacity B u (A ∪ E) ℓ = 0 := by
            simp [activeCapacity, hA, hℓ]
          change (∑ t : Fin (activeCapacity B u (A ∪ E) ℓ + 1),
            if (if j ℓ ≠ 0 then True else if ℓ ∈ A ∪ E then 0 < t.val else t.val = 0) then
              ((activeCapacity B u (A ∪ E) ℓ).choose t.val : ℝ) *
                gamma d h (j ℓ + t.val) else 0) = _
          rw [hc]
          simp [hj, hA, hℓ, gamma_zero_energy]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      rw [Fintype.prod_ite_mem, Fintype.prod_ite_mem]

/-- Summing nonempty revealed subsets and every hidden degree is precisely
revealed row energy, rather than an independent hidden-row approximation.  [For the stated data and conditions](hyp:d,h,r), [the stated conclusion holds](goal). -/
-- @node: rowRevealedEnergy_subset_degree_sum
lemma rowRevealedEnergy_subset_degree_sum (d : ℕ) (h : ℝ) (r : Fin d → Bool) :
    (∑ J ∈ (Finset.univ.filter (fun j : Fin d => r j = true)).powerset,
      if J = ∅ then 0 else
        ∑ t : Fin ((Finset.univ.filter (fun j : Fin d => r j = false)).card + 1),
          (((Finset.univ.filter (fun j : Fin d => r j = false)).card).choose t.val : ℝ) *
            gamma d h (J.card + t.val)) = rowRevealedEnergy d h r := by
  classical
  let R := Finset.univ.filter (fun j : Fin d => r j = true)
  let U := Finset.univ.filter (fun j : Fin d => r j = false)
  have hRU : Disjoint R U := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have ht := (Finset.mem_filter.mp hj).2
    have hf := (Finset.mem_filter.mp hk).2
    simp [ht] at hf
  have hcover : R ∪ U = Finset.univ := by
    ext j
    cases hr : r j <;> simp [R, U, hr]
  have hsum (J : Finset (Fin d)) :
      (∑ t : Fin (U.card + 1), (U.card.choose t.val : ℝ) *
        gamma d h (J.card + t.val)) = ∑ K ∈ U.powerset, gamma d h (J.card + K.card) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (U.card.choose k : ℝ) *
      gamma d h (J.card + k))]
    simpa only [nsmul_eq_mul] using
      (Finset.sum_powerset_apply_card (fun k => gamma d h (J.card + k)) (x := U)).symm
  change (∑ J ∈ R.powerset, if J = ∅ then 0 else
    ∑ t : Fin (U.card + 1), (U.card.choose t.val : ℝ) * gamma d h (J.card + t.val)) = _
  simp_rw [hsum]
  rw [rowRevealedEnergy, ← Finset.powerset_univ, ← hcover,
    labeled_walsh_powerset_split R U hRU]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJR := Finset.mem_powerset.mp hJ
  by_cases hz : J = ∅
  · subst J
    simp only [if_true, Finset.empty_union]
    symm
    apply Finset.sum_eq_zero
    intro K hK
    have hn : ¬ ∃ j ∈ K, r j = true := by
      rintro ⟨j, hj, ht⟩
      have hf := (Finset.mem_filter.mp (Finset.mem_powerset.mp hK hj)).2
      simp [ht] at hf
    simp [hn]
  · simp only [hz, if_false]
    apply Finset.sum_congr rfl
    intro K hK
    have hKU := Finset.mem_powerset.mp hK
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hz
    have hh : ∃ j ∈ J ∪ K, r j = true :=
      ⟨j, Finset.mem_union_left K hj, (Finset.mem_filter.mp (hJR hj)).2⟩
    have hne : J ∪ K ≠ ∅ := by
      exact Finset.nonempty_iff_ne_empty.mp ⟨j, Finset.mem_union_left K hj⟩
    rw [if_pos hh, rowSubsetEnergy, if_neg hne,
      Finset.card_union_of_disjoint (hRU.mono hJR hKU)]

/-- The revealed-subset energy factor depends only on the revealed and hidden
counts, and therefore agrees with any row reveal pattern of those counts.  [For the stated data and conditions](hyp:α,d,h,R,u,r,hR,hu), [the stated conclusion holds](goal). -/
-- @node: labeled_revealed_subset_energy_eq
lemma labeled_revealed_subset_energy_eq {α : Type*} [DecidableEq α]
    (d : ℕ) (h : ℝ) (R : Finset α) (u : ℕ) (r : Fin d → Bool)
    (hR : R.card = (Finset.univ.filter (fun j : Fin d => r j = true)).card)
    (hu : u = (Finset.univ.filter (fun j : Fin d => r j = false)).card) :
    (∑ J ∈ R.powerset, if J = ∅ then 0 else
      ∑ t : Fin (u + 1), (u.choose t.val : ℝ) * gamma d h (J.card + t.val)) =
      rowRevealedEnergy d h r := by
  classical
  rw [← rowRevealedEnergy_subset_degree_sum d h r, ← hu]
  let F (k : ℕ) : ℝ := if k = 0 then 0 else
    ∑ t : Fin (u + 1), (u.choose t.val : ℝ) * gamma d h (k + t.val)
  simp_rw [← Finset.card_eq_zero]
  change (∑ J ∈ R.powerset, F J.card) =
    ∑ J ∈ (Finset.univ.filter (fun j : Fin d => r j = true)).powerset, F J.card
  simp_rw [Finset.sum_powerset_apply_card]
  rw [hR]

/-- A canonical reveal pattern with r revealed slots preserves the two row
counts. It is used only to express energies, after the full-label reindexing. -/
-- @node: countRevealRow
def countRevealRow (d r : ℕ) : Fin d → Bool := fun j => decide (j.val < r)

/-- The canonical count pattern has exactly r revealed slots and d-r hidden slots.  [For the stated data and conditions](hyp:d,r,hr), [the stated conclusion holds](goal). -/
-- @node: countRevealRow_counts
lemma countRevealRow_counts (d r : ℕ) (hr : r ≤ d) :
    (Finset.univ.filter (fun j : Fin d => countRevealRow d r j = true)).card = r ∧
    (Finset.univ.filter (fun j : Fin d => countRevealRow d r j = false)).card = d - r := by
  classical
  let e : Fin r ↪ Fin d := ⟨fun j => ⟨j.val, by omega⟩, fun a b hab =>
    Fin.ext (congrArg (fun k : Fin d => k.val) hab)⟩
  have he : Finset.univ.filter (fun j : Fin d => countRevealRow d r j = true) =
      Finset.univ.map e := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, countRevealRow,
      decide_eq_true_eq, Finset.mem_map]
    constructor
    · intro hj
      exact ⟨⟨j.val, hj⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.isLt
  have hc : (Finset.univ.filter (fun j : Fin d => countRevealRow d r j = true)).card = r := by
    rw [he, Finset.card_map]; simp
  refine ⟨hc, ?_⟩
  have hcomp : Finset.univ.filter (fun j : Fin d => countRevealRow d r j = false) =
      Finset.univ \ Finset.univ.filter (fun j : Fin d => countRevealRow d r j = true) := by
    ext j
    cases hj : countRevealRow d r j <;> simp [hj]
  rw [hcomp, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hc]
  simp

/-- At a fixed revealed-active set, the row-subset sum factors into independent
nonempty-subset sums; inactive rows have the unique empty selection.  [For the stated data and conditions](hyp:α,B,R,A,F), [the stated conclusion holds](goal). -/
-- @node: revealed_active_subset_product
lemma revealed_active_subset_product {α : Type*} [DecidableEq α]
    (B : ℕ) (R : Fin B → Finset α) (A : Finset (Fin B))
    (F : Fin B → Finset α → ℝ) :
    (∑ J ∈ (Fintype.piFinset (fun ℓ => (R ℓ).powerset)).filter
      (fun J => Finset.univ.filter (fun ℓ => J ℓ ≠ ∅) = A),
        ∏ ℓ ∈ A, F ℓ (J ℓ)) =
      ∏ ℓ ∈ A, ∑ J ∈ (R ℓ).powerset, if J = ∅ then 0 else F ℓ J := by
  classical
  let S (ℓ : Fin B) := if ℓ ∈ A then (R ℓ).powerset.erase ∅ else {∅}
  have hsets : (Fintype.piFinset (fun ℓ => (R ℓ).powerset)).filter
      (fun J => Finset.univ.filter (fun ℓ => J ℓ ≠ ∅) = A) = Fintype.piFinset S := by
    ext J
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hJ, hA⟩ ℓ
      have hm : J ℓ ≠ ∅ ↔ ℓ ∈ A := by
        rw [← hA]; simp
      by_cases hℓ : ℓ ∈ A
      · simp [S, hℓ, (hm.mpr hℓ), hJ ℓ]
      · have hz : J ℓ = ∅ := by tauto
        simp [S, hℓ, hz]
    · intro hJ
      have hm (ℓ) : J ℓ ≠ ∅ ↔ ℓ ∈ A := by
        have hh := hJ ℓ
        by_cases hℓ : ℓ ∈ A
        · have hn := (Finset.mem_erase.mp
            (show J ℓ ∈ (R ℓ).powerset.erase ∅ by simpa [S, hℓ] using hh)).1
          simp [hn, hℓ]
        · simp only [S, hℓ, if_false, Finset.mem_singleton] at hh
          simp [hh, hℓ]
      refine ⟨?_, ?_⟩
      · intro ℓ
        have hh := hJ ℓ
        by_cases hℓ : ℓ ∈ A
        · exact (Finset.mem_erase.mp (by simpa [S, hℓ] using hh)).2
        · have hz : J ℓ = ∅ := by simpa [S, hℓ] using hh
          simp [hz]
      · ext ℓ
        simp [hm ℓ]
  rw [hsets]
  calc
    _ = ∑ J ∈ Fintype.piFinset S, ∏ ℓ : Fin B,
        if ℓ ∈ A then F ℓ (J ℓ) else 1 := by
      simp_rw [Fintype.prod_ite_mem]
    _ = ∏ ℓ : Fin B, ∑ J ∈ S ℓ, if ℓ ∈ A then F ℓ J else 1 :=
      (Finset.prod_univ_sum S (fun ℓ J => if ℓ ∈ A then F ℓ J else 1)).symm
    _ = ∏ ℓ : Fin B, if ℓ ∈ A then
        (∑ J ∈ (R ℓ).powerset, if J = ∅ then 0 else F ℓ J) else 1 := by
      apply Finset.prod_congr rfl
      intro ℓ _
      by_cases hℓ : ℓ ∈ A
      · simp only [S, hℓ, if_true]
        rw [Finset.sum_ite]
        simp only [Finset.sum_const_zero, zero_add]
        congr 1
        ext J
        simp [Finset.mem_erase, and_comm]
      · simp [S, hℓ]
    _ = _ := Fintype.prod_ite_mem A _

/-- The exact row-subset envelope before revealed-active rows are grouped. -/
-- @node: rowSubsetActiveEnvelope
def rowSubsetActiveEnvelope {α : Type*} [DecidableEq α]
    (B d : ℕ) (h : ℝ) (R : Fin B → Finset α) (u : Fin B → ℕ) : ℝ :=
  ∑ J ∈ Fintype.piFinset (fun ℓ => (R ℓ).powerset),
    let A := Finset.univ.filter (fun ℓ => J ℓ ≠ ∅)
    ∑ E ∈ (Finset.univ \ A).powerset,
      (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
        ((∏ ℓ ∈ A, ∑ t : Fin (u ℓ + 1),
          ((u ℓ).choose t.val : ℝ) * gamma d h ((J ℓ).card + t.val)) *
         (∏ ℓ ∈ E, ∑ t : Fin (u ℓ + 1),
          if 0 < t.val then ((u ℓ).choose t.val : ℝ) * gamma d h t.val else 0))

/-- Grouping the exact revealed-subset families by their nonempty rows gives
products of row-subset energies for every disjoint pair of active sets.  [For the stated data and conditions](hyp:α,B,d,h,R,u), [the stated conclusion holds](goal). -/
-- @node: rowSubsetActiveEnvelope_active_rows
lemma rowSubsetActiveEnvelope_active_rows {α : Type*} [DecidableEq α]
    (B d : ℕ) (h : ℝ) (R : Fin B → Finset α) (u : Fin B → ℕ) :
    rowSubsetActiveEnvelope B d h R u =
      ∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
        (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
          ((∏ ℓ ∈ A, ∑ J ∈ (R ℓ).powerset, if J = ∅ then 0 else
            ∑ t : Fin (u ℓ + 1), ((u ℓ).choose t.val : ℝ) *
              gamma d h (J.card + t.val)) *
           (∏ ℓ ∈ E, ∑ t : Fin (u ℓ + 1),
            if 0 < t.val then ((u ℓ).choose t.val : ℝ) * gamma d h t.val else 0)) := by
  classical
  let F (ℓ : Fin B) (J : Finset α) := ∑ t : Fin (u ℓ + 1),
    ((u ℓ).choose t.val : ℝ) * gamma d h (J.card + t.val)
  let U (ℓ : Fin B) := ∑ t : Fin (u ℓ + 1),
    if 0 < t.val then ((u ℓ).choose t.val : ℝ) * gamma d h t.val else 0
  let g (J : Fin B → Finset α) := Finset.univ.filter (fun ℓ => J ℓ ≠ ∅)
  let c (A E : Finset (Fin B)) :=
    (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card
  unfold rowSubsetActiveEnvelope
  change (∑ J ∈ Fintype.piFinset (fun ℓ => (R ℓ).powerset),
    ∑ E ∈ (Finset.univ \ g J).powerset,
      c (g J) E * ((∏ ℓ ∈ g J, F ℓ (J ℓ)) * ∏ ℓ ∈ E, U ℓ)) = _
  rw [← Finset.sum_fiberwise (Fintype.piFinset (fun ℓ => (R ℓ).powerset)) g]
  apply Finset.sum_congr rfl
  intro A _
  calc
    _ = ∑ J ∈ (Fintype.piFinset (fun ℓ => (R ℓ).powerset)).filter (fun J => g J = A),
        ∑ E ∈ (Finset.univ \ A).powerset,
          c A E * ((∏ ℓ ∈ A, F ℓ (J ℓ)) * ∏ ℓ ∈ E, U ℓ) := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [(Finset.mem_filter.mp hJ).2]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E _
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [revealed_active_subset_product B R A F]

/-- When row counts match, the exact active-set envelope is the product of
the revealed and hidden row energies used by independent-row averaging.  [For the stated data and conditions](hyp:α,B,d,h,R,u,r,hR,hu), [the stated conclusion holds](goal). -/
-- @node: rowSubsetActiveEnvelope_eq_row_energies
lemma rowSubsetActiveEnvelope_eq_row_energies {α : Type*} [DecidableEq α]
    (B d : ℕ) (h : ℝ) (R : Fin B → Finset α) (u : Fin B → ℕ)
    (r : Fin B → Fin d → Bool)
    (hR : ∀ ℓ, (R ℓ).card = (Finset.univ.filter (fun j => r ℓ j = true)).card)
    (hu : ∀ ℓ, u ℓ = (Finset.univ.filter (fun j => r ℓ j = false)).card) :
    rowSubsetActiveEnvelope B d h R u =
      ∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
        (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
          ((∏ ℓ ∈ A, rowRevealedEnergy d h (r ℓ)) *
           (∏ ℓ ∈ E, rowHiddenEnergy d h (r ℓ))) := by
  rw [rowSubsetActiveEnvelope_active_rows]
  simp_rw [labeled_revealed_subset_energy_eq d h _ _ _ (hR _) (hu _),
    rowHiddenEnergy_fin_degree_sum d h _ _ (hu _)]

/-- The original label enumeration and the disjoint row-subset family have
identical envelopes, including the constant coefficient.  [For the stated data and conditions](hyp:n,B,d,h,H,s), [the stated conclusion holds](goal). -/
-- @node: actualLabelActiveEnvelope_eq_rowSubset
lemma actualLabelActiveEnvelope_eq_rowSubset (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (s : CompatiblePartition n B d H) :
    actualLabelActiveEnvelope n B d h H =
      rowSubsetActiveEnvelope B d h (revealedSources n B d H) (capacity n B d H) := by
  unfold actualLabelActiveEnvelope rowSubsetActiveEnvelope
  have hr := disjoint_rowSubset_sum_reindex (revealedSources n B d H)
    (revealedSources_pairwise_disjoint n B d H s)
    (fun J => activeSupportEnergyBound B d h (capacity n B d H)
      (fun ℓ => (J ℓ).card))
  rw [← revealedLabelEmbedding_univ_map n B d H, labeled_powerset_map,
    Finset.sum_map] at hr
  simp only [Finset.powerset_univ] at hr
  trans ∑ J ∈ Fintype.piFinset (fun ℓ => (revealedSources n B d H ℓ).powerset),
    activeSupportEnergyBound B d h (capacity n B d H) (fun ℓ => (J ℓ).card)
  · exact hr.symm
  apply Finset.sum_congr rfl
  intro J _
  rw [activeSupportEnergyBound_row_factors]
  simp only [ne_eq, Finset.card_eq_zero]

/-- Nonconstant disjoint-row envelope expressed through the actual row counts. -/
-- @node: retainedRowEnergyEnvelope
def retainedRowEnergyEnvelope (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) : ℝ :=
  ∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
    if A.card + E.card = 0 then 0 else
      (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
        ((∏ ℓ ∈ A, rowRevealedEnergy d h
          (countRevealRow d (revealedCount n B d H ℓ))) *
         (∏ ℓ ∈ E, rowHiddenEnergy d h
          (countRevealRow d (revealedCount n B d H ℓ))))

/-- Summing all actual revealed labels gives the nonconstant disjoint-row energy
envelope, with exactly one constant term removed.  [For the stated data and conditions](hyp:n,B,d,h,H,hH), [the stated conclusion holds](goal). -/
-- @node: actualLabelActiveEnvelope_sub_one_eq_row_energy
lemma actualLabelActiveEnvelope_sub_one_eq_row_energy (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (hH : ValidRetainedGraph n B d H) :
    actualLabelActiveEnvelope n B d h H - 1 = retainedRowEnergyEnvelope n B d h H := by
  classical
  obtain ⟨hfit, s, hs⟩ := hH
  have hc (ℓ : Fin B) := countRevealRow_counts d (revealedCount n B d H ℓ)
    (revealedCount_le n B d H ⟨hfit, s, hs⟩ ℓ)
  rw [actualLabelActiveEnvelope_eq_rowSubset n B d h H ⟨s, hs⟩,
    rowSubsetActiveEnvelope_eq_row_energies B d h (revealedSources n B d H) (capacity n B d H)
      (fun ℓ => countRevealRow d (revealedCount n B d H ℓ))
      (fun ℓ => (hc ℓ).1.symm) (fun ℓ => (hc ℓ).2.symm)]
  let F (A E : Finset (Fin B)) : ℝ :=
    (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
      ((∏ ℓ ∈ A, rowRevealedEnergy d h (countRevealRow d (revealedCount n B d H ℓ))) *
       (∏ ℓ ∈ E, rowHiddenEnergy d h (countRevealRow d (revealedCount n B d H ℓ))))
  change (∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset, F A E) - 1 =
    ∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
      if A.card + E.card = 0 then 0 else F A E
  have hcst : (∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
      if A.card + E.card = 0 then (1 : ℝ) else 0) = 1 := by
    simp [Finset.card_eq_zero, ite_and]
  have ht (A E : Finset (Fin B)) : F A E =
      (if A.card + E.card = 0 then 1 else 0) +
      (if A.card + E.card = 0 then 0 else F A E) := by
    by_cases hz : A.card + E.card = 0
    · have hA : A = ∅ := Finset.card_eq_zero.mp (by omega)
      have hE : E = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [F, hA, hE]
    · simp only [hz, if_false, zero_add]
  conv_lhs => arg 1; arg 2; ext A; arg 2; ext E; rw [ht A E]
  simp only [Finset.sum_add_distrib]
  rw [hcst]
  ring

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
