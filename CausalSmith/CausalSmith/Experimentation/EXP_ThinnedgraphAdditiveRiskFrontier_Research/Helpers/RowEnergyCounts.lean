module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.RowRevealEnergy

/-!
# Row energies from hidden capacities

Counting subsets of the actual hidden labels identifies the hidden active-row
energy with the binomial degree sum in the contraction roadmap. The revealed
energy is its complement in the total nonconstant channel energy.
-/

public section

open scoped BigOperators
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Hidden energy sums exactly the nonconstant subsets of the hidden label set.  [For the stated data and conditions](hyp:d,h,r), [the stated conclusion holds](goal). -/
-- @node: rowHiddenEnergy_eq_powerset
lemma rowHiddenEnergy_eq_powerset (d : ℕ) (h : ℝ) (r : Fin d → Bool) :
    rowHiddenEnergy d h r =
      ∑ E ∈ (Finset.univ.filter (fun j : Fin d => r j = false)).powerset,
        rowSubsetEnergy d h E := by
  classical
  rw [rowHiddenEnergy]
  have he (E : Finset (Fin d)) :
      (¬ ∃ j ∈ E, r j = true) ↔
        E ⊆ Finset.univ.filter (fun j : Fin d => r j = false) := by
    simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hn j hj
      cases hr : r j
      · rfl
      · exact False.elim (hn ⟨j, hj, hr⟩)
    · intro hn ⟨j, hj, ht⟩
      have := hn hj
      simp [ht] at this
  calc
    _ = ∑ E : Finset (Fin d), if E ⊆ Finset.univ.filter
        (fun j : Fin d => r j = false) then rowSubsetEnergy d h E else 0 := by
      apply Finset.sum_congr rfl
      intro E _
      by_cases hr : ∃ j ∈ E, r j = true
      · simp [hr, show ¬ E ⊆ Finset.univ.filter (fun j : Fin d => r j = false)
          from fun hs => (he E).mpr hs hr]
      · simp [hr, (he E).mp hr]
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext E
      simp

/-- Counting hidden subsets by cardinality gives the exact positive-degree
binomial sum, including an empty hidden label set.  [For the stated data and conditions](hyp:d,h,r), [the stated conclusion holds](goal). -/
-- @node: rowHiddenEnergy_by_count
lemma rowHiddenEnergy_by_count (d : ℕ) (h : ℝ) (r : Fin d → Bool) :
    rowHiddenEnergy d h r =
      ∑ k ∈ Finset.Icc 1 (Finset.univ.filter (fun j : Fin d => r j = false)).card,
        (((Finset.univ.filter (fun j : Fin d => r j = false)).card).choose k : ℝ) *
          gamma d h k := by
  classical
  rw [rowHiddenEnergy_eq_powerset]
  let U := Finset.univ.filter (fun j : Fin d => r j = false)
  have hc := Finset.sum_powerset_apply_card
    (fun k => if k = 0 then (0 : ℝ) else gamma d h k) (x := U)
  simp only [Finset.card_eq_zero, nsmul_eq_mul] at hc
  change (∑ E ∈ U.powerset, if E = ∅ then 0 else gamma d h E.card) = _
  rw [hc]
  have hr : Finset.range (U.card + 1) = insert 0 (Finset.Icc 1 U.card) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp)]
  simp only [ite_true, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_neg (by have := (Finset.mem_Icc.mp hk).1; omega)]

/-- The revealed energy is the remainder after the exact hidden-degree sum.  [For the stated data and conditions](hyp:d,h,r), [the stated conclusion holds](goal). -/
-- @node: rowRevealedEnergy_by_count
lemma rowRevealedEnergy_by_count (d : ℕ) (h : ℝ) (r : Fin d → Bool) :
    rowRevealedEnergy d h r = eta d h -
      ∑ k ∈ Finset.Icc 1 (Finset.univ.filter (fun j : Fin d => r j = false)).card,
        (((Finset.univ.filter (fun j : Fin d => r j = false)).card).choose k : ℝ) *
          gamma d h k := by
  have hs := rowRevealEnergy_split d h r
  rw [rowHiddenEnergy_by_count] at hs
  linarith

/-- Row energies depend only on the hidden count; detailed labels can be retained
in the likelihood while these energy factors are reduced to counts.  [For the stated data and conditions](hyp:d,h,r,s,hc), [the stated conclusion holds](goal). -/
-- @node: rowRevealEnergy_eq_of_hidden_count_eq
lemma rowRevealEnergy_eq_of_hidden_count_eq (d : ℕ) (h : ℝ)
    (r s : Fin d → Bool)
    (hc : (Finset.univ.filter (fun j : Fin d => r j = false)).card =
      (Finset.univ.filter (fun j : Fin d => s j = false)).card) :
    rowRevealedEnergy d h r = rowRevealedEnergy d h s ∧
      rowHiddenEnergy d h r = rowHiddenEnergy d h s := by
  constructor
  · simp only [rowRevealedEnergy_by_count, hc]
  · simp only [rowHiddenEnergy_by_count, hc]

/-- The positive-degree factor used by the restricted allocation sum is exactly
hidden row energy, with the zero-degree allocation excluded.  [For the stated data and conditions](hyp:d,h,r,u,hu), [the stated conclusion holds](goal). -/
-- @node: rowHiddenEnergy_fin_degree_sum
lemma rowHiddenEnergy_fin_degree_sum (d : ℕ) (h : ℝ) (r : Fin d → Bool)
    (u : ℕ) (hu : u = (Finset.univ.filter (fun j : Fin d => r j = false)).card) :
    (∑ k : Fin (u + 1), if 0 < k.val then
      (u.choose k.val : ℝ) * gamma d h k.val else 0) = rowHiddenEnergy d h r := by
  classical
  rw [rowHiddenEnergy_by_count, ← hu]
  rw [Fin.sum_univ_eq_sum_range (fun k => if 0 < k then
    (u.choose k : ℝ) * gamma d h k else 0)]
  have hr : Finset.range (u + 1) = insert 0 (Finset.Icc 1 u) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp)]
  simp only [lt_self_iff_false, if_false, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos (by have := (Finset.mem_Icc.mp hk).1; omega)]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
