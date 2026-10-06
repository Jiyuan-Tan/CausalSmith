module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.VectorChannel
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Range

/-!
# Helpers/PrivateMoments

Finite original-record private value frontiers: Helpers/PrivateMoments.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {m d : ℕ}
-- @node: def:private-moments
/-- Fix [the function W](hyp:W), [the order](hyp:k), and [the coordinate index](hyp:j). [Distinct-person unbiased power statistic including degree zero](goal). -/
def privateMoment (W : Fin m → Fin d → ℝ) (k : ℕ) (j : Fin d) : ℝ :=
  (Nat.choose m k : ℝ)⁻¹ * ∑ J ∈ Finset.univ.powersetCard k, ∏ i ∈ J, W i j
  -- @realizes \mathsf U(distinct-person power) @realizes J(k-subset of participants) @realizes k(moment degree)
/-- Fix [the function w](hyp:w). [Structural elementary-symmetric recursion, avoiding subset enumeration](goal). -/
def elementaryMoment (w : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | m+1, k+1 => elementaryMoment w m (k+1) + w m * elementaryMoment w m k
/-- Assume [the stated hx condition](hyp:hx). [Splitting subsets according to whether they contain the new participant](goal). -/
-- @node: sum_powersetCard_insert_product
lemma sum_powersetCard_insert_product (w : ℕ → ℝ) (s : Finset ℕ) (x k : ℕ)
    (hx : x ∉ s) :
    (∑ J ∈ (insert x s).powersetCard (k+1), ∏ i ∈ J, w i) =
      (∑ J ∈ s.powersetCard (k+1), ∏ i ∈ J, w i) +
        w x * (∑ J ∈ s.powersetCard k, ∏ i ∈ J, w i) := by
  classical
  have hnot : ∀ J ∈ s.powersetCard k, x ∉ J := by
    intro J hJ hxJ
    exact hx ((Finset.mem_powersetCard.mp hJ).1 hxJ)
  rw [Finset.powersetCard_succ_insert hx]
  rw [Finset.sum_union]
  · congr 1
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      exact Finset.prod_insert (hnot J hJ)
    · intro J hJ K hK hJK
      apply Finset.ext
      intro i
      have hi := Finset.ext_iff.mp hJK i
      by_cases hix : i = x
      · subst i
        simp [hnot J hJ, hnot K hK]
      · simpa [hix] using hi
  · apply Finset.disjoint_left.mpr
    intro J hJ hJi
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hJi
    exact hx ((Finset.mem_powersetCard.mp hJ).1 (Finset.mem_insert_self _ _))

/-- [The structural recursion enumerates products over subsets of a finite range](goal). -/
-- @node: elementaryMoment_eq_range_sum
lemma elementaryMoment_eq_range_sum (w : ℕ → ℝ) (m k : ℕ) :
    elementaryMoment w m k = ∑ J ∈ (Finset.range m).powersetCard k, ∏ i ∈ J, w i := by
  classical
  induction m generalizing k with
  | zero =>
    cases k with
    | zero => simp [elementaryMoment]
    | succ k =>
      have hempty : (∅ : Finset ℕ).powersetCard (k+1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [elementaryMoment, hempty]
  | succ m ih =>
    cases k with
    | zero => simp [elementaryMoment]
    | succ k =>
      rw [elementaryMoment, ih, ih, Finset.range_add_one,
        sum_powersetCard_insert_product w (Finset.range m) m k (by simp)]

/-- [Recursion agrees with the private moment subset formula](goal). -/
-- @node: privateMoment_eq_recursion
lemma privateMoment_eq_recursion (W : Fin m → Fin d → ℝ) (k : ℕ) (j : Fin d) :
    privateMoment W k j = (Nat.choose m k : ℝ)⁻¹ *
      elementaryMoment (fun i => if h : i < m then W ⟨i,h⟩ j else 0) m k := by
  classical
  unfold privateMoment
  congr 1
  rw [elementaryMoment_eq_range_sum]
  let e : Fin m ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have he : (Finset.univ : Finset (Fin m)).map e = Finset.range m := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.isLt, fun hi => ⟨⟨i, hi⟩, rfl⟩⟩
  rw [← he, Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro J hJ
  change (∏ i ∈ J, W i j) =
    ∏ i ∈ J.map e, (if h : i < m then W ⟨i,h⟩ j else 0)
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i hi
  simp [e, i.isLt]



end CausalSmith.Stat.LdpOptvalueUniformFrontier
