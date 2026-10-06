/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Order.Interval.Set.Union
public import Mathlib.Tactic.Order

/-!
# Finite partitions by ordered intervals

This file defines measurable finite partitions of a closed interval and constructs one from an
ordered sequence of cut points. All cells except the last are left closed and right open; the last
cell is closed at both ends.
-/

@[expose] public section

open MeasureTheory Set

namespace Causalean.Mathlib.MeasureTheory

/-- A [family of `k` sets](hyp:k,B) is [a measurable partition](goal) of the [closed interval from
`a` to `b`](hyp:a,b) when its cells are measurable, pairwise disjoint, and cover that interval. -/
def IsIntervalPartition {α : Type*} [MeasurableSpace α] [Preorder α]
    (a b : α) (k : ℕ) (B : Fin k → Set α) : Prop :=
  (∀ j, MeasurableSet (B j)) ∧
  (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
  (⋃ j, B j) = Set.Icc a b

/-- For [ordered cut points `f` through index `n`](hyp:f,n,hf), [the union of their consecutive
left-closed, right-open cells is the interval from the first through the last cut point](goal). -/
lemma orderedHalfOpenIntervals_cover {α : Type*} [LinearOrder α]
    (f : ℕ → α) (n : ℕ) (hf : ∀ i j, i ≤ j → j ≤ n → f i ≤ f j) :
    (⋃ j ∈ Finset.range n, Set.Ico (f j) (f (j + 1))) = Set.Ico (f 0) (f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i j hij hj => hf i j hij (hj.trans (Nat.le_succ n)))
    simp only [Finset.range_add_one, Finset.mem_insert, Set.iUnion_or]
    rw [Set.iUnion_union_distrib]
    simp only [Set.iUnion_iUnion_eq_left, ih']
    simpa [Set.union_comm] using (Set.Ico_union_Ico_eq_Ico
      (hf 0 n (Nat.zero_le n) (Nat.le_succ n))
      (hf n (n + 1) (Nat.le_succ n) le_rfl))

/-- Given [a positive number `k` of cells](hyp:k,hk) and [ordered cut points `f` through index
`k`](hyp:f,hf), [the consecutive half-open cells, with a closed final cell, measurably partition
the closed interval from the first to the last cut point](goal). -/
lemma orderedIntervalCells_partition {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [LinearOrder α] [BorelSpace α] [OrderClosedTopology α]
    (f : ℕ → α) (k : ℕ) (hk : 0 < k)
    (hf : ∀ i j, i ≤ j → j ≤ k → f i ≤ f j) :
    IsIntervalPartition (f 0) (f k) k
      (fun j : Fin k => if j.val + 1 = k then
        Set.Icc (f j.val) (f (j.val + 1))
       else Set.Ico (f j.val) (f (j.val + 1))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro j
    change MeasurableSet (if j.val + 1 = k then
      Set.Icc (f j.val) (f (j.val + 1)) else
      Set.Ico (f j.val) (f (j.val + 1)))
    split_ifs
    · exact measurableSet_Icc
    · exact measurableSet_Ico
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hji : i.val ≠ j.val := Fin.val_ne_of_ne hij
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hi : i.val + 1 ≠ k := by omega
      simp only [hi, ↓reduceIte, Set.mem_Ico] at hxi
      have hlow : f j.val ≤ x := by
        change x ∈ (if j.val + 1 = k then Set.Icc (f j.val) (f (j.val + 1))
          else Set.Ico (f j.val) (f (j.val + 1))) at hxj
        split_ifs at hxj <;> exact hxj.1
      have horder : f (i.val + 1) ≤ f j.val :=
        hf _ _ (by omega) (Nat.le_of_lt j.isLt)
      exact (not_lt_of_ge (horder.trans hlow) hxi.2).elim
    · have hj : j.val + 1 ≠ k := by omega
      simp only [hj, ↓reduceIte, Set.mem_Ico] at hxj
      have hlow : f i.val ≤ x := by
        change x ∈ (if i.val + 1 = k then Set.Icc (f i.val) (f (i.val + 1))
          else Set.Ico (f i.val) (f (i.val + 1))) at hxi
        split_ifs at hxi <;> exact hxi.1
      have horder : f (j.val + 1) ≤ f i.val :=
        hf _ _ (by omega) (Nat.le_of_lt i.isLt)
      exact (not_lt_of_ge (horder.trans hlow) hxj.2).elim
  · let n := k - 1
    have hn : n + 1 = k := by dsimp [n]; omega
    have hnlt : n < k := by omega
    have hcover := orderedHalfOpenIntervals_cover f n
      (fun i j hij hj => hf i j hij (by omega))
    have hchain : Set.Ico (f 0) (f n) ∪ Set.Icc (f n) (f k) =
        Set.Icc (f 0) (f k) :=
      Set.Ico_union_Icc_eq_Icc (hf 0 n (Nat.zero_le n) (by omega))
        (hf n k (by omega) le_rfl)
    rw [← hchain, ← hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨j, hjx⟩ := Set.mem_iUnion.mp hx
      by_cases hj : j.val + 1 = k
      · right
        have hval : j.val = n := by omega
        simpa [hval, hn] using hjx
      · left
        have hjn : j.val < n := by omega
        refine Set.mem_iUnion.mpr ⟨j.val, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hjn, ?_⟩⟩
        simpa [hj] using hjx
    · rintro (hx | hx)
      · obtain ⟨j, hjx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hj, hjx⟩ := Set.mem_iUnion.mp hjx
        have hjlt : j < k := by have := Finset.mem_range.mp hj; omega
        let q : Fin k := ⟨j, hjlt⟩
        refine Set.mem_iUnion.mpr ⟨q, ?_⟩
        have hne : j + 1 ≠ k := by have := Finset.mem_range.mp hj; omega
        simpa [q, hne] using hjx
      · let q : Fin k := ⟨n, hnlt⟩
        refine Set.mem_iUnion.mpr ⟨q, ?_⟩
        simpa [q, hn] using hx

end Causalean.Mathlib.MeasureTheory
