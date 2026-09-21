/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-! # Deterministic accounting for predictable budget stopping

This module isolates the finite-sum argument used when a predictable process
is stopped before either of two nonnegative cumulative budgets is exceeded.
It is purely deterministic and does not mention filtrations or conditional
expectations.
-/

namespace Causalean.Stat

open scoped BigOperators

/-- Given [two sequences of budget charges](hyp:x,y), [two budgets](hyp:K,delta), and [a time
index](hyp:k), the [budget multiplier at that time](goal) is one exactly when both cumulative
charges through `k` remain within budget, and zero otherwise. -/
noncomputable def budgetMultiplier (x y : ℕ → ℝ) (K delta : ℝ) (k : ℕ) : ℝ :=
  if (∑ j ∈ Finset.range (k + 1), x j) ≤ K ∧
      (∑ j ∈ Finset.range (k + 1), y j) ≤ delta then 1 else 0

/-- If [both charge sequences are nonnegative before the row length](hyp:hx,hy)
and [both budgets are nonnegative](hyp:hK,hdelta), then [the total charges
selected by the through-time budget multiplier do not exceed their respective
budgets](goal).  The result permits the charge that first crosses a budget to
be discarded and uses no probabilistic assumptions. -/
theorem budgetWeightedSums_le
    (x y : ℕ → ℝ) (K delta : ℝ) (r : ℕ)
    (hx : ∀ k < r, 0 ≤ x k) (hy : ∀ k < r, 0 ≤ y k)
    (hK : 0 ≤ K) (hdelta : 0 ≤ delta) :
    (∑ k ∈ Finset.range r, budgetMultiplier x y K delta k * x k) ≤ K ∧
      (∑ k ∈ Finset.range r, budgetMultiplier x y K delta k * y k) ≤ delta := by
  /-
  Induct on `r`.  At the successor step, split on whether the two full
  prefixes through the new last index satisfy their budgets.  If they do,
  nonnegativity implies every earlier prefix also satisfies its budgets, so
  all multipliers are one and the selected sums are the full prefix sums.  If
  either full prefix fails, the new multiplier is zero and the induction
  hypothesis bounds the unchanged selected sums.  Useful rewrites are
  `Finset.sum_range_succ`, `Finset.mem_range`, and `budgetMultiplier`.
  -/
  induction r with
  | zero =>
      simpa using And.intro hK hdelta
  | succ r ih =>
      have hx' : ∀ k < r, 0 ≤ x k := fun k hk => hx k (Nat.lt_succ_of_lt hk)
      have hy' : ∀ k < r, 0 ≤ y k := fun k hk => hy k (Nat.lt_succ_of_lt hk)
      have ih_bounds := ih hx' hy'
      by_cases hfull :
          (∑ j ∈ Finset.range (r + 1), x j) ≤ K ∧
            (∑ j ∈ Finset.range (r + 1), y j) ≤ delta
      · have hprefix (k : ℕ) (hk : k < r + 1) :
            (∑ j ∈ Finset.range (k + 1), x j) ≤ K ∧
              (∑ j ∈ Finset.range (k + 1), y j) ≤ delta := by
          have hsub : Finset.range (k + 1) ⊆ Finset.range (r + 1) :=
            Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt_succ hk))
          constructor
          · exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i hi _ => hx i (Finset.mem_range.mp hi))).trans hfull.1
          · exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i hi _ => hy i (Finset.mem_range.mp hi))).trans hfull.2
        have hmul (k : ℕ) (hk : k < r + 1) :
            budgetMultiplier x y K delta k = 1 := by
          simp [budgetMultiplier, hprefix k hk]
        constructor
        · calc
            (∑ k ∈ Finset.range (r + 1),
                budgetMultiplier x y K delta k * x k) =
                ∑ k ∈ Finset.range (r + 1), x k := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [hmul k (Finset.mem_range.mp hk), one_mul]
            _ ≤ K := hfull.1
        · calc
            (∑ k ∈ Finset.range (r + 1),
                budgetMultiplier x y K delta k * y k) =
                ∑ k ∈ Finset.range (r + 1), y k := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [hmul k (Finset.mem_range.mp hk), one_mul]
            _ ≤ delta := hfull.2
      · have hlast : budgetMultiplier x y K delta r = 0 := by
          simp [budgetMultiplier, hfull]
        simpa [Finset.sum_range_succ, hlast] using ih_bounds

end Causalean.Stat
