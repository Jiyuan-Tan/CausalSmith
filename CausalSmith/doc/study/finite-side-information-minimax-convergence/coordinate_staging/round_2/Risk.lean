/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.FiniteSideInformation.Coordinates

/-!
# Finite squared risks

This module defines bounded decision rules for a finite labeled observation,
their finite squared risks, and the continuity and uniform bounds needed by
compact minimax arguments.
-/

open scoped BigOperators
open Set

namespace Causalean.Stat.Minimax.FiniteSideInformation

variable {Theta X C : Type*} [TopologicalSpace Theta] [Fintype X] [Fintype C]

/-- For a [finite labeled alphabet](hyp:X) and [action bounds](hyp:l,u), a
[bounded decision](goal) assigns an action in the closed interval to every label. -/
abbrev BoundedDecision (X : Type*) (l u : ℝ) := X → Set.Icc l u

/-- Given [label probabilities](hyp:p), [a target](hyp:tau), [a bounded decision](hyp:d), and
[a parameter](hyp:theta), the [finite squared risk](goal) is the probability-weighted sum of
squared errors over the labeled alphabet. -/
def finiteSquaredRisk (p : Theta → X → ℝ) (tau : Theta → ℝ)
    (d : BoundedDecision X l u) (theta : Theta) : ℝ :=
  ∑ x, p theta x * (((d x : Set.Icc l u) : ℝ) - tau theta) ^ 2

/-- Given [label probabilities](hyp:p), [a target](hyp:tau), [nonnegative label coordinates](hyp:hp),
a [bounded decision](hyp:d), and a [parameter](hyp:theta), the [finite squared risk is nonnegative](goal). -/
theorem finiteSquaredRisk_nonneg (p : Theta → X → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta x, 0 ≤ p theta x) (d : BoundedDecision X l u) (theta : Theta) :
    0 ≤ finiteSquaredRisk p tau d theta := by
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp theta x) (sq_nonneg _)

/-- Given [label probabilities](hyp:p), [a target](hyp:tau), [nonnegative label coordinates](hyp:hp),
[unit-sum label probabilities](hyp:hsum), [ordered action bounds](hyp:hlu), a [target in those bounds](hyp:htau),
a [bounded decision](hyp:d), and a [parameter](hyp:theta), the [finite squared risk is bounded](goal)
between zero and the squared interval width. -/
theorem finiteSquaredRisk_bounds (p : Theta → X → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta x, 0 ≤ p theta x) (hsum : ∀ theta, ∑ x, p theta x = 1)
    (hlu : l ≤ u) (htau : ∀ theta, tau theta ∈ Set.Icc l u)
    (d : BoundedDecision X l u) (theta : Theta) :
    0 ≤ finiteSquaredRisk p tau d theta ∧ finiteSquaredRisk p tau d theta ≤ (u - l) ^ 2 := by
  refine ⟨finiteSquaredRisk_nonneg p tau hp d theta, ?_⟩
  calc
    finiteSquaredRisk p tau d theta ≤ ∑ x, p theta x * (u - l) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hp theta x)
      have hd := (d x).2
      have ht := htau theta
      have hdiff_le : (d x : ℝ) - tau theta ≤ u - l := sub_le_sub hd.2 ht.1
      have hneg_diff_le : -(u - l) ≤ (d x : ℝ) - tau theta := by
        linarith [hd.1, ht.2]
      nlinarith [mul_nonneg (sub_nonneg.mpr hdiff_le)
        (by linarith : 0 ≤ (u - l) + ((d x : ℝ) - tau theta))]
    _ = (u - l) ^ 2 := by
      rw [← Finset.sum_mul, hsum theta, one_mul]

/-- Given [label probabilities](hyp:p), a [target](hyp:tau), [continuous label coordinates](hyp:hp),
a [continuous target](hyp:htau), and a [bounded decision](hyp:d), the [finite squared risk is continuous](goal)
in the parameter. -/
theorem continuous_finiteSquaredRisk (p : Theta → X → ℝ) (tau : Theta → ℝ)
    (hp : ∀ x, Continuous (fun theta ↦ p theta x)) (htau : Continuous tau)
    (d : BoundedDecision X l u) :
    Continuous (fun theta ↦ finiteSquaredRisk p tau d theta) := by
  unfold finiteSquaredRisk
  fun_prop

/-- Given [label probabilities](hyp:p), a [target](hyp:tau), [continuous label coordinates](hyp:hp),
and a [continuous target](hyp:htau), the [finite squared risk is jointly continuous](goal) in the
bounded decision and parameter. -/
theorem continuous_finiteSquaredRisk_joint (p : Theta → X → ℝ) (tau : Theta → ℝ)
    (hp : ∀ x, Continuous (fun theta ↦ p theta x)) (htau : Continuous tau) :
    Continuous (fun z : BoundedDecision X l u × Theta ↦
      finiteSquaredRisk p tau z.1 z.2) := by
  unfold finiteSquaredRisk
  fun_prop

/-- Given [ordered action bounds](hyp:hlu), the space of [bounded decisions on a finite alphabet](hyp:X)
is [compact](goal). -/
theorem isCompact_boundedDecision (hlu : l ≤ u) :
    IsCompact (Set.univ : Set (BoundedDecision X l u)) := by
  exact isCompact_univ

end Causalean.Stat.Minimax.FiniteSideInformation
