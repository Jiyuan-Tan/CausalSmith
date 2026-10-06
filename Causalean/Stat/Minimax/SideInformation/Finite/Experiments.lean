/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.SideInformation.Finite.Risk
public import Causalean.Stat.Minimax.MinimaxValue

/-!
# Exact and empirical finite side-information experiments

This module defines the two decision problems compared by the convergence
theorem: exact observation of a finite side-law vector, and observation of a
finite iid side sample.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Set

namespace Causalean.Stat.Minimax.FiniteSideInformation

open Causalean.Stat

variable {Theta X C : Type*} [Fintype X] [Fintype C]

/-- Given a [labeled alphabet](hyp:X), a [side alphabet](hyp:C), and [action bounds](hyp:l,u),
an [exact-side procedure](goal) assigns a bounded action after observing a label and its exact
finite side-law vector. -/
abbrev ExactSideProcedure (X C : Type*) [Fintype C] (l u : ℝ) :=
  X → FinitePmf C → Set.Icc l u

/-- Given a [labeled alphabet](hyp:X), a [side alphabet](hyp:C), a [sample size](hyp:m), and
[action bounds](hyp:l,u), an [empirical-side procedure](goal) assigns a bounded action after
observing a label and ordered side draws. -/
abbrev EmpiricalSideProcedure (X C : Type*) (m : ℕ) (l u : ℝ) :=
  X → (Fin m → C) → Set.Icc l u

/-- Given [side-probability coordinates](hyp:q) that are [simplex-valid](hyp:hq), the
[side law at a parameter](hyp:theta) is the [corresponding finite probability vector](goal). -/
def sidePmf (q : Theta → C → ℝ) (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (theta : Theta) : FinitePmf C :=
  ⟨q theta, hq theta⟩

/-- When [side-probability coordinates](hyp:q) are [simplex-valid](hyp:hq) and
[continuous](hyp:hqcont), the [simplex-valued side law is continuous](goal). -/
theorem continuous_sidePmf [TopologicalSpace Theta]
    (q : Theta → C → ℝ) (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hqcont : ∀ c, Continuous (fun theta ↦ q theta c)) :
    Continuous (sidePmf q hq) := by
  exact continuous_induced_rng.2 (continuous_pi hqcont)

/-- Given [label and side probabilities](hyp:p,q,hq), [a target](hyp:tau), an
[exact-side procedure](hyp:d), and a [parameter](hyp:theta), the [exact-side squared risk](goal)
averages only over the labeled outcome because the side-law vector is observed without noise. -/
def exactSideRisk (p : Theta → X → ℝ) (q : Theta → C → ℝ)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C) (tau : Theta → ℝ)
    (d : ExactSideProcedure X C l u) (theta : Theta) : ℝ :=
  ∑ x, p theta x * (((d x (sidePmf q hq theta) : Set.Icc l u) : ℝ) - tau theta) ^ 2

/-- Given [label and side probabilities](hyp:p,q,hq), [a target](hyp:tau), an
[empirical-side procedure](hyp:d), a [sample size](hyp:m), and a [parameter](hyp:theta), the
[empirical-side squared risk](goal) averages squared loss over the label and all ordered iid side samples. -/
def empiricalSideRisk (p : Theta → X → ℝ) (q : Theta → C → ℝ)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C) (tau : Theta → ℝ) (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) (theta : Theta) : ℝ :=
  ∑ x, p theta x * ∑ z : Fin m → C,
    productProbability C (sidePmf q hq theta) z * ((d x z : ℝ) - tau theta) ^ 2

/-- Given [label probabilities](hyp:p), [side probabilities](hyp:q,hq), a [target](hyp:tau),
and [action bounds](hyp:l,u), the [exact-side minimax value](goal) is the infimum over bounded
exact-law procedures of their worst-case squared risk over the parameter space. -/
noncomputable def exactSideMinimaxValue (p : Theta → X → ℝ)
    (q : Theta → C → ℝ) (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (tau : Theta → ℝ) (l u : ℝ) : ℝ :=
  minimaxValueReal
    (exactSideRisk p q hq tau : ExactSideProcedure X C l u → Theta → ℝ)

/-- Given [label probabilities](hyp:p), [side probabilities](hyp:q,hq), a [target](hyp:tau),
and [action bounds](hyp:l,u), the [standard exact-side minimax value](goal) is the extended
nonnegative infimum of worst-case squared risks. -/
noncomputable def exactSideMinimaxValueENNReal (p : Theta → X → ℝ)
    (q : Theta → C → ℝ) (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (tau : Theta → ℝ) (l u : ℝ) : ℝ≥0∞ :=
  minimaxValueENNRealOfReal
    (exactSideRisk p q hq tau : ExactSideProcedure X C l u → Theta → ℝ)

/-- Given [label probabilities](hyp:p), [side probabilities](hyp:q,hq), a [target](hyp:tau),
[action bounds](hyp:l,u), and a [sample size](hyp:m), the [empirical-side minimax value](goal)
is the infimum over bounded sample procedures of their worst-case squared risk over the parameter space. -/
noncomputable def empiricalSideMinimaxValue (p : Theta → X → ℝ)
    (q : Theta → C → ℝ) (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (tau : Theta → ℝ) (l u : ℝ) (m : ℕ) : ℝ :=
  minimaxValueReal
    (empiricalSideRisk p q hq tau m :
      EmpiricalSideProcedure X C m l u → Theta → ℝ)

/-- Given [label probabilities](hyp:p), [side probabilities](hyp:q,hq), a [target](hyp:tau),
[action bounds](hyp:l,u), and a [sample size](hyp:m), the [standard empirical-side minimax
value](goal) is the extended nonnegative infimum of worst-case squared risks. -/
noncomputable def empiricalSideMinimaxValueENNReal (p : Theta → X → ℝ)
    (q : Theta → C → ℝ) (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (tau : Theta → ℝ) (l u : ℝ) (m : ℕ) : ℝ≥0∞ :=
  minimaxValueENNRealOfReal
    (empiricalSideRisk p q hq tau m :
      EmpiricalSideProcedure X C m l u → Theta → ℝ)

/-- Under [probability-simplex label and side coordinates](hyp:hp,hq), empirical-side
[squared risk is nonnegative](goal). -/
theorem empiricalSideRisk_nonneg (p : Theta → X → ℝ) (q : Theta → C → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C) (tau : Theta → ℝ) (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) (theta : Theta) :
    0 ≤ empiricalSideRisk p q hq tau m d theta := by
  unfold empiricalSideRisk
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg ((hp theta).1 x)
  apply Finset.sum_nonneg
  intro z _
  exact mul_nonneg (productProbability_nonneg C (sidePmf q hq theta) z) (sq_nonneg _)

/-- Under [probability-simplex label and side coordinates](hyp:hp,hq), with [ordered action
bounds containing the target](hyp:hlu,htau), empirical-side [squared risk is at most the
squared action width](goal). -/
theorem empiricalSideRisk_le (p : Theta → X → ℝ) (q : Theta → C → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C) (tau : Theta → ℝ)
    (hlu : l ≤ u) (htau : ∀ theta, tau theta ∈ Set.Icc l u) (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) (theta : Theta) :
    empiricalSideRisk p q hq tau m d theta ≤ (u - l) ^ 2 := by
  unfold empiricalSideRisk
  calc
    ∑ x, p theta x * ∑ z : Fin m → C,
        productProbability C (sidePmf q hq theta) z * ((d x z : ℝ) - tau theta) ^ 2 ≤
        ∑ x, p theta x * (u - l) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ ((hp theta).1 x)
      calc
        ∑ z : Fin m → C,
            productProbability C (sidePmf q hq theta) z * ((d x z : ℝ) - tau theta) ^ 2 ≤
            ∑ z : Fin m → C,
              productProbability C (sidePmf q hq theta) z * (u - l) ^ 2 := by
          apply Finset.sum_le_sum
          intro z _
          apply mul_le_mul_of_nonneg_left _
            (productProbability_nonneg C (sidePmf q hq theta) z)
          have hd := (d x z).2
          have ht := htau theta
          have hdiff_le : (d x z : ℝ) - tau theta ≤ u - l :=
            sub_le_sub hd.2 ht.1
          have hneg_diff_le : -(u - l) ≤ (d x z : ℝ) - tau theta := by
            linarith [hd.1, ht.2]
          nlinarith [hlu, mul_nonneg (sub_nonneg.mpr hdiff_le)
            (by linarith : 0 ≤ (u - l) + ((d x z : ℝ) - tau theta))]
        _ = (u - l) ^ 2 := by
          rw [← Finset.sum_mul, sum_productProbability]
          exact one_mul _
    _ = (u - l) ^ 2 := by
      rw [← Finset.sum_mul, (hp theta).2]
      exact one_mul _

end Causalean.Stat.Minimax.FiniteSideInformation
