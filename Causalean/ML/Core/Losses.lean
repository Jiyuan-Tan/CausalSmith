/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Loss functions for the standalone ML module

This file collects the elementary pointwise loss functions used throughout
`Causalean.ML`: the squared loss for regression, and the sigmoid / softplus /
score-space logistic loss for binary classification.  Everything here is
causal-free real analysis; no probability or causal layer is imported.
-/

namespace Causalean.ML

/-- For [a real-valued prediction $\hat y$](hyp:ŷ) and [a real-valued observed outcome $y$](hyp:y), the [squared loss](goal) is $(y-\hat y)^2$.

It measures prediction error by its square. -/
def squaredLoss (ŷ y : ℝ) : ℝ := (y - ŷ) ^ 2

/-- For [a binary label](hyp:b), the [zero--one real-valued encoding of that label](goal) is one when the label is true and zero when it is false.

This lets real-valued loss formulas use binary labels. -/
def bool01 (b : Bool) : ℝ := if b then 1 else 0

/-- For [a real-valued score $t$](hyp:t), the [logistic sigmoid](goal) is $(1+\exp(-t))^{-1}$.

It maps scores to values strictly between zero and one. -/
noncomputable def sigmoid (t : ℝ) : ℝ := (1 + Real.exp (-t))⁻¹

/-- For [a real-valued score $t$](hyp:t), the [softplus transformation](goal) is $\log(1+\exp t)$.

It is a smooth positive transformation used to express logistic losses in score space. -/
noncomputable def softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)

/-- For [a binary outcome $y$](hyp:y) and [a real-valued prediction score $t$](hyp:t), the [logistic score loss](goal) is $\log(1+\exp t)-y_0t$, where $y_0$ is one when $y$ is true and zero when $y$ is false.

This is binary cross-entropy written as a function of an unrestricted prediction score. -/
noncomputable def logisticScoreLoss (y : Bool) (t : ℝ) : ℝ :=
  softplus t - bool01 y * t

/-- [A true Boolean label is encoded as the real number one](goal). -/
@[simp] lemma bool01_true : bool01 true = 1 := rfl

/-- A false Boolean label is encoded as zero. -/
@[simp] lemma bool01_false : bool01 false = 0 := rfl

/-- The zero-one encoding of a Boolean label is always nonnegative. -/
lemma bool01_nonneg (b : Bool) : 0 ≤ bool01 b := by
  cases b <;> simp [bool01]

/-- The zero-one encoding of a Boolean label is always at most one. -/
lemma bool01_le_one (b : Bool) : bool01 b ≤ 1 := by
  cases b <;> simp [bool01]

/-- Squared loss is always nonnegative. -/
lemma squaredLoss_nonneg (ŷ y : ℝ) : 0 ≤ squaredLoss ŷ y := sq_nonneg _

/-- The logistic sigmoid is strictly positive at every score. -/
lemma sigmoid_pos (t : ℝ) : 0 < sigmoid t := by
  have : 0 < 1 + Real.exp (-t) := by positivity
  exact inv_pos.mpr this

/-- The logistic sigmoid is strictly below one at every score. -/
lemma sigmoid_lt_one (t : ℝ) : sigmoid t < 1 := by
  have hpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have h1 : (1 : ℝ) < 1 + Real.exp (-t) := by linarith
  calc sigmoid t = (1 + Real.exp (-t))⁻¹ := rfl
    _ < 1 := by
        rw [inv_lt_one_iff₀]
        right; exact h1

/-- Softplus is strictly positive at every score. -/
lemma softplus_pos (t : ℝ) : 0 < softplus t := by
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos _
  have h1 : (1 : ℝ) < 1 + Real.exp t := by linarith
  exact Real.log_pos h1

end Causalean.ML
