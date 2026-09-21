/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Loss functions for the standalone ML module

This file collects the elementary pointwise loss functions used throughout
`Causalean.ML`: squared loss for regression, Boolean-to-real encoding, softplus,
and score-space logistic loss for binary classification. Logistic models use
Mathlib's canonical `Real.sigmoid`. Everything here is causal-free real
analysis; no probability or causal layer is imported.
-/

@[expose] public section

namespace Causalean.ML

/-- [Squared loss](goal) measures [a real-valued prediction](hyp:ŷ) against
[the observed outcome](hyp:y) by [squaring their difference](step:1).

It measures prediction error by its square. -/
def squaredLoss (ŷ y : ℝ) : ℝ := (y - ŷ) ^ 2

/-- [The zero--one real encoding](goal) makes [a Boolean label](hyp:b) available to real-valued
loss formulas by [mapping true to one and false to zero](step:1).

This lets real-valued loss formulas use binary labels. -/
def bool01 (b : Bool) : ℝ := if b then 1 else 0

/-- [Softplus](goal) turns [an unrestricted real score](hyp:t) into
[the log of one plus its exponential](step:1), a smooth positive quantity used in logistic loss.

It is a smooth positive transformation used to express logistic losses in score space. -/
noncomputable def softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)

/-- [The score-space logistic loss](goal) evaluates [a binary outcome](hyp:y) at
[an unrestricted prediction score](hyp:t) as
[softplus minus the zero--one label times the score](step:1).

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

/-- [Squared prediction error cannot be negative](goal), regardless of
[the predicted and observed values](hyp:ŷ,y). -/
lemma squaredLoss_nonneg (ŷ y : ℝ) : 0 ≤ squaredLoss ŷ y := sq_nonneg _

/-- Softplus is strictly positive at every score. -/
lemma softplus_pos (t : ℝ) : 0 < softplus t := by
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos _
  have h1 : (1 : ℝ) < 1 + Real.exp t := by linarith
  exact Real.log_pos h1

end Causalean.ML
