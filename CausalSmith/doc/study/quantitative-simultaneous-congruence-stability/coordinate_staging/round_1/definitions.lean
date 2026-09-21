/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Quantitative simultaneous-congruence stability: definitions

This module gives paper-independent definitions for the residual of a finite family of
real congruence equations, quantitative affine separation of their prescribed diagonal
vectors, normalization and conditioning assumptions, and the explicit constants used by
the stability theorem.

The matrix norm in this API is the Euclidean (`ℓ²`) operator norm.
-/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.Quantitative

/-- A `d × d` real square matrix. -/
abbrev SqMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The defect of `B` in one prescribed congruence equation is
`B A Bᵀ - diagonal(s)`. -/
def congruenceDefect {d : ℕ} (A : SqMatrix d) (s : Fin d → ℝ) (B : SqMatrix d) :
    SqMatrix d :=
  B * A * B.transpose - Matrix.diagonal s

/-- The simultaneous-congruence residual is the largest Euclidean operator norm of the
congruence defects over the nonempty finite family. -/
def simultaneousCongruenceResidual {d : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B : SqMatrix d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun e => ‖congruenceDefect (A e) (s e) B‖

/-- For [a finite real matrix family](hyp:A), [its prescribed diagonal shifts](hyp:s), and
[a candidate change of coordinates](hyp:B), [the simultaneous-congruence residual is
nonnegative](goal). -/
theorem simultaneousCongruenceResidual_nonneg {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E] (A : E → SqMatrix d) (s : E → Fin d → ℝ)
    (B : SqMatrix d) :
    0 ≤ simultaneousCongruenceResidual A s B := by
  classical
  let e : E := Classical.choice ‹Nonempty E›
  exact (norm_nonneg _).trans
    (Finset.le_sup' (fun e => ‖congruenceDefect (A e) (s e) B‖) (Finset.mem_univ e))

/-- For [a finite real matrix family](hyp:A), [its prescribed diagonal shifts](hyp:s), [a
candidate change of coordinates](hyp:B), and [a tolerance](hyp:ε), [the simultaneous
residual is at most that tolerance exactly when every individual congruence defect is](goal). -/
theorem simultaneousCongruenceResidual_le_iff {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E] (A : E → SqMatrix d) (s : E → Fin d → ℝ)
    (B : SqMatrix d) (ε : ℝ) :
    simultaneousCongruenceResidual A s B ≤ ε ↔
      ∀ e, ‖congruenceDefect (A e) (s e) B‖ ≤ ε := by
  classical
  simp only [simultaneousCongruenceResidual, Finset.sup'_le_iff, Finset.mem_univ,
    forall_const]

/-- A shift-vector family has affine minor separation `δ` when some base environment and
`d` selected environments form a shift-difference matrix whose determinant has absolute
value at least `δ`. -/
def AffineMinorSeparated {d : ℕ} {E : Type*} [Fintype E]
    (s : E → Fin d → ℝ) (δ : ℝ) : Prop :=
  ∃ (base : E) (pick : Fin d → E),
    δ ≤ |Matrix.det (fun i j => s (pick i) j - s base j)|

/-- The shift family has scale at most `L` when every prescribed diagonal coordinate has
absolute value at most `L`. -/
def ShiftScaleBound {d : ℕ} {E : Type*} [Fintype E]
    (s : E → Fin d → ℝ) (L : ℝ) : Prop :=
  ∀ e i, |s e i| ≤ L

/-- A square matrix has unit-diagonal normalization when every diagonal entry equals one. -/
def UnitDiagonal {d : ℕ} (B : SqMatrix d) : Prop :=
  ∀ i, B i i = 1

/-- The Euclidean operator-norm condition number is `‖B‖ ‖B⁻¹‖`. -/
def operatorConditionNumber {d : ℕ} (B : SqMatrix d) : ℝ :=
  ‖B‖ * ‖B⁻¹‖

/-- A matrix is boundedly conditioned by `κ` when it is nonsingular and its Euclidean
operator-norm condition number is at most `κ`. -/
def WellConditioned {d : ℕ} (κ : ℝ) (B : SqMatrix d) : Prop :=
  IsUnit B.det ∧ operatorConditionNumber B ≤ κ

/-- A reference/candidate pair obeys the same operator-norm condition bound. -/
def PairConditionBound {d : ℕ} (κ : ℝ) (B₀ B : SqMatrix d) : Prop :=
  WellConditioned κ B₀ ∧ WellConditioned κ B

/-- A reference/candidate pair has operator-norm scale at most `R`. -/
def PairMatrixScaleBound {d : ℕ} (R : ℝ) (B₀ B : SqMatrix d) : Prop :=
  ‖B₀‖ ≤ R ∧ ‖B‖ ≤ R

/-- The change-of-coordinates matrix carrying an invertible reference matrix to a
candidate is `B B₀⁻¹`. -/
def transition {d : ℕ} (B₀ B : SqMatrix d) : SqMatrix d :=
  B * B₀⁻¹

/-- The reference exactly realizes all prescribed diagonal congruences. -/
def ExactCongruence {d : ℕ} {E : Type*} [Fintype E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B₀ : SqMatrix d) : Prop :=
  ∀ e, B₀ * A e * B₀.transpose = Matrix.diagonal (s e)

/-- The candidate realizes every prescribed diagonal congruence up to operator-norm error
`ε`. -/
def ApproximateCongruence {d : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B : SqMatrix d) (ε : ℝ) : Prop :=
  simultaneousCongruenceResidual A s B ≤ ε

/-- Cramer's-rule amplification for an affine shift minor of determinant margin `δ` and
entry scale `2L`. -/
def affineSolveFactor (d : ℕ) (L δ : ℝ) : ℝ :=
  (d : ℝ) * (Nat.factorial (d - 1) : ℝ) * (2 * L) ^ (d - 1) / δ

/-- The coordinate-product error factor, including the factor two from subtracting the
base-environment congruence equation. -/
def productControlFactor (d : ℕ) (L δ : ℝ) : ℝ :=
  2 * affineSolveFactor d L δ

/-- The explicit linear stability modulus in Euclidean operator norm.  It displays the
dimension, shift scale, affine separation, matrix scale, and condition-number envelope. -/
def stabilityConstant (d : ℕ) (L δ R κ : ℝ) : ℝ :=
  2 * (d : ℝ) * R * max 1 κ * productControlFactor d L δ

/-- The explicit small-residual threshold used to select the unit-diagonal branch and
upgrade square-root coordinate control to linear control. -/
def admissibleRadius (d : ℕ) (L δ R κ : ℝ) : ℝ :=
  min (1 / (4 * productControlFactor d L δ))
    (1 / (4 * (d : ℝ) ^ 2 * (R * max 1 κ) ^ 2 * productControlFactor d L δ))

/-- When [the matrix dimension is positive](hyp:hd), [the shift scale is positive](hyp:hL),
and [the affine separation margin is positive](hyp:hδ), [the coordinate-product
amplification factor is strictly positive](goal). -/
theorem productControlFactor_pos {d : ℕ} {L δ : ℝ}
    (hd : 0 < d) (hL : 0 < L) (hδ : 0 < δ) :
    0 < productControlFactor d L δ := by
  unfold productControlFactor affineSolveFactor
  positivity

/-- When [the matrix dimension is positive](hyp:hd), [the shift scale is positive](hyp:hL),
[the affine separation margin is positive](hyp:hδ), and [the matrix scale is positive](hyp:hR),
[the declared small-residual radius is strictly positive](goal). -/
theorem admissibleRadius_pos {d : ℕ} {L δ R κ : ℝ}
    (hd : 0 < d) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R) :
    0 < admissibleRadius d L δ R κ := by
  have hq : 0 < productControlFactor d L δ :=
    productControlFactor_pos hd hL hδ
  unfold admissibleRadius
  have hmax : 0 < max 1 κ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

end Causalean.Discovery.LinearDisentanglement.Quantitative
