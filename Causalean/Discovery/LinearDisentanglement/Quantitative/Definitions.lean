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

/-- For [a nonnegative integer dimension](hyp:d), [a square matrix](goal) is a real-valued
matrix with that many rows and that many columns. -/
abbrev SqMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- For [a dimension](hyp:d), [an observed matrix](hyp:A), [a prescribed diagonal vector](hyp:s),
and [a candidate change-of-coordinates matrix](hyp:B), [the congruence defect](goal) is
$BAB^\mathsf{T}$ minus the diagonal matrix formed from the prescribed vector. -/
def congruenceDefect {d : ℕ} (A : SqMatrix d) (s : Fin d → ℝ) (B : SqMatrix d) :
    SqMatrix d :=
  B * A * B.transpose - Matrix.diagonal s

/-- For [a dimension](hyp:d), [a nonempty finite environment collection](hyp:E),
[an observed matrix for each environment](hyp:A), [a prescribed diagonal vector for each
environment](hyp:s), and [a candidate change-of-coordinates matrix](hyp:B), [the simultaneous
congruence residual](goal) is the largest Euclidean operator norm of the individual congruence
defects across environments. -/
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

/-- For [a dimension](hyp:d), [a finite environment collection](hyp:E), [a diagonal shift
vector for each environment](hyp:s), and [a real margin](hyp:δ), [affine minor separation](goal)
holds when there exist one base environment and one selected environment for each coordinate such
that the absolute determinant of their shift-difference matrix is at least the margin. -/
def AffineMinorSeparated {d : ℕ} {E : Type*} [Fintype E]
    (s : E → Fin d → ℝ) (δ : ℝ) : Prop :=
  ∃ (base : E) (pick : Fin d → E),
    δ ≤ |Matrix.det (fun i j => s (pick i) j - s base j)|

/-- For [a dimension](hyp:d), [a finite environment collection](hyp:E), [a diagonal shift
vector for each environment](hyp:s), and [a real bound](hyp:L), [the shift-scale bound](goal)
holds exactly when every coordinate of every prescribed diagonal shift has absolute value at most
the bound. -/
def ShiftScaleBound {d : ℕ} {E : Type*} [Fintype E]
    (s : E → Fin d → ℝ) (L : ℝ) : Prop :=
  ∀ e i, |s e i| ≤ L

/-- For [a dimension](hyp:d) and [a square matrix](hyp:B), [unit-diagonal normalization](goal)
holds exactly when every diagonal entry of the matrix equals one. -/
def UnitDiagonal {d : ℕ} (B : SqMatrix d) : Prop :=
  ∀ i, B i i = 1

/-- For [a dimension](hyp:d) and [a square matrix](hyp:B), [its Euclidean operator-norm
condition number](goal) is the product of its Euclidean operator norm and the Euclidean operator
norm of its inverse. -/
def operatorConditionNumber {d : ℕ} (B : SqMatrix d) : ℝ :=
  ‖B‖ * ‖B⁻¹‖

/-- For [a dimension](hyp:d), [a real condition bound](hyp:κ), and [a square matrix](hyp:B),
[bounded conditioning](goal) holds exactly when [the matrix is nonsingular](step:1) and [its
Euclidean operator-norm condition number is at most the bound](step:2). -/
def WellConditioned {d : ℕ} (κ : ℝ) (B : SqMatrix d) : Prop :=
  IsUnit B.det ∧ operatorConditionNumber B ≤ κ

/-- For [a dimension](hyp:d), [a real condition bound](hyp:κ), and [a reference and candidate
matrix](hyp:B₀,B), [the pair condition bound](goal) holds exactly when [the reference matrix is
boundedly conditioned by that bound](step:1) and [the candidate matrix is boundedly conditioned
by that bound](step:2). -/
def PairConditionBound {d : ℕ} (κ : ℝ) (B₀ B : SqMatrix d) : Prop :=
  WellConditioned κ B₀ ∧ WellConditioned κ B

/-- For [a dimension](hyp:d), [a real scale bound](hyp:R), and [a reference and candidate
matrix](hyp:B₀,B), [the pair matrix-scale bound](goal) holds exactly when [the reference matrix's
Euclidean operator norm is at most the scale bound](step:1) and [the candidate matrix's Euclidean
operator norm is at most the scale bound](step:2). -/
def PairMatrixScaleBound {d : ℕ} (R : ℝ) (B₀ B : SqMatrix d) : Prop :=
  ‖B₀‖ ≤ R ∧ ‖B‖ ≤ R

/-- For [a dimension](hyp:d) and [a reference and candidate matrix](hyp:B₀,B), [the transition
matrix](goal) is the candidate matrix multiplied by the inverse of the reference matrix. -/
def transition {d : ℕ} (B₀ B : SqMatrix d) : SqMatrix d :=
  B * B₀⁻¹

/-- For [a dimension](hyp:d), [a finite environment collection](hyp:E), [an observed matrix
for each environment](hyp:A), [a prescribed diagonal vector for each environment](hyp:s), and [a
reference matrix](hyp:B₀), [exact congruence](goal) holds exactly when, in every environment,
the reference matrix transforms the observed matrix into the diagonal matrix prescribed there. -/
def ExactCongruence {d : ℕ} {E : Type*} [Fintype E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B₀ : SqMatrix d) : Prop :=
  ∀ e, B₀ * A e * B₀.transpose = Matrix.diagonal (s e)

/-- For [a dimension](hyp:d), [a nonempty finite environment collection](hyp:E),
[an observed matrix for each environment](hyp:A), [a prescribed diagonal vector for each
environment](hyp:s), [a candidate matrix](hyp:B), and [a real tolerance](hyp:ε), [approximate
congruence](goal) holds exactly when the simultaneous congruence residual is at most the
tolerance. -/
def ApproximateCongruence {d : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B : SqMatrix d) (ε : ℝ) : Prop :=
  simultaneousCongruenceResidual A s B ≤ ε

/-- For [a dimension](hyp:d), [a shift scale](hyp:L), and [an affine-separation margin](hyp:δ),
[the affine solve factor](goal) is $d(d-1)!(2L)^{d-1}/\delta$. -/
def affineSolveFactor (d : ℕ) (L δ : ℝ) : ℝ :=
  (d : ℝ) * (Nat.factorial (d - 1) : ℝ) * (2 * L) ^ (d - 1) / δ

/-- For [a dimension](hyp:d), [a shift scale](hyp:L), and [an affine-separation margin](hyp:δ),
[the product-control factor](goal) is twice the affine solve factor. -/
def productControlFactor (d : ℕ) (L δ : ℝ) : ℝ :=
  2 * affineSolveFactor d L δ

/-- For [a dimension](hyp:d), [a shift scale](hyp:L), [an affine-separation margin](hyp:δ), [a
matrix scale](hyp:R), and [a condition-number envelope](hyp:κ), [the stability constant](goal)
is $2dR\max(1,\kappa)$ times the product-control factor. -/
def stabilityConstant (d : ℕ) (L δ R κ : ℝ) : ℝ :=
  2 * (d : ℝ) * R * max 1 κ * productControlFactor d L δ

/-- For [a dimension](hyp:d), [a shift scale](hyp:L), [an affine-separation margin](hyp:δ), [a
matrix scale](hyp:R), and [a condition-number envelope](hyp:κ), [the admissible residual
radius](goal) is the smaller of the two displayed reciprocal bounds determined by those
quantities. -/
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
