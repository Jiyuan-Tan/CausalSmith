/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Quantitative simultaneous-congruence stability: definitions

This module gives paper-independent definitions for the residual of a finite family of
real congruence equations, quantitative affine separation of their prescribed diagonal
vectors, normalization and conditioning assumptions, and the explicit constants used by
the stability theorem.

The matrix norm in this API is the Euclidean (`ℓ²`) operator norm.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.Quantitative

/-- [A square matrix](goal) represents a latent change of coordinates in [dimension
`d`](hyp:d). -/
abbrev SqMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- [The congruence defect](goal) measures how far [candidate coordinates `B`](hyp:B) fail to turn
[observed matrix `A`](hyp:A) into [the prescribed diagonal `s`](hyp:s), in [dimension
`d`](hyp:d). -/
def congruenceDefect {d : ℕ} (A : SqMatrix d) (s : Fin d → ℝ) (B : SqMatrix d) :
    SqMatrix d :=
  B * A * B.transpose - Matrix.diagonal s

/-- [The simultaneous congruence residual](goal) is the worst transformation error across [a
nonempty finite environment collection](hyp:E), comparing [observed matrices](hyp:A) with
[prescribed diagonal shifts](hyp:s) under [candidate coordinates `B`](hyp:B) in [dimension
`d`](hyp:d). -/
def simultaneousCongruenceResidual {d : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B : SqMatrix d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun e => ‖congruenceDefect (A e) (s e) B‖

/-- [The worst-environment congruence residual cannot be negative](goal), for [observed
matrices](hyp:A), [prescribed shifts](hyp:s), and [candidate coordinates](hyp:B) over [environment
collection `E`](hyp:E) in [dimension `d`](hyp:d). -/
theorem simultaneousCongruenceResidual_nonneg {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E] (A : E → SqMatrix d) (s : E → Fin d → ℝ)
    (B : SqMatrix d) :
    0 ≤ simultaneousCongruenceResidual A s B := by
  classical
  let e : E := Classical.choice ‹Nonempty E›
  exact (norm_nonneg _).trans
    (Finset.le_sup' (fun e => ‖congruenceDefect (A e) (s e) B‖) (Finset.mem_univ e))

/-- [A simultaneous residual meets a tolerance exactly when every environment does](goal), for
[observed matrices](hyp:A), [prescribed shifts](hyp:s), [candidate coordinates](hyp:B), and
[tolerance `ε`](hyp:ε) over [environment collection `E`](hyp:E) in [dimension `d`](hyp:d). -/
theorem simultaneousCongruenceResidual_le_iff {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E] (A : E → SqMatrix d) (s : E → Fin d → ℝ)
    (B : SqMatrix d) (ε : ℝ) :
    simultaneousCongruenceResidual A s B ≤ ε ↔
      ∀ e, ‖congruenceDefect (A e) (s e) B‖ ≤ ε := by
  classical
  simp only [simultaneousCongruenceResidual, Finset.sup'_le_iff, Finset.mem_univ,
    forall_const]

/-- [Affine minor separation](goal) certifies that [environmental shift vectors](hyp:s) span enough
independent variation to solve all [dimension `d`](hyp:d) coordinates: within [finite environment
collection `E`](hyp:E), some shift-difference determinant is at least [margin `δ`](hyp:δ). -/
def AffineMinorSeparated {d : ℕ} {E : Type*} [Fintype E]
    (s : E → Fin d → ℝ) (δ : ℝ) : Prop :=
  ∃ (base : E) (pick : Fin d → E),
    δ ≤ |Matrix.det (fun i j => s (pick i) j - s base j)|

/-- [The shift-scale bound](goal) caps every coordinate of [all environmental shifts](hyp:s) by
[magnitude `L`](hyp:L), across [finite environment collection `E`](hyp:E) in [dimension
`d`](hyp:d). -/
def ShiftScaleBound {d : ℕ} {E : Type*} [Fintype E]
    (s : E → Fin d → ℝ) (L : ℝ) : Prop :=
  ∀ e i, |s e i| ≤ L

/-- [Unit-diagonal normalization](goal) fixes the otherwise free row scales of [matrix
`B`](hyp:B) in [dimension `d`](hyp:d). -/
def UnitDiagonal {d : ℕ} (B : SqMatrix d) : Prop :=
  ∀ i, B i i = 1

/-- [The Euclidean operator-norm condition number](goal) quantifies how strongly [matrix
`B`](hyp:B) can amplify perturbations in [dimension `d`](hyp:d). It is meaningful with a separate
nonsingularity condition because the library's inverse convention assigns zero to singular
matrices. -/
def operatorConditionNumber {d : ℕ} (B : SqMatrix d) : ℝ :=
  ‖B‖ * ‖B⁻¹‖

/-- [Bounded conditioning](goal) rules out unstable coordinate systems by requiring [matrix
`B`](hyp:B) in [dimension `d`](hyp:d) to be (1) [nonsingular](step:1) and (2) [no more ill
conditioned than](step:2) [envelope `κ`](hyp:κ). -/
def WellConditioned {d : ℕ} (κ : ℝ) (B : SqMatrix d) : Prop :=
  IsUnit B.det ∧ operatorConditionNumber B ≤ κ

/-- [The pair condition bound](goal) puts [reference and candidate coordinates](hyp:B₀,B) in the
same stable class for [dimension `d`](hyp:d): (1) [the reference is well conditioned](step:1) and
(2) [the candidate is well conditioned](step:2) under [envelope `κ`](hyp:κ). -/
def PairConditionBound {d : ℕ} (κ : ℝ) (B₀ B : SqMatrix d) : Prop :=
  WellConditioned κ B₀ ∧ WellConditioned κ B

/-- [The pair matrix-scale bound](goal) keeps [reference and candidate coordinates](hyp:B₀,B)
inside a common compact scale envelope in [dimension `d`](hyp:d) with [radius `R`](hyp:R): (1)
[the reference norm obeys the radius](step:1) and (2) [the candidate norm obeys it](step:2). -/
def PairMatrixScaleBound {d : ℕ} (R : ℝ) (B₀ B : SqMatrix d) : Prop :=
  ‖B₀‖ ≤ R ∧ ‖B‖ ≤ R

/-- [The transition matrix](goal) expresses [candidate coordinates relative to the reference
coordinates](hyp:B₀,B) in [dimension `d`](hyp:d), so identity is exact recovery. -/
def transition {d : ℕ} (B₀ B : SqMatrix d) : SqMatrix d :=
  B * B₀⁻¹

/-- [Exact congruence](goal) means [reference coordinates `B₀`](hyp:B₀) recover every [prescribed
diagonal shift](hyp:s) from [the observed matrix family](hyp:A), throughout [finite environment
collection `E`](hyp:E) in [dimension `d`](hyp:d). -/
def ExactCongruence {d : ℕ} {E : Type*} [Fintype E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B₀ : SqMatrix d) : Prop :=
  ∀ e, B₀ * A e * B₀.transpose = Matrix.diagonal (s e)

/-- [Approximate congruence](goal) accepts [candidate coordinates `B`](hyp:B) when their worst
error against [observed matrices](hyp:A) and [prescribed shifts](hyp:s) is at most [tolerance
`ε`](hyp:ε), across [environment collection `E`](hyp:E) in [dimension `d`](hyp:d). -/
def ApproximateCongruence {d : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B : SqMatrix d) (ε : ℝ) : Prop :=
  simultaneousCongruenceResidual A s B ≤ ε

/-- [The affine solve factor](goal) converts residual error into coordinate error; it worsens with
[dimension `d`](hyp:d) and [shift scale `L`](hyp:L), and improves with [affine-separation margin
`δ`](hyp:δ). -/
def affineSolveFactor (d : ℕ) (L δ : ℝ) : ℝ :=
  (d : ℝ) * (Nat.factorial (d - 1) : ℝ) * (2 * L) ^ (d - 1) / δ

/-- [The product-control factor](goal) is the two-sided amplification budget for controlling
transition products from [dimension `d`](hyp:d), [shift scale `L`](hyp:L), and [separation margin
`δ`](hyp:δ). -/
def productControlFactor (d : ℕ) (L δ : ℝ) : ℝ :=
  2 * affineSolveFactor d L δ

/-- [The stability constant](goal) turns congruence residuals into recovery error under [dimension
`d`](hyp:d), [shift scale `L`](hyp:L), [separation margin `δ`](hyp:δ), and [matrix scale
`R`](hyp:R). -/
def stabilityConstant (d : ℕ) (L δ R : ℝ) : ℝ :=
  2 * (d : ℝ) * R * productControlFactor d L δ

/-- [The admissible residual radius](goal) is the noise regime where local stability estimates
remain valid, determined by [dimension `d`](hyp:d), [shift scale `L`](hyp:L), [separation margin
`δ`](hyp:δ), and [matrix scale `R`](hyp:R). -/
def admissibleRadius (d : ℕ) (L δ R : ℝ) : ℝ :=
  min (1 / (4 * productControlFactor d L δ))
    (1 / (4 * (d : ℝ) ^ 2 * R ^ 2 * productControlFactor d L δ))

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
theorem admissibleRadius_pos {d : ℕ} {L δ R : ℝ}
    (hd : 0 < d) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R) :
    0 < admissibleRadius d L δ R := by
  have hq : 0 < productControlFactor d L δ :=
    productControlFactor_pos hd hL hδ
  unfold admissibleRadius
  positivity

end Causalean.Discovery.LinearDisentanglement.Quantitative
