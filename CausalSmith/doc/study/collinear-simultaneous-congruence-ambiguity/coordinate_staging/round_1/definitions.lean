/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Quantitative.Definitions
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Two-coordinate deformations for collinear congruence families

This module defines the paper-independent objects used to deform a simultaneous
congruence representation along an affine-collinear pair of diagonal shifts.  The
deformation first mixes the two selected rows and then rescales them so that a
unit-diagonal normalization is retained.
-/

noncomputable section

open scoped Matrix

namespace Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity

open Causalean.Discovery.LinearDisentanglement.Quantitative

/-- A concrete certificate that the selected two-coordinate shift cloud is contained in
the affine line `u x + v y = c`, with a nonzero normal vector. -/
structure AffineLineCertificate {d : ℕ} {E : Type*} (s : E → Fin d → ℝ)
    (i j : Fin d) where
  /-- First component of the line's normal vector. -/
  u : ℝ
  /-- Second component of the line's normal vector. -/
  v : ℝ
  /-- Affine offset of the line. -/
  c : ℝ
  /-- The normal vector is nonzero. -/
  normal_ne : u ≠ 0 ∨ v ≠ 0
  /-- Every selected shift pair lies on the certified affine line. -/
  equation : ∀ e, u * s e i + v * s e j = c

/-- The elementary two-row shear has selected block `[[1, t v], [t u, 1]]` and is the
identity away from the selected off-diagonal entries. -/
def pairShear {d : ℕ} (i j : Fin d) (u v t : ℝ) : SqMatrix d :=
  1 + Matrix.single i j (t * v) + Matrix.single j i (t * u)

/-- The diagonal entry created in row `i` when the shear is applied to a unit-diagonal
matrix `B`. -/
def firstNormalizationDenom {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (v t : ℝ) : ℝ :=
  1 + t * v * B j i

/-- The diagonal entry created in row `j` when the shear is applied to a unit-diagonal
matrix `B`. -/
def secondNormalizationDenom {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u t : ℝ) : ℝ :=
  1 + t * u * B i j

/-- The diagonal row rescaling that restores the selected diagonal entries to one after
applying `pairShear`. -/
def pairRowNormalizer {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v t : ℝ) : SqMatrix d :=
  Matrix.diagonal fun k ↦
    if k = i then (firstNormalizationDenom B i j v t)⁻¹
    else if k = j then (secondNormalizationDenom B i j u t)⁻¹
    else 1

/-- The normalized two-coordinate change of latent coordinates is the row normalizer
followed by the elementary pair shear. -/
def normalizedPairDeformation {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v t : ℝ) : SqMatrix d :=
  pairRowNormalizer B i j u v t * pairShear i j u v t

/-- The deformed diagonalizer obtained by acting on the rows of the reference
diagonalizer. -/
def deformedDiagonalizer {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v t : ℝ) : SqMatrix d :=
  normalizedPairDeformation B i j u v t * B

/-- A normalized matrix is admissible at the selected two-cycle when the product of its
two opposite selected off-diagonal entries is not one. -/
def PairCycleAdmissible {d : ℕ} (B : SqMatrix d) (i j : Fin d) : Prop :=
  B i j * B j i ≠ 1

/-- The common selected off-diagonal term generated from a shift cloud on the line
`u x + v y = c`. -/
def commonShiftCrossTerm {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v c t : ℝ) : ℝ :=
  (firstNormalizationDenom B i j v t)⁻¹ *
    (secondNormalizationDenom B i j u t)⁻¹ * (t * c)

/-- The symmetric matrix supported on the two selected off-diagonal positions with the
given common entry. -/
def pairSymmetricOffDiagonal {d : ℕ} (i j : Fin d) (x : ℝ) : SqMatrix d :=
  Matrix.single i j x + Matrix.single j i x

/-- The invariant matrix after the coordinate deformation, including the common
off-diagonal shift term absorbed from every environment. -/
def deformedInvariant {d : ℕ} (B Ω : SqMatrix d) (i j : Fin d)
    (u v c t : ℝ) : SqMatrix d :=
  let T := normalizedPairDeformation B i j u v t
  T * Ω * T.transpose +
    pairSymmetricOffDiagonal i j (commonShiftCrossTerm B i j u v c t)

/-- The transformed shift is the diagonal of the congruence transform of the original
diagonal shift matrix. -/
def deformedShift {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v t : ℝ) (s : Fin d → ℝ) : Fin d → ℝ :=
  fun k ↦
    let T := normalizedPairDeformation B i j u v t
    (T * Matrix.diagonal s * T.transpose) k k

/-- The covariance matrix represented by a diagonalizer, an invariant matrix, and one
diagonal shift vector, using inverse congruence. -/
def representedCovariance {d : ℕ} (B Ω : SqMatrix d) (s : Fin d → ℝ) : SqMatrix d :=
  B⁻¹ * (Ω + Matrix.diagonal s) * (B⁻¹).transpose

/-- A finite covariance family is represented by the same normalized-congruence model in
every environment. -/
def RepresentsCovarianceFamily {d : ℕ} {E : Type*} (Sigma : E → SqMatrix d)
    (B Ω : SqMatrix d) (s : E → Fin d → ℝ) : Prop :=
  ∀ e, Sigma e = representedCovariance B Ω (s e)

end Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity
