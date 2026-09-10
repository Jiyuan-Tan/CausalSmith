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

/-- For [a $d$-dimensional coordinate system](hyp:d), [two selected coordinates](hyp:i,j), and
[three real numbers specifying a line normal and deformation magnitude](hyp:u,v,t), [the
elementary two-row shear](goal) is the identity matrix except for selected off-diagonal entries
$tv$ and $tu$. -/
def pairShear {d : ℕ} (i j : Fin d) (u v t : ℝ) : SqMatrix d :=
  1 + Matrix.single i j (t * v) + Matrix.single j i (t * u)

/-- For [a $d\u2011by\u2011$d reference matrix](hyp:B), [two selected coordinates](hyp:i,j), and
[a shear coefficient and magnitude](hyp:v,t), [the first normalization denominator](goal) is
$1+t v B_{ji}$. -/
def firstNormalizationDenom {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (v t : ℝ) : ℝ :=
  1 + t * v * B j i

/-- For [a $d\u2011by\u2011$d reference matrix](hyp:B), [two selected coordinates](hyp:i,j), and
[a shear coefficient and magnitude](hyp:u,t), [the second normalization denominator](goal) is
$1+t u B_{ij}$. -/
def secondNormalizationDenom {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u t : ℝ) : ℝ :=
  1 + t * u * B i j

/-- For [a $d\u2011by\u2011$d reference matrix](hyp:B), [two selected coordinates](hyp:i,j), and
[a line normal and deformation magnitude](hyp:u,v,t), [the pair row normalizer](goal) is the
diagonal matrix that rescales the two selected rows by the reciprocals of their normalization
denominators and leaves all other rows unchanged. -/
def pairRowNormalizer {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v t : ℝ) : SqMatrix d :=
  Matrix.diagonal fun k ↦
    if k = i then (firstNormalizationDenom B i j v t)⁻¹
    else if k = j then (secondNormalizationDenom B i j u t)⁻¹
    else 1

/-- For [a $d\u2011by\u2011$d reference matrix](hyp:B), [two selected coordinates](hyp:i,j), and
[a line normal and deformation magnitude](hyp:u,v,t), [the normalized two-coordinate
deformation](goal) is the pair row normalizer multiplied by the elementary pair shear. -/
def normalizedPairDeformation {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v t : ℝ) : SqMatrix d :=
  pairRowNormalizer B i j u v t * pairShear i j u v t

/-- For [a $d\u2011by\u2011$d reference diagonalizer](hyp:B), [two selected coordinates](hyp:i,j),
and [a line normal and deformation magnitude](hyp:u,v,t), [the deformed diagonalizer](goal) is
the normalized two-coordinate deformation applied to the rows of the reference diagonalizer. -/
def deformedDiagonalizer {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v t : ℝ) : SqMatrix d :=
  normalizedPairDeformation B i j u v t * B

/-- For [a $d\u2011by\u2011$d matrix](hyp:B) and [two selected coordinates](hyp:i,j), [pair-cycle
admissibility](goal) holds exactly when the product of the two opposite selected off-diagonal
entries is not one. -/
def PairCycleAdmissible {d : ℕ} (B : SqMatrix d) (i j : Fin d) : Prop :=
  B i j * B j i ≠ 1

/-- For [a $d\u2011by\u2011$d reference matrix](hyp:B), [two selected coordinates](hyp:i,j), and
[a line normal, offset, and deformation magnitude](hyp:u,v,c,t), [the common shift cross
term](goal) is the line offset times the deformation magnitude, divided by both selected
normalization denominators. -/
def commonShiftCrossTerm {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v c t : ℝ) : ℝ :=
  (firstNormalizationDenom B i j v t)⁻¹ *
    (secondNormalizationDenom B i j u t)⁻¹ * (t * c)

/-- For [a $d$-dimensional coordinate system](hyp:d), [two selected coordinates](hyp:i,j), and
[a real entry value](hyp:x), [the symmetric selected off-diagonal matrix](goal) has that value
in both selected off-diagonal positions and zero elsewhere. -/
def pairSymmetricOffDiagonal {d : ℕ} (i j : Fin d) (x : ℝ) : SqMatrix d :=
  Matrix.single i j x + Matrix.single j i x

/-- For [a $d\u2011by\u2011$d reference diagonalizer and invariant matrix](hyp:B,Ω), [two selected
coordinates](hyp:i,j), and [a line normal, offset, and deformation magnitude](hyp:u,v,c,t),
[the deformed invariant matrix](goal) is obtained by [first forming the normalized
two-coordinate deformation](step:1), then taking its congruence transform of the invariant matrix
and adding the symmetric common shift cross term. -/
def deformedInvariant {d : ℕ} (B Ω : SqMatrix d) (i j : Fin d)
    (u v c t : ℝ) : SqMatrix d :=
  let T := normalizedPairDeformation B i j u v t
  T * Ω * T.transpose +
    pairSymmetricOffDiagonal i j (commonShiftCrossTerm B i j u v c t)

/-- For [a $d\u2011by\u2011$d reference diagonalizer](hyp:B), [two selected coordinates](hyp:i,j),
[a line normal and deformation magnitude](hyp:u,v,t), [an original diagonal shift vector](hyp:s),
and a coordinate, [the deformed shift at that coordinate](goal) is the corresponding
diagonal entry obtained after [forming the normalized two-coordinate deformation](step:1) and
taking the congruence transform of the original diagonal shift matrix. -/
def deformedShift {d : ℕ} (B : SqMatrix d) (i j : Fin d)
    (u v t : ℝ) (s : Fin d → ℝ) : Fin d → ℝ :=
  fun k ↦
    let T := normalizedPairDeformation B i j u v t
    (T * Matrix.diagonal s * T.transpose) k k

/-- For [a $d\u2011by\u2011$d diagonalizer and invariant matrix](hyp:B,Ω) and [a diagonal shift
vector](hyp:s), [the represented covariance matrix](goal) is the inverse congruence transform
of the invariant matrix plus the diagonal shift matrix. -/
def representedCovariance {d : ℕ} (B Ω : SqMatrix d) (s : Fin d → ℝ) : SqMatrix d :=
  B⁻¹ * (Ω + Matrix.diagonal s) * (B⁻¹).transpose

/-- For [a dimension](hyp:d), [an environment collection](hyp:E), [a covariance matrix for
each environment](hyp:Sigma), [a diagonalizer and invariant matrix](hyp:B,Ω), and [a diagonal
shift vector for each environment](hyp:s), [the covariance family is represented](goal) exactly
when every environment's covariance matrix equals the covariance represented by those common
matrices and that environment's shift vector. -/
def RepresentsCovarianceFamily {d : ℕ} {E : Type*} (Sigma : E → SqMatrix d)
    (B Ω : SqMatrix d) (s : E → Fin d → ℝ) : Prop :=
  ∀ e, Sigma e = representedCovariance B Ω (s e)

end Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity
