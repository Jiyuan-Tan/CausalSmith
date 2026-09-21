/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity.Algebra

/-!
# Congruence preservation for collinear shift deformations

This module proves that the two-coordinate deformation splits every transformed diagonal
shift into a common off-diagonal invariant term and a new diagonal shift.  It then derives
exact preservation of the represented covariance family and the associated symmetry and
positive-definiteness facts.
-/

noncomputable section

open scoped Matrix

namespace Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity

open Causalean.Discovery.LinearDisentanglement.Quantitative

    · rw [deformedShift_apply_of_ne B hki hkj]
      exact hs k

private theorem diagonal_congruence_apply {d : ℕ} (T : SqMatrix d)
    (s : Fin d → ℝ) (a b : Fin d) :
    (T * Matrix.diagonal s * T.transpose) a b = ∑ l, T a l * s l * T b l := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Matrix.mul_diagonal]
  simp only [Matrix.transpose_apply]

private theorem normalizedPairDeformation_apply_first {d : ℕ} (B : SqMatrix d)
    {i j : Fin d} (hij : i ≠ j) (u v t : ℝ) (l : Fin d) :
    normalizedPairDeformation B i j u v t i l =
      (firstNormalizationDenom B i j v t)⁻¹ *
        ((if i = l then 1 else 0) + if j = l then t * v else 0) := by
  simp [normalizedPairDeformation_apply, hij, Ne.symm hij]

private theorem normalizedPairDeformation_apply_second {d : ℕ} (B : SqMatrix d)
    {i j : Fin d} (hij : i ≠ j) (u v t : ℝ) (l : Fin d) :
    normalizedPairDeformation B i j u v t j l =
      (secondNormalizationDenom B i j u t)⁻¹ *
        ((if j = l then 1 else 0) + if i = l then t * u else 0) := by
  simp [normalizedPairDeformation_apply, hij, Ne.symm hij]

private theorem normalizedPairDeformation_apply_unselected {d : ℕ} (B : SqMatrix d)
    {i j k : Fin d} (hki : k ≠ i) (hkj : k ≠ j) (u v t : ℝ) (l : Fin d) :
    normalizedPairDeformation B i j u v t k l = if k = l then 1 else 0 := by
  simp [normalizedPairDeformation_apply, hki, hkj, Ne.symm hki, Ne.symm hkj]

private theorem diagonal_congruence_apply_first_second {d : ℕ} {E : Type*}
    (B : SqMatrix d) {i j : Fin d} (hij : i ≠ j) (s : E → Fin d → ℝ)
    (cert : AffineLineCertificate s i j) (t : ℝ) (e : E) :
    (normalizedPairDeformation B i j cert.u cert.v t * Matrix.diagonal (s e) *
        (normalizedPairDeformation B i j cert.u cert.v t).transpose) i j =
      commonShiftCrossTerm B i j cert.u cert.v cert.c t := by
  rw [diagonal_congruence_apply]
  simp_rw [normalizedPairDeformation_apply_first B hij,
    normalizedPairDeformation_apply_second B hij]
  calc
    _ = ∑ l, ((if i = l then
          (firstNormalizationDenom B i j cert.v t)⁻¹ * s e l *
            (secondNormalizationDenom B i j cert.u t)⁻¹ * (t * cert.u) else 0) +
        (if j = l then
          (firstNormalizationDenom B i j cert.v t)⁻¹ * (t * cert.v) * s e l *
            (secondNormalizationDenom B i j cert.u t)⁻¹ else 0)) := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hil : i = l
      · by_cases hjl : j = l
        · exact (hij (hil.trans hjl.symm)).elim
        · subst l; simp [hij, Ne.symm hij] <;> ring
      · by_cases hjl : j = l
        · subst l; simp [hij, Ne.symm hij] <;> ring
        · simp [hil, hjl]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [commonShiftCrossTerm]
      rw [← cert.equation e]
      ring

private theorem diagonal_congruence_apply_second_first {d : ℕ} {E : Type*}
    (B : SqMatrix d) {i j : Fin d} (hij : i ≠ j) (s : E → Fin d → ℝ)
    (cert : AffineLineCertificate s i j) (t : ℝ) (e : E) :
    (normalizedPairDeformation B i j cert.u cert.v t * Matrix.diagonal (s e) *
        (normalizedPairDeformation B i j cert.u cert.v t).transpose) j i =
      commonShiftCrossTerm B i j cert.u cert.v cert.c t := by
  rw [diagonal_congruence_apply]
  calc
    _ = ∑ l, normalizedPairDeformation B i j cert.u cert.v t i l * s e l *
        normalizedPairDeformation B i j cert.u cert.v t j l := by
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := by
      rw [← diagonal_congruence_apply]
      exact diagonal_congruence_apply_first_second B hij s cert t e

private theorem diagonal_congruence_apply_unselected {d : ℕ} (B : SqMatrix d)
    {i j a b : Fin d} (hai : a ≠ i) (haj : a ≠ j) (hab : a ≠ b)
    (u v t : ℝ) (s : Fin d → ℝ) :
    (normalizedPairDeformation B i j u v t * Matrix.diagonal s *
        (normalizedPairDeformation B i j u v t).transpose) a b = 0 := by
  rw [diagonal_congruence_apply]
  simp_rw [normalizedPairDeformation_apply_unselected B hai haj]
  by_cases hbi : b = i
  · subst b
    simp [normalizedPairDeformation_apply, hai, Ne.symm hai, haj, Ne.symm haj]
  · by_cases hbj : b = j
    · subst b
      simp [normalizedPairDeformation_apply, hai, Ne.symm hai, haj, Ne.symm haj]
    · simp [normalizedPairDeformation_apply_unselected B hbi hbj, hab]

private theorem diagonal_congruence_symm_apply {d : ℕ} (T : SqMatrix d)
    (s : Fin d → ℝ) (a b : Fin d) :
    (T * Matrix.diagonal s * T.transpose) a b =
      (T * Matrix.diagonal s * T.transpose) b a := by
  rw [diagonal_congruence_apply, diagonal_congruence_apply]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- For a [matrix dimension and environment family](hyp:d,E), a [reference diagonalizer](hyp:B),
[two distinct selected coordinates](hyp:i,j,hij), [shift vectors](hyp:s) whose [selected pairs
obey a certified affine-line equation](hyp:cert), and [a deformation parameter and environment](hyp:t,e),
[the transformed shift matrix splits into its common symmetric off-diagonal term and its new
diagonal shift](goal). -/
theorem pairShear_diagonal_congruence_decomposition {d : ℕ} {E : Type*}
    (B : SqMatrix d) {i j : Fin d} (hij : i ≠ j) (s : E → Fin d → ℝ)
    (cert : AffineLineCertificate s i j) (t : ℝ) (e : E) :
    let T := normalizedPairDeformation B i j cert.u cert.v t
    T * Matrix.diagonal (s e) * T.transpose =
      pairSymmetricOffDiagonal i j
          (commonShiftCrossTerm B i j cert.u cert.v cert.c t) +
        Matrix.diagonal (deformedShift B i j cert.u cert.v t (s e)) := by
  classical
  dsimp
  ext a b
  by_cases hab : a = b
  · subst b
    have hia : ¬(i = a ∧ j = a) := by
      rintro ⟨rfl, h⟩
      exact hij h.symm
    have hja : ¬(j = a ∧ i = a) := by
      rintro ⟨rfl, h⟩
      exact hij h
    simp [pairSymmetricOffDiagonal, Matrix.single_apply, hia, hja, deformedShift]
  · by_cases hai : a = i
    · subst a
      by_cases hbj : b = j
      · subst b
        simpa [pairSymmetricOffDiagonal, hij, Ne.symm hij] using
          diagonal_congruence_apply_first_second B hij s cert t e
      · have hbi : b ≠ i := by intro h; exact hab h.symm
        have hz := diagonal_congruence_apply_unselected B hbi hbj (Ne.symm hab)
          cert.u cert.v t (s e)
        rw [diagonal_congruence_symm_apply]
        simpa [pairSymmetricOffDiagonal, Matrix.single_apply, hij, Ne.symm hij,
          hbi, Ne.symm hbi, hbj, Ne.symm hbj, hab, Ne.symm hab] using hz
    · by_cases haj : a = j
      · subst a
        by_cases hbi : b = i
        · subst b
          simpa [pairSymmetricOffDiagonal, hij, Ne.symm hij] using
            diagonal_congruence_apply_second_first B hij s cert t e
        · have hbj : b ≠ j := by intro h; exact hab h.symm
          have hz := diagonal_congruence_apply_unselected B hbi hbj (Ne.symm hab)
            cert.u cert.v t (s e)
          rw [diagonal_congruence_symm_apply]
          simpa [pairSymmetricOffDiagonal, Matrix.single_apply, hij, Ne.symm hij,
            hbi, Ne.symm hbi, hbj, Ne.symm hbj, hab, Ne.symm hab] using hz
      · by_cases hbi : b = i
        · subst b
          have hz := diagonal_congruence_apply_unselected B hai haj hab
            cert.u cert.v t (s e)
          simpa [pairSymmetricOffDiagonal, Matrix.single_apply, hij, Ne.symm hij,
            hai, Ne.symm hai, haj, Ne.symm haj, hab, Ne.symm hab] using hz
        · by_cases hbj : b = j
          · subst b
            have hz := diagonal_congruence_apply_unselected B hai haj hab
              cert.u cert.v t (s e)
            simpa [pairSymmetricOffDiagonal, Matrix.single_apply, hij, Ne.symm hij,
              hai, Ne.symm hai, haj, Ne.symm haj, hab, Ne.symm hab] using hz
          · have hz := diagonal_congruence_apply_unselected B hai haj hab
              cert.u cert.v t (s e)
            simpa [pairSymmetricOffDiagonal, Matrix.single_apply, hij, Ne.symm hij,
              hai, Ne.symm hai, haj, Ne.symm haj, hbi, Ne.symm hbi,
              hbj, Ne.symm hbj, hab, Ne.symm hab] using hz

/- In the decomposition proof, all unselected off-diagonal entries vanish.  The two
selected off-diagonal entries both equal the row-scale product times
`t * (cert.u * s e i + cert.v * s e j)`, which rewrites with `cert.equation e`. -/

/-- For a [matrix dimension and environment family](hyp:d,E), [reference diagonalizer and invariant](hyp:B,Ω), [two distinct selected coordinates](hyp:i,j,hij), [shift vectors](hyp:s) with [a certified affine-line relation](hyp:cert), and [a deformation parameter and environment](hyp:t,e), [the full transformed latent covariance splits into the deformed invariant plus transformed diagonal shift](goal). -/
theorem total_congruence_decomposition {d : ℕ} {E : Type*}
    (B Ω : SqMatrix d) {i j : Fin d} (hij : i ≠ j) (s : E → Fin d → ℝ)
    (cert : AffineLineCertificate s i j) (t : ℝ) (e : E) :
    let T := normalizedPairDeformation B i j cert.u cert.v t
    T * (Ω + Matrix.diagonal (s e)) * T.transpose =
      deformedInvariant B Ω i j cert.u cert.v cert.c t +
        Matrix.diagonal (deformedShift B i j cert.u cert.v t (s e)) := by
  dsimp
  rw [mul_add, add_mul]
  rw [pairShear_diagonal_congruence_decomposition B hij s cert t e]
  simp only [deformedInvariant]
  noncomm_ring

/-- For a [matrix dimension and environment family](hyp:d,E), a [reference diagonalizer and
invariant](hyp:B,Ω), [two distinct selected coordinates](hyp:i,j,hij), [shift vectors](hyp:s)
with [a certified affine-line relation](hyp:cert), a [deformation parameter and environment](hyp:t,e),
and [invertible reference and deformation matrices](hyp:hB,hT), [the deformed representation
gives exactly the original covariance matrix](goal). -/
theorem representedCovariance_deformation_eq {d : ℕ} {E : Type*}
    (B Ω : SqMatrix d) {i j : Fin d} (hij : i ≠ j) (s : E → Fin d → ℝ)
    (cert : AffineLineCertificate s i j) (t : ℝ) (e : E)
    (hB : IsUnit B.det)
    (hT : IsUnit (normalizedPairDeformation B i j cert.u cert.v t).det) :
    representedCovariance
        (deformedDiagonalizer B i j cert.u cert.v t)
        (deformedInvariant B Ω i j cert.u cert.v cert.c t)
        (deformedShift B i j cert.u cert.v t (s e)) =
      representedCovariance B Ω (s e) := by
  let T := normalizedPairDeformation B i j cert.u cert.v t
  have hTtr : IsUnit T.transpose.det := Matrix.isUnit_det_transpose T hT
  unfold representedCovariance deformedDiagonalizer
  change (T * B)⁻¹ *
      (deformedInvariant B Ω i j cert.u cert.v cert.c t +
        Matrix.diagonal (deformedShift B i j cert.u cert.v t (s e))) *
      ((T * B)⁻¹).transpose = _
  rw [← total_congruence_decomposition B Ω hij s cert t e]
  rw [Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  calc
    (B⁻¹ * T⁻¹) * (T * (Ω + Matrix.diagonal (s e)) * T.transpose) *
          ((T.transpose)⁻¹ * (B⁻¹).transpose) =
        B⁻¹ * (T⁻¹ * T) * (Ω + Matrix.diagonal (s e)) *
          (T.transpose * (T.transpose)⁻¹) * (B⁻¹).transpose := by
            noncomm_ring
    _ = B⁻¹ * (Ω + Matrix.diagonal (s e)) * (B⁻¹).transpose := by
      rw [Matrix.nonsing_inv_mul T hT, Matrix.mul_nonsing_inv T.transpose hTtr]
      simp

/-- For a [matrix dimension, diagonalizer, invariant matrix, and shift vector](hyp:d,B,Ω,s), if [the diagonalizer is invertible](hyp:hB), [the invariant is positive definite](hyp:hΩ), and [the shift is coordinatewise nonnegative](hyp:hs), [the represented covariance is positive definite](goal). -/
theorem representedCovariance_posDef {d : ℕ} (B Ω : SqMatrix d)
    (s : Fin d → ℝ) (hB : IsUnit B.det) (hΩ : Ω.PosDef)
    (hs : ∀ k, 0 ≤ s k) :
    (representedCovariance B Ω s).PosDef := by
  have hsum : (Ω + Matrix.diagonal s).PosDef :=
    hΩ.add_posSemidef (Matrix.PosSemidef.diagonal hs)
  have hBinv : IsUnit B⁻¹ :=
    (Matrix.isUnit_iff_isUnit_det B⁻¹).mpr (Matrix.isUnit_nonsing_inv_det B hB)
  have hinj : Function.Injective B⁻¹.vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr hBinv
  simpa [representedCovariance] using hsum.mul_mul_conjTranspose_same hinj

/-- For a [matrix dimension and reference and invariant matrices](hyp:d,B,Ω), [two distinct selected coordinates](hyp:i,j,hij), a [symmetric invariant](hyp:hΩ), and [line coefficients and parameter](hyp:u,v,c,t), [the deformed invariant is symmetric](goal). -/
theorem deformedInvariant_isSymm {d : ℕ} (B Ω : SqMatrix d) {i j : Fin d}
    (hij : i ≠ j) (hΩ : Ω.IsSymm) (u v c t : ℝ) :
    (deformedInvariant B Ω i j u v c t).IsSymm := by
  unfold deformedInvariant
  apply Matrix.IsSymm.add
  · simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hΩ, Matrix.mul_assoc]
  · simp [pairSymmetricOffDiagonal, Matrix.IsSymm, add_comm]

end Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity
