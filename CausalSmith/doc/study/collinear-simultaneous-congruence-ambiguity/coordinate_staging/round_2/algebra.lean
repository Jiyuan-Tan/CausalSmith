/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity.Definitions
import Mathlib.Algebra.Order.Star.Real

/-!
# Algebra of the normalized two-coordinate deformation

This module records the entry formulas, invertibility and normalization facts, cycle
product identity, shift nonnegativity, and exact congruence decomposition for the
two-coordinate construction.
-/

noncomputable section

open scoped Matrix

namespace Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity

open Causalean.Discovery.LinearDisentanglement.Quantitative

private theorem elementaryShear_isUnit_det {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    (a : ℝ) : IsUnit ((1 + Matrix.single i j a : SqMatrix d).det) := by
  apply Matrix.isUnit_det_of_right_inverse
    (B := (1 + Matrix.single i j (-a) : SqMatrix d))
  classical
  simp [mul_add, add_mul, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    ← Matrix.single_neg]

private theorem diagonalReplace_isUnit_det {d : ℕ} (j : Fin d) {a : ℝ}
    (ha : a ≠ 0) :
    IsUnit (Matrix.diagonal (fun k : Fin d ↦ if k = j then a else 1)).det := by
  rw [Matrix.det_diagonal]
  rw [IsUnit.prod_iff]
  intro k hk
  exact by
    split_ifs with h
    · exact ha.isUnit
    · exact isUnit_one

private theorem pairShear_factorization {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    (u v t : ℝ) :
    pairShear i j u v t =
      (1 + Matrix.single j i (t * u)) *
        Matrix.diagonal (fun k : Fin d ↦ if k = j then 1 - t ^ 2 * u * v else 1) *
          (1 + Matrix.single i j (t * v)) := by
  classical
  have hd :
      Matrix.diagonal (fun k : Fin d ↦ if k = j then 1 - t ^ 2 * u * v else 1) =
        1 + Matrix.single j j (-t ^ 2 * u * v) := by
    ext k l
    by_cases hkl : k = l
    · subst l
      by_cases hkj : k = j
      · subst k
        simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.single_apply]
        ring
      · simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.single_apply,
          hkj, Ne.symm hkj]
    · have hn : ¬(j = k ∧ j = l) := by
        rintro ⟨rfl, rfl⟩
        exact hkl rfl
      simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.single_apply, hkl, hn]
  rw [hd]
  simp [pairShear, mul_add, add_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ hij,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    Matrix.single_mul_single_same]
  ext k l
  simp [Matrix.single_apply]
  split_ifs <;> ring

/- Proof guide: entrywise identities in this file should be proved by `classical`, matrix
extensionality, and `simp [Matrix.mul_apply, pairShear, pairRowNormalizer, ...]`, splitting
the finitely many equality cases involving `i` and `j`.  Keep those calculations local so
the public API remains independent of the chosen representation by `Matrix.single`. -/

/-- [At zero deformation parameter, the normalized pair deformation is the identity
matrix](goal). -/
@[simp] theorem normalizedPairDeformation_zero {d : ℕ} (B : SqMatrix d)
    (i j : Fin d) (u v : ℝ) :
    normalizedPairDeformation B i j u v 0 = 1 := by
  classical
  have hR : pairRowNormalizer B i j u v 0 = 1 := by
    ext k l
    simp [pairRowNormalizer, firstNormalizationDenom, secondNormalizationDenom]
  have hS : pairShear i j u v 0 = 1 := by
    ext k l
    simp [pairShear]
  simp [normalizedPairDeformation, hR, hS]

/-- [At zero deformation parameter, the deformed diagonalizer equals the reference
diagonalizer](goal). -/
@[simp] theorem deformedDiagonalizer_zero {d : ℕ} (B : SqMatrix d)
    (i j : Fin d) (u v : ℝ) :
    deformedDiagonalizer B i j u v 0 = B := by
  simp [deformedDiagonalizer]

/-- [At zero deformation parameter, the transformed invariant is the original invariant
matrix](goal). -/
@[simp] theorem deformedInvariant_zero {d : ℕ} (B Ω : SqMatrix d)
    (i j : Fin d) (u v c : ℝ) :
    deformedInvariant B Ω i j u v c 0 = Ω := by
  simp [deformedInvariant, commonShiftCrossTerm, pairSymmetricOffDiagonal]

/-- [At zero deformation parameter, the transformed diagonal shift is the original
shift](goal). -/
@[simp] theorem deformedShift_zero {d : ℕ} (B : SqMatrix d)
    (i j : Fin d) (u v : ℝ) (s : Fin d → ℝ) :
    deformedShift B i j u v 0 s = s := by
  funext k
  simp [deformedShift]

/-- When [the selected coordinates are distinct](hyp:hij) and [the selected shear-block
determinant is nonzero](hyp:hdet), [the elementary pair shear is invertible](goal). -/
theorem pairShear_isUnit_det {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {u v t : ℝ} (hdet : 1 - t ^ 2 * u * v ≠ 0) :
    IsUnit (pairShear i j u v t).det := by
  rw [pairShear_factorization hij, Matrix.det_mul, Matrix.det_mul]
  exact IsUnit.mul
    (IsUnit.mul (elementaryShear_isUnit_det hij.symm (t * u))
      (diagonalReplace_isUnit_det j hdet))
    (elementaryShear_isUnit_det hij (t * v))

/- For the invertibility chain, either exhibit the inverse of the selected 2×2 block or
prove injectivity of `mulVec`; then use Mathlib's matrix-is-unit/determinant bridges. -/

/-- When [the selected coordinates are distinct](hyp:hij) and [both row-normalization
denominators are nonzero](hyp:hfirst,hsecond), [the diagonal row normalizer is
invertible](goal). -/
theorem pairRowNormalizer_isUnit_det {d : ℕ} (B : SqMatrix d) {i j : Fin d}
    (hij : i ≠ j) {u v t : ℝ}
    (hfirst : firstNormalizationDenom B i j v t ≠ 0)
    (hsecond : secondNormalizationDenom B i j u t ≠ 0) :
    IsUnit (pairRowNormalizer B i j u v t).det := by
  rw [pairRowNormalizer, Matrix.det_diagonal, IsUnit.prod_iff]
  intro k hk
  split_ifs with hki hkj
  · exact (inv_ne_zero hfirst).isUnit
  · exact (inv_ne_zero hsecond).isUnit
  · exact isUnit_one

/-- When [the selected coordinates are distinct](hyp:hij), [both normalization
denominators are nonzero](hyp:hfirst,hsecond), and [the shear determinant is
nonzero](hyp:hdet), [the normalized pair deformation is invertible](goal). -/
theorem normalizedPairDeformation_isUnit_det {d : ℕ} (B : SqMatrix d)
    {i j : Fin d} (hij : i ≠ j) {u v t : ℝ}
    (hfirst : firstNormalizationDenom B i j v t ≠ 0)
    (hsecond : secondNormalizationDenom B i j u t ≠ 0)
    (hdet : 1 - t ^ 2 * u * v ≠ 0) :
    IsUnit (normalizedPairDeformation B i j u v t).det := by
  rw [normalizedPairDeformation, Matrix.det_mul]
  exact IsUnit.mul
    (pairRowNormalizer_isUnit_det B hij hfirst hsecond)
    (pairShear_isUnit_det hij hdet)

private theorem normalizedPairDeformation_apply {d : ℕ} (B : SqMatrix d)
    (i j k l : Fin d) (u v t : ℝ) :
    normalizedPairDeformation B i j u v t k l =
      (if k = i then (firstNormalizationDenom B i j v t)⁻¹
       else if k = j then (secondNormalizationDenom B i j u t)⁻¹ else 1) *
        ((if k = l then 1 else 0) +
          (if i = k ∧ j = l then t * v else 0) +
          (if j = k ∧ i = l then t * u else 0)) := by
  classical
  change
    (Matrix.diagonal (fun k : Fin d ↦
      if k = i then (firstNormalizationDenom B i j v t)⁻¹
      else if k = j then (secondNormalizationDenom B i j u t)⁻¹ else 1) *
        pairShear i j u v t) k l = _
  rw [Matrix.diagonal_mul]
  simp [pairShear, Matrix.single_apply, Matrix.one_apply]

private theorem deformedDiagonalizer_apply_first {d : ℕ} (B : SqMatrix d)
    {i j : Fin d} (hij : i ≠ j) (u v t : ℝ) (l : Fin d) :
    deformedDiagonalizer B i j u v t i l =
      (firstNormalizationDenom B i j v t)⁻¹ * (B i l + t * v * B j l) := by
  classical
  simp only [deformedDiagonalizer, Matrix.mul_apply, normalizedPairDeformation_apply]
  calc
    _ = ∑ x, ((if i = x then
          (firstNormalizationDenom B i j v t)⁻¹ * B x l else 0) +
        (if j = x then
          (firstNormalizationDenom B i j v t)⁻¹ * (t * v) * B x l else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hix : i = x
      · by_cases hjx : j = x
        · exact (hij (hix.trans hjx.symm)).elim
        · simp [hix, hjx, hij, Ne.symm hij] <;> ring
      · by_cases hjx : j = x
        · simp [hix, Ne.symm hix, hjx, hij, Ne.symm hij] <;> ring
        · simp [hix, Ne.symm hix, hjx, hij, Ne.symm hij]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp
      ring

private theorem deformedDiagonalizer_apply_second {d : ℕ} (B : SqMatrix d)
    {i j : Fin d} (hij : i ≠ j) (u v t : ℝ) (l : Fin d) :
    deformedDiagonalizer B i j u v t j l =
      (secondNormalizationDenom B i j u t)⁻¹ * (t * u * B i l + B j l) := by
  classical
  simp only [deformedDiagonalizer, Matrix.mul_apply, normalizedPairDeformation_apply]
  calc
    _ = ∑ x, ((if j = x then
          (secondNormalizationDenom B i j u t)⁻¹ * B x l else 0) +
        (if i = x then
          (secondNormalizationDenom B i j u t)⁻¹ * (t * u) * B x l else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hix : i = x
      · by_cases hjx : j = x
        · exact (hij (hix.trans hjx.symm)).elim
        · simp [hix, hjx, hij, Ne.symm hij] <;> ring
      · by_cases hjx : j = x
        · simp [hix, Ne.symm hix, hjx, hij, Ne.symm hij] <;> ring
        · simp [hix, Ne.symm hix, hjx, hij, Ne.symm hij]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp
      ring

private theorem deformedDiagonalizer_apply_of_ne {d : ℕ} (B : SqMatrix d)
    {i j k : Fin d} (hki : k ≠ i) (hkj : k ≠ j) (u v t : ℝ) (l : Fin d) :
    deformedDiagonalizer B i j u v t k l = B k l := by
  classical
  simp [deformedDiagonalizer, Matrix.mul_apply, normalizedPairDeformation_apply,
    hki, hkj, Ne.symm hki, Ne.symm hkj]

/-- When [the selected coordinates are distinct](hyp:hij), [the reference diagonal is
unit-normalized](hyp:hB), and [both normalization denominators are
nonzero](hyp:hfirst,hsecond), [row normalization restores unit diagonal](goal). -/
theorem deformedDiagonalizer_unitDiagonal {d : ℕ} (B : SqMatrix d)
    {i j : Fin d} (hij : i ≠ j) (hB : UnitDiagonal B) {u v t : ℝ}
    (hfirst : firstNormalizationDenom B i j v t ≠ 0)
    (hsecond : secondNormalizationDenom B i j u t ≠ 0) :
    UnitDiagonal (deformedDiagonalizer B i j u v t) := by
  intro k
  by_cases hki : k = i
  · subst k
    rw [deformedDiagonalizer_apply_first B hij, hB]
    change (firstNormalizationDenom B i j v t)⁻¹ *
      firstNormalizationDenom B i j v t = 1
    exact inv_mul_cancel₀ hfirst
  · by_cases hkj : k = j
    · subst k
      rw [deformedDiagonalizer_apply_second B hij, hB]
      rw [show t * u * B i j + 1 = secondNormalizationDenom B i j u t by
        unfold secondNormalizationDenom
        ring]
      exact inv_mul_cancel₀ hsecond
    · rw [deformedDiagonalizer_apply_of_ne B hki hkj]
      exact hB k

/-- When [the selected coordinates are distinct](hyp:hij), [the reference diagonal is
unit-normalized](hyp:hB), and [both normalization denominators are
nonzero](hyp:hfirst,hsecond), [the selected cycle-product defect obeys the stated shear
identity](goal). -/
theorem deformedDiagonalizer_cycle_identity {d : ℕ} (B : SqMatrix d)
    {i j : Fin d} (hij : i ≠ j) (hB : UnitDiagonal B) {u v t : ℝ}
    (hfirst : firstNormalizationDenom B i j v t ≠ 0)
    (hsecond : secondNormalizationDenom B i j u t ≠ 0) :
    firstNormalizationDenom B i j v t * secondNormalizationDenom B i j u t *
        (deformedDiagonalizer B i j u v t i j *
            deformedDiagonalizer B i j u v t j i - 1) =
      (B i j * B j i - 1) * (1 - t ^ 2 * u * v) := by
  rw [deformedDiagonalizer_apply_first B hij,
    deformedDiagonalizer_apply_second B hij, hB, hB]
  unfold firstNormalizationDenom secondNormalizationDenom at *
  field_simp [hfirst, hsecond]
  ring

/- The cycle identity reduces, after the two selected-entry formulas and cancellation of
the nonzero denominators, to
`(p + tv)(q + tu) - (1 + tvq)(1 + tup) = (pq - 1)(1 - t²uv)`. -/

/-- When [the selected coordinates are distinct](hyp:hij), [the reference diagonal is
unit-normalized](hyp:hB), [its selected two-cycle is admissible](hyp:hcycle), [both
normalization denominators are nonzero](hyp:hfirst,hsecond), and [the shear determinant
is nonzero](hyp:hdet), [the deformed selected two-cycle remains admissible](goal). -/
theorem deformedDiagonalizer_pairCycleAdmissible {d : ℕ} (B : SqMatrix d)
    {i j : Fin d} (hij : i ≠ j) (hB : UnitDiagonal B)
    (hcycle : PairCycleAdmissible B i j) {u v t : ℝ}
    (hfirst : firstNormalizationDenom B i j v t ≠ 0)
    (hsecond : secondNormalizationDenom B i j u t ≠ 0)
    (hdet : 1 - t ^ 2 * u * v ≠ 0) :
    PairCycleAdmissible (deformedDiagonalizer B i j u v t) i j := by
  intro hbad
  have h := deformedDiagonalizer_cycle_identity B hij hB hfirst hsecond
  rw [hbad, sub_self, mul_zero] at h
  have hright : (B i j * B j i - 1) * (1 - t ^ 2 * u * v) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hcycle) hdet
  exact hright h.symm

/-- When [the selected coordinates are distinct](hyp:hij), [the reference diagonalizer
is invertible](hyp:hBunit), [the line normal is nonzero](hyp:hnormal), [the deformation
parameter is nonzero](hyp:ht), and [both normalization denominators are
nonzero](hyp:hfirst,hsecond), [the deformed diagonalizer differs from the reference](goal). -/
theorem deformedDiagonalizer_ne {d : ℕ} (B : SqMatrix d) {i j : Fin d}
    (hij : i ≠ j) (hBunit : IsUnit B.det) {u v t : ℝ}
    (hnormal : u ≠ 0 ∨ v ≠ 0) (ht : t ≠ 0)
    (hfirst : firstNormalizationDenom B i j v t ≠ 0)
    (hsecond : secondNormalizationDenom B i j u t ≠ 0) :
    deformedDiagonalizer B i j u v t ≠ B := by
  intro heq
  have hmul : normalizedPairDeformation B i j u v t * B = B := heq
  have hT : normalizedPairDeformation B i j u v t = 1 := by
    calc
      normalizedPairDeformation B i j u v t =
          normalizedPairDeformation B i j u v t * (B * B⁻¹) := by
            rw [Matrix.mul_nonsing_inv B hBunit, Matrix.mul_one]
      _ = (normalizedPairDeformation B i j u v t * B) * B⁻¹ := by
            rw [Matrix.mul_assoc]
      _ = B * B⁻¹ := by rw [hmul]
      _ = 1 := Matrix.mul_nonsing_inv B hBunit
  rcases hnormal with hu | hv
  · have hentry := congrArg (fun M : SqMatrix d ↦ M j i) hT
    simp [normalizedPairDeformation_apply, hij, Ne.symm hij] at hentry
    rcases hentry with h | h | h
    · exact hsecond h
    · exact ht h
    · exact hu h
  · have hentry := congrArg (fun M : SqMatrix d ↦ M i j) hT
    simp [normalizedPairDeformation_apply, hij, Ne.symm hij] at hentry
    rcases hentry with h | h | h
    · exact hfirst h
    · exact ht h
    · exact hv h

private theorem deformedShift_sum_squares {d : ℕ} (B : SqMatrix d)
    (i j : Fin d) (u v t : ℝ) (s : Fin d → ℝ) (k : Fin d) :
    deformedShift B i j u v t s k =
      ∑ l, (normalizedPairDeformation B i j u v t k l) ^ 2 * s l := by
  classical
  let T := normalizedPairDeformation B i j u v t
  change (T * Matrix.diagonal s * T.transpose) k k = ∑ l, T k l ^ 2 * s l
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Matrix.mul_diagonal]
  simp only [Matrix.transpose_apply, pow_two]
  ring

/-- When [the selected coordinates are distinct](hyp:hij), [the first transformed shift
is its stated nonnegative weighted sum](goal). -/
theorem deformedShift_apply_first {d : ℕ} (B : SqMatrix d) {i j : Fin d}
    (hij : i ≠ j) (u v t : ℝ) (s : Fin d → ℝ) :
    deformedShift B i j u v t s i =
      (firstNormalizationDenom B i j v t)⁻¹ ^ 2 *
        (s i + t ^ 2 * v ^ 2 * s j) := by
  classical
  rw [deformedShift_sum_squares]
  simp only [normalizedPairDeformation_apply]
  simp only [if_pos, Ne.symm hij, false_and, if_false, true_and]
  calc
    _ = ∑ l, ((if i = l then
          (firstNormalizationDenom B i j v t)⁻¹ ^ 2 * s l else 0) +
        (if j = l then
          (firstNormalizationDenom B i j v t)⁻¹ ^ 2 *
            (t ^ 2 * v ^ 2) * s l else 0)) := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hil : i = l
      · by_cases hjl : j = l
        · exact (hij (hil.trans hjl.symm)).elim
        · subst l
          simp [hij, Ne.symm hij] <;> try ring <;> simp_all
      · by_cases hjl : j = l
        · subst l
          simp [hij, Ne.symm hij] <;> try ring <;> simp_all
        · simp [hil, Ne.symm hil, hjl, Ne.symm hjl] <;> try ring <;> simp_all
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp
      ring

/-- When [the selected coordinates are distinct](hyp:hij), [the second transformed shift
is its stated nonnegative weighted sum](goal). -/
theorem deformedShift_apply_second {d : ℕ} (B : SqMatrix d) {i j : Fin d}
    (hij : i ≠ j) (u v t : ℝ) (s : Fin d → ℝ) :
    deformedShift B i j u v t s j =
      (secondNormalizationDenom B i j u t)⁻¹ ^ 2 *
        (t ^ 2 * u ^ 2 * s i + s j) := by
  classical
  rw [deformedShift_sum_squares]
  simp only [normalizedPairDeformation_apply]
  simp only [if_neg (Ne.symm hij), if_pos, hij, false_and, if_false, true_and]
  calc
    _ = ∑ l, ((if i = l then
          (secondNormalizationDenom B i j u t)⁻¹ ^ 2 *
            (t ^ 2 * u ^ 2) * s l else 0) +
        (if j = l then
          (secondNormalizationDenom B i j u t)⁻¹ ^ 2 * s l else 0)) := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hil : i = l
      · by_cases hjl : j = l
        · exact (hij (hil.trans hjl.symm)).elim
        · subst l
          simp [hij, Ne.symm hij] <;> try ring <;> simp_all
      · by_cases hjl : j = l
        · subst l
          simp [hij, Ne.symm hij] <;> try ring <;> simp_all
        · simp [hil, Ne.symm hil, hjl, Ne.symm hjl] <;> try ring <;> simp_all
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp
      ring

/-- When [the coordinate is neither selected coordinate](hyp:hki,hkj), [its transformed
shift is unchanged](goal). -/
theorem deformedShift_apply_of_ne {d : ℕ} (B : SqMatrix d) {i j k : Fin d}
    (hki : k ≠ i) (hkj : k ≠ j) (u v t : ℝ) (s : Fin d → ℝ) :
    deformedShift B i j u v t s k = s k := by
  classical
  rw [deformedShift_sum_squares]
  simp [normalizedPairDeformation_apply, hki, hkj, Ne.symm hki, Ne.symm hkj]

/-- When [the selected coordinates are distinct](hyp:hij) and [the original shift is
coordinatewise nonnegative](hyp:hs), [the transformed shift is coordinatewise
nonnegative](goal). -/
theorem deformedShift_nonnegative {d : ℕ} (B : SqMatrix d) {i j : Fin d}
    (hij : i ≠ j) (u v t : ℝ) (s : Fin d → ℝ)
    (hs : ∀ k, 0 ≤ s k) :
    ∀ k, 0 ≤ deformedShift B i j u v t s k := by
  intro k
  by_cases hki : k = i
  · subst k
    rw [deformedShift_apply_first B hij]
    exact mul_nonneg (sq_nonneg _)
      (add_nonneg (hs i) (mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg v)) (hs j)))
  · by_cases hkj : k = j
    · subst k
      rw [deformedShift_apply_second B hij]
      exact mul_nonneg (sq_nonneg _)
        (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg u)) (hs i)) (hs j))
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

/-- When [the selected coordinates are distinct](hyp:hij), [the transformed diagonal
shift matrix splits into the common symmetric off-diagonal term and its new diagonal
shift](goal). -/
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

/-- When [the selected coordinates are distinct](hyp:hij), [the latent congruence is
exactly the deformed invariant plus the transformed diagonal shift](goal). -/
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

/-- With [two distinct selected coordinates](hyp:hij), [an invertible reference
diagonalizer](hyp:hB), and [an invertible normalized deformation](hyp:hT), [the transformed
representation gives exactly the same covariance matrix in each environment](goal). -/
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

/-- Given [an invertible diagonalizer](hyp:hB), [a positive-definite invariant](hyp:hΩ),
and [a coordinatewise nonnegative shift](hyp:hs), [the represented covariance matrix is
positive definite](goal). -/
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

/-- When [the selected coordinates are distinct](hyp:hij) and [the original invariant
is symmetric](hyp:hΩ), [the deformed invariant is symmetric](goal). -/
theorem deformedInvariant_isSymm {d : ℕ} (B Ω : SqMatrix d) {i j : Fin d}
    (hij : i ≠ j) (hΩ : Ω.IsSymm) (u v c t : ℝ) :
    (deformedInvariant B Ω i j u v c t).IsSymm := by
  unfold deformedInvariant
  apply Matrix.IsSymm.add
  · simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hΩ, Matrix.mul_assoc]
  · simp [pairSymmetricOffDiagonal, Matrix.IsSymm, add_comm]

end Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity
