/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine.Definitions

/-!
# Pairwise affine coordinate control

This module expands a congruence around the identity transition, bounds its quadratic
coordinate-product remainder, solves the two-coordinate affine system furnished by one
pair's selected environment triple, and controls diagonal transition entries using
unit-diagonal normalization.
-/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine

open Causalean.Discovery.LinearDisentanglement.Quantitative

/-- For [a real square matrix](hyp:R), [two rows](hyp:i,j), and [two environments](hyp:e₁,e₀), if [the shifts have scale at most `M`](hyp:hscale) and
[`M` is nonnegative](hyp:hM), then [the weighted coordinate-product remainder is bounded
by `2 M` times the squared entrywise L² size](goal). -/
-- Proof route: `|s₁ k-s₀ k| ≤ 2M`, then Cauchy--Schwarz on the two rows and the
-- fact that each row's squared sum is bounded by the full entrywise squared sum.
theorem coordinateProductRemainder_le {p : ℕ} {E : Type*} [Fintype E]
    (s : E → Fin p → ℝ) (R : SqMatrix p) {M : ℝ}
    (hM : 0 ≤ M) (hscale : ShiftScaleBound s M)
    (e₁ e₀ : E) (i j : Fin p) :
    |∑ k, R i k * R j k * (s e₁ k - s e₀ k)| ≤
      2 * M * entryL2 R ^ 2 := by
  classical
  have hshift (k : Fin p) : |s e₁ k - s e₀ k| ≤ 2 * M := by
    calc
      |s e₁ k - s e₀ k| ≤ |s e₁ k| + |s e₀ k| := abs_sub _ _
      _ ≤ M + M := add_le_add (hscale _ _) (hscale _ _)
      _ = 2 * M := by ring
  have hterm (k : Fin p) :
      |R i k * R j k * (s e₁ k - s e₀ k)| ≤
        M * (|R i k| ^ 2 + |R j k| ^ 2) := by
    have huv : 2 * (|R i k| * |R j k|) ≤ |R i k| ^ 2 + |R j k| ^ 2 := by
      nlinarith [sq_nonneg (|R i k| - |R j k|)]
    calc
      |R i k * R j k * (s e₁ k - s e₀ k)| =
          (|R i k| * |R j k|) * |s e₁ k - s e₀ k| := by
            simp only [abs_mul]
      _ ≤ (|R i k| * |R j k|) * (2 * M) := by
        gcongr
        exact hshift k
      _ ≤ M * (|R i k| ^ 2 + |R j k| ^ 2) := by
        nlinarith [mul_nonneg (abs_nonneg (R i k)) (abs_nonneg (R j k))]
  have hrow (a : Fin p) :
      (∑ k, |R a k| ^ 2) ≤ ∑ u, ∑ k, |R u k| ^ 2 := by
    exact Finset.single_le_sum (fun u _ => Finset.sum_nonneg fun k _ => sq_nonneg |R u k|)
      (Finset.mem_univ a)
  have hentry : entryL2 R ^ 2 = ∑ u, ∑ k, |R u k| ^ 2 := by
    unfold entryL2
    rw [Real.sq_sqrt]
    positivity
  calc
    |∑ k, R i k * R j k * (s e₁ k - s e₀ k)| ≤
        ∑ k, |R i k * R j k * (s e₁ k - s e₀ k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, M * (|R i k| ^ 2 + |R j k| ^ 2) := by
      gcongr with k
      exact hterm k
    _ = M * ((∑ k, |R i k| ^ 2) + ∑ k, |R j k| ^ 2) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * M * (∑ u, ∑ k, |R u k| ^ 2) := by
      nlinarith [hrow i, hrow j]
    _ = 2 * M * entryL2 R ^ 2 := by rw [hentry]

/-- If [the scale is nonnegative, the determinant margin is positive, and the residual
bound is nonnegative](hyp:hM,hδ,hη), [all four coefficients have scale at most `2M`](hyp:hcoeff), [the two-by-two coefficient determinant is separated](hyp:hdet), [the
two displayed equations hold](hyp:heq₁,heq₂), and [both equation residuals are at most
`η`](hyp:hr₁,hr₂), then [both unknowns obey the conservative explicit Cramer bound](goal). -/
theorem pair_cramer_control {a b c d x y r₁ r₂ M δ η : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hcoeff : |a| ≤ 2 * M ∧ |b| ≤ 2 * M ∧
      |c| ≤ 2 * M ∧ |d| ≤ 2 * M)
    (hdet : δ ≤ |a * d - c * b|)
    (heq₁ : a * x + b * y = r₁) (heq₂ : c * x + d * y = r₂)
    (hr₁ : |r₁| ≤ η) (hr₂ : |r₂| ≤ η) :
    |x| ≤ pairwiseSolveFactor M δ * η ∧
      |y| ≤ pairwiseSolveFactor M δ * η := by
  have hxid : (a * d - c * b) * x = d * r₁ - b * r₂ := by
    rw [← heq₁, ← heq₂]
    ring_nf
  have hyid : (a * d - c * b) * y = a * r₂ - c * r₁ := by
    rw [← heq₁, ← heq₂]
    ring
  have hxnum : |d * r₁ - b * r₂| ≤ 4 * M * η := by
    calc
      |d * r₁ - b * r₂| ≤ |d * r₁| + |b * r₂| := abs_sub _ _
      _ = |d| * |r₁| + |b| * |r₂| := by simp only [abs_mul]
      _ ≤ (2 * M) * η + (2 * M) * η := by
        exact add_le_add
          (mul_le_mul hcoeff.2.2.2 hr₁ (abs_nonneg r₁) (by positivity))
          (mul_le_mul hcoeff.2.1 hr₂ (abs_nonneg r₂) (by positivity))
      _ = 4 * M * η := by ring
  have hynum : |a * r₂ - c * r₁| ≤ 4 * M * η := by
    calc
      |a * r₂ - c * r₁| ≤ |a * r₂| + |c * r₁| := abs_sub _ _
      _ = |a| * |r₂| + |c| * |r₁| := by simp only [abs_mul]
      _ ≤ (2 * M) * η + (2 * M) * η := by
        exact add_le_add
          (mul_le_mul hcoeff.1 hr₂ (abs_nonneg r₂) (by positivity))
          (mul_le_mul hcoeff.2.2.1 hr₁ (abs_nonneg r₁) (by positivity))
      _ = 4 * M * η := by ring
  have hxmul : δ * |x| ≤ 4 * M * η := by
    calc
      δ * |x| ≤ |a * d - c * b| * |x| := by gcongr
      _ = |d * r₁ - b * r₂| := by rw [← abs_mul, hxid]
      _ ≤ 4 * M * η := hxnum
  have hymul : δ * |y| ≤ 4 * M * η := by
    calc
      δ * |y| ≤ |a * d - c * b| * |y| := by gcongr
      _ = |a * r₂ - c * r₁| := by rw [← abs_mul, hyid]
      _ ≤ 4 * M * η := hynum
  constructor <;> unfold pairwiseSolveFactor <;>
    rw [div_mul_eq_mul_div] <;> apply (le_div_iff₀ hδ).2 <;>
    nlinarith [mul_nonneg hM hη]

/-- For [distinct selected coordinates](hyp:hij), [nonnegative scale and residual
parameters with a positive affine margin](hyp:hM,hδ,hε), [an exact invertible reference](hyp:hunit,hexact), [an off-diagonally approximate candidate](hyp:happrox), [bounded
shifts](hyp:hscale), and [one selected triple whose affine determinant separates the
coordinates](hyp:hdet), [both off-diagonal transition errors for that coordinate pair are
bounded by the selected triple's affine-system estimate](goal). -/
-- Proof route: put `Q = B B₀⁻¹ = I+R`.  Subtract the congruence equations at `e₀`
-- from those at `e₁,e₂`.  The `(i,j)` entries give a 2×2 system in `R i j` and
-- `R j i`; `coordinateProductRemainder_le` bounds its nonlinear terms and the two
-- off-diagonal residuals contribute `2ε`.  Apply `pair_cramer_control`.
theorem selectedTriple_offDiagonal_control {p : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix p) (s : E → Fin p → ℝ) (B₀ B : SqMatrix p)
    {M δ ε : ℝ} (i j : Fin p) (hij : i ≠ j) (e₀ e₁ e₂ : E)
    (hM : 0 ≤ M) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hscale : ShiftScaleBound s M)
    (hdet : δ ≤ |pairAffineDet s i j e₀ e₁ e₂|)
    (hunit : IsUnit B₀.det) (hexact : ExactCongruence A s B₀)
    (happrox : OffDiagonalApproximateCongruence A B ε) :
    let R := transitionError B₀ B
    let η := 2 * M * entryL2 R ^ 2 + 2 * ε
    |R i j| ≤ pairwiseSolveFactor M δ * η ∧
      |R j i| ≤ pairwiseSolveFactor M δ * η := by
  classical
  dsimp only
  let Q := transition B₀ B
  let R := transitionError B₀ B
  have hQR : Q = 1 + R := by
    ext u v
    simp [Q, R, transitionError, Matrix.sub_apply]
  have hformula (e : E) :
      (B * A e * B.transpose) i j =
        R i j * s e j + R j i * s e i +
          ∑ k, R i k * R j k * s e k := by
    rw [← transition_diagonal_congruence A s B₀ B hunit hexact e]
    have hentry :
        (Q * Matrix.diagonal (s e) * Q.transpose) i j =
          ∑ k, Q i k * s e k * Q j k := by
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
    change (Q * Matrix.diagonal (s e) * Q.transpose) i j = _
    rw [hentry, hQR]
    simp only [Matrix.add_apply, Matrix.one_apply]
    ring_nf
    repeat rw [Finset.sum_add_distrib]
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [if_neg hij]
    have hsum : (∑ k, R i k * s e k * R j k) =
        ∑ k, R i k * R j k * s e k := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hsum]
    ring
  have hlinear (e' e : E) :
      (s e' j - s e j) * R i j + (s e' i - s e i) * R j i =
        ((B * A e' * B.transpose) i j - (B * A e * B.transpose) i j) -
          ∑ k, R i k * R j k * (s e' k - s e k) := by
    rw [hformula e', hformula e]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  let a := s e₁ j - s e₀ j
  let b := s e₁ i - s e₀ i
  let c := s e₂ j - s e₀ j
  let d := s e₂ i - s e₀ i
  let r₁ := ((B * A e₁ * B.transpose) i j - (B * A e₀ * B.transpose) i j) -
    ∑ k, R i k * R j k * (s e₁ k - s e₀ k)
  let r₂ := ((B * A e₂ * B.transpose) i j - (B * A e₀ * B.transpose) i j) -
    ∑ k, R i k * R j k * (s e₂ k - s e₀ k)
  have heq₁ : a * R i j + b * R j i = r₁ := by
    simpa [a, b, r₁] using hlinear e₁ e₀
  have heq₂ : c * R i j + d * R j i = r₂ := by
    simpa [c, d, r₂] using hlinear e₂ e₀
  have hcoeff : |a| ≤ 2 * M ∧ |b| ≤ 2 * M ∧
      |c| ≤ 2 * M ∧ |d| ≤ 2 * M := by
    have hdiff (e' e : E) (k : Fin p) : |s e' k - s e k| ≤ 2 * M := by
      calc
        |s e' k - s e k| ≤ |s e' k| + |s e k| := abs_sub _ _
        _ ≤ M + M := add_le_add (hscale _ _) (hscale _ _)
        _ = 2 * M := by ring
    exact ⟨hdiff e₁ e₀ j, hdiff e₁ e₀ i,
      hdiff e₂ e₀ j, hdiff e₂ e₀ i⟩
  have hdet' : δ ≤ |a * d - c * b| := by
    have heqdet : a * d - c * b = -pairAffineDet s i j e₀ e₁ e₂ := by
      simp [a, b, c, d, pairAffineDet]
      ring
    rw [heqdet, abs_neg]
    exact hdet
  have houtput (e' e : E) :
      |(B * A e' * B.transpose) i j - (B * A e * B.transpose) i j| ≤
        2 * ε := by
    calc
      |_ - _| ≤ |(B * A e' * B.transpose) i j| +
          |(B * A e * B.transpose) i j| := abs_sub _ _
      _ ≤ ε + ε := add_le_add (happrox e' i j hij) (happrox e i j hij)
      _ = 2 * ε := by ring
  have hr₁ : |r₁| ≤ 2 * M * entryL2 R ^ 2 + 2 * ε := by
    dsimp [r₁]
    calc
      |_ - _| ≤
          |(B * A e₁ * B.transpose) i j - (B * A e₀ * B.transpose) i j| +
            |∑ k, R i k * R j k * (s e₁ k - s e₀ k)| := abs_sub _ _
      _ ≤ 2 * ε + 2 * M * entryL2 R ^ 2 :=
        add_le_add (houtput e₁ e₀)
          (coordinateProductRemainder_le s R hM hscale e₁ e₀ i j)
      _ = 2 * M * entryL2 R ^ 2 + 2 * ε := by ring
  have hr₂ : |r₂| ≤ 2 * M * entryL2 R ^ 2 + 2 * ε := by
    dsimp [r₂]
    calc
      |_ - _| ≤
          |(B * A e₂ * B.transpose) i j - (B * A e₀ * B.transpose) i j| +
            |∑ k, R i k * R j k * (s e₂ k - s e₀ k)| := abs_sub _ _
      _ ≤ 2 * ε + 2 * M * entryL2 R ^ 2 :=
        add_le_add (houtput e₂ e₀)
          (coordinateProductRemainder_le s R hM hscale e₂ e₀ i j)
      _ = 2 * M * entryL2 R ^ 2 + 2 * ε := by ring
  have hη : 0 ≤ 2 * M * entryL2 R ^ 2 + 2 * ε := by positivity
  change |R i j| ≤ _ ∧ |R j i| ≤ _
  exact pair_cramer_control hM hδ hη hcoeff hdet' heq₁ heq₂ hr₁ hr₂

/-- For [nonnegative scale and residual parameters with a positive affine margin](hyp:hM,hδ,hε), [pairwise affine-separated bounded shifts](hyp:hsep,hscale), [an exact
invertible reference](hyp:hunit,hexact), and [an off-diagonally approximate candidate](hyp:happrox), [every ordered off-diagonal transition error obeys the common pairwise
estimate](goal). -/
theorem pairwise_offDiagonal_control {p : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix p) (s : E → Fin p → ℝ) (B₀ B : SqMatrix p)
    {M δ ε : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hscale : ShiftScaleBound s M) (hsep : PairwiseAffineSeparated s δ)
    (hunit : IsUnit B₀.det) (hexact : ExactCongruence A s B₀)
    (happrox : OffDiagonalApproximateCongruence A B ε) :
    ∀ i j, i ≠ j →
      |transitionError B₀ B i j| ≤
        pairwiseSolveFactor M δ *
          (2 * M * entryL2 (transitionError B₀ B) ^ 2 + 2 * ε) := by
  intro i j hij
  obtain ⟨e₀, e₁, e₂, hdet⟩ := hsep i j hij
  exact (selectedTriple_offDiagonal_control A s B₀ B i j hij e₀ e₁ e₂
    hM hδ hε hscale hdet hunit hexact happrox).1

/-- For [an invertible reference](hyp:hunit), [unit-diagonal reference and candidate
matrices](hyp:hdiag₀,hdiag), [a nonnegative entry bound](hyp:hc), and [an off-diagonal
transition-entry bound](hyp:hoff),
[each diagonal transition error is controlled by the same row's off-diagonal entries and
the corresponding reference column](goal). -/
-- Proof route: `B = (I+R)B₀`; comparing diagonal entries gives
-- `R i i = -∑_{k≠i} R i k B₀ k i`, then apply Cauchy--Schwarz.
theorem diagonalBranch_control {p : ℕ} (B₀ B : SqMatrix p) {c : ℝ}
    (hunit : IsUnit B₀.det) (hdiag₀ : UnitDiagonal B₀)
    (hdiag : UnitDiagonal B) (hc : 0 ≤ c)
    (hoff : ∀ i j, i ≠ j → |transitionError B₀ B i j| ≤ c) :
    ∀ i,
      |transitionError B₀ B i i| ^ 2 ≤
        ‖B₀‖ ^ 2 * ∑ k ∈ (Finset.univ.erase i),
          |transitionError B₀ B i k| ^ 2 := by
  classical
  let R := transitionError B₀ B
  have hRB : R * B₀ = B - B₀ := by
    dsimp [R, transitionError, transition]
    rw [Matrix.sub_mul, Matrix.one_mul]
    simpa only [Matrix.mul_assoc] using
      congrArg (fun X : SqMatrix p => X - B₀)
        (Matrix.nonsing_inv_mul_cancel_right B₀ B hunit)
  intro i
  have hentry := congrArg (fun X : SqMatrix p => X i i) hRB
  simp only [Matrix.mul_apply, Matrix.sub_apply, hdiag i, hdiag₀ i, sub_self] at hentry
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin p))
    (fun k => R i k * B₀ k i) (Finset.mem_univ i)
  have heq : R i i = -∑ k ∈ Finset.univ.erase i, R i k * B₀ k i := by
    rw [← hsplit, hdiag₀ i, mul_one] at hentry
    linarith
  have hcolumn : ∑ k ∈ Finset.univ.erase i, |B₀ k i| ^ 2 ≤ ‖B₀‖ ^ 2 := by
    let e : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 (Pi.single i 1)
    have he : ‖e‖ = 1 := by simp [e]
    have hmul := Matrix.l2_opNorm_mulVec B₀ e
    rw [he, mul_one] at hmul
    have hfull : ∑ k, |B₀ k i| ^ 2 ≤ ‖B₀‖ ^ 2 := by
      have hsquare := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmul
      rw [EuclideanSpace.norm_sq_eq] at hsquare
      simpa [e, Matrix.mulVec, dotProduct, sq_abs] using hsquare
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans hfull
  change |R i i| ^ 2 ≤ ‖B₀‖ ^ 2 * ∑ k ∈ Finset.univ.erase i, |R i k| ^ 2
  rw [heq, abs_neg, sq_abs]
  calc
    (∑ k ∈ Finset.univ.erase i, R i k * B₀ k i) ^ 2 ≤
        (∑ k ∈ Finset.univ.erase i, (R i k) ^ 2) *
          ∑ k ∈ Finset.univ.erase i, (B₀ k i) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ k ∈ Finset.univ.erase i, |R i k| ^ 2) *
          ∑ k ∈ Finset.univ.erase i, |B₀ k i| ^ 2 := by
      simp only [sq_abs]
    _ ≤ (∑ k ∈ Finset.univ.erase i, |R i k| ^ 2) * ‖B₀‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left hcolumn
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = ‖B₀‖ ^ 2 * ∑ k ∈ Finset.univ.erase i, |R i k| ^ 2 := by ring

/-- For [positive dimension and nonnegative matrix and entry bounds](hyp:hp,hL,hc), [an
invertible unit-diagonal reference and a unit-diagonal candidate](hyp:hunit,hdiag₀,hdiag),
[a reference norm bound](hyp:hB₀), and [a common off-diagonal transition-entry bound](hyp:hoff), [the full transition error's entrywise L² size is bounded by the ordered-pair
aggregation factor](goal). -/
theorem entryL2_transitionError_le {p : ℕ} (B₀ B : SqMatrix p) {L c : ℝ}
    (hp : 0 < p) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hunit : IsUnit B₀.det) (hdiag₀ : UnitDiagonal B₀)
    (hdiag : UnitDiagonal B) (hB₀ : ‖B₀‖ ≤ L)
    (hoff : ∀ i j, i ≠ j → |transitionError B₀ B i j| ≤ c) :
    entryL2 (transitionError B₀ B) ≤
      c * Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2)) := by
  classical
  let R := transitionError B₀ B
  have hdiagControl := diagonalBranch_control B₀ B hunit hdiag₀ hdiag hc hoff
  have hnormsq : ‖B₀‖ ^ 2 ≤ L ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hL).mpr hB₀
  have hoffSq (i k : Fin p) (hik : i ≠ k) : |R i k| ^ 2 ≤ c ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg _) hc).mpr (by simpa [R] using hoff i k hik)
  have herase (i : Fin p) :
      ∑ k ∈ Finset.univ.erase i, |R i k| ^ 2 ≤ (p - 1 : ℕ) * c ^ 2 := by
    calc
      ∑ k ∈ Finset.univ.erase i, |R i k| ^ 2 ≤
          (Finset.univ.erase i).card • c ^ 2 :=
        Finset.sum_le_card_nsmul _ _ _ (fun k hk =>
          hoffSq i k (by simpa [ne_comm] using (Finset.mem_erase.mp hk).1))
      _ = (p - 1 : ℕ) * c ^ 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
        norm_num
  have hrow (i : Fin p) :
      ∑ k, |R i k| ^ 2 ≤
        (1 + L ^ 2) * ∑ k ∈ Finset.univ.erase i, |R i k| ^ 2 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin p))
      (fun k => |R i k| ^ 2) (Finset.mem_univ i)
    rw [← hsplit]
    calc
      (∑ k ∈ Finset.univ.erase i, |R i k| ^ 2) + |R i i| ^ 2 ≤
          (∑ k ∈ Finset.univ.erase i, |R i k| ^ 2) +
            ‖B₀‖ ^ 2 * ∑ k ∈ Finset.univ.erase i, |R i k| ^ 2 := by
        gcongr
        simpa [R] using hdiagControl i
      _ ≤ (∑ k ∈ Finset.univ.erase i, |R i k| ^ 2) +
            L ^ 2 * ∑ k ∈ Finset.univ.erase i, |R i k| ^ 2 := by
        gcongr
      _ = (1 + L ^ 2) * ∑ k ∈ Finset.univ.erase i, |R i k| ^ 2 := by ring
  have hsum : ∑ i, ∑ k, |R i k| ^ 2 ≤
      (p : ℝ) * (p - 1 : ℕ) * c ^ 2 * (1 + L ^ 2) := by
    calc
      ∑ i, ∑ k, |R i k| ^ 2 ≤
          ∑ i, (1 + L ^ 2) * ∑ k ∈ Finset.univ.erase i, |R i k| ^ 2 := by
        gcongr with i
        exact hrow i
      _ ≤ ∑ _i : Fin p, (1 + L ^ 2) * ((p - 1 : ℕ) * c ^ 2) := by
        gcongr with i
        exact herase i
      _ = (p : ℝ) * (p - 1 : ℕ) * c ^ 2 * (1 + L ^ 2) := by
        simp [Finset.card_univ, Fintype.card_fin]
        ring
  unfold entryL2
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      ∑ i, ∑ j, |R i j| ^ 2 ≤
          (p : ℝ) * (p - 1 : ℕ) * c ^ 2 * (1 + L ^ 2) := hsum
      _ = (c * Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt]
        · ring
        · positivity

end Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine
