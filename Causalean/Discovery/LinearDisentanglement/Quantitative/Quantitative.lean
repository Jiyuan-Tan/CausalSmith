/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Quantitative.Definitions

/-!
# Explicit quantitative simultaneous-congruence stability

This module proves a finite-dimensional residual-to-distance estimate.  Affine minor
separation first controls coordinatewise products of the transition matrix.  Unit-diagonal
normalization and the explicit small-residual threshold select the reference branch, after
which coordinate bounds convert to a Euclidean operator-norm bound.
-/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.Quantitative

open scoped Matrix.Norms.Frobenius in
private theorem l2CLM_norm_le_frobenius {d : ℕ} (M : SqMatrix d) :
    ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) M‖ ≤ ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M) fun x => ?_
  have hmul := Matrix.frobenius_norm_mul M
    (Matrix.replicateCol Unit (WithLp.ofLp x))
  have heq :
      M * Matrix.replicateCol Unit (WithLp.ofLp x) =
        Matrix.replicateCol Unit (M *ᵥ WithLp.ofLp x) := by
    ext i u
    simp [Matrix.mul_apply, Matrix.mulVec, Matrix.replicateCol, dotProduct]
  rw [heq, Matrix.frobenius_norm_replicateCol] at hmul
  rw [← Matrix.toEuclideanCLM_toLp M (WithLp.ofLp x), WithLp.toLp_ofLp] at hmul
  simpa using hmul

private theorem abs_det_updateCol_le {d : ℕ} (V : SqMatrix d)
    (b : Fin d → ℝ) (j : Fin d) {C η : ℝ} (hC : 0 ≤ C)
    (hV : ∀ i k, |V i k| ≤ C) (hb : ∀ i, |b i| ≤ η) :
    |(V.updateCol j b).det| ≤ (Nat.factorial d : ℝ) * C ^ (d - 1) * η := by
  classical
  rw [Matrix.det_apply]
  calc
    |∑ σ : Equiv.Perm (Fin d), Equiv.Perm.sign σ •
        ∏ k, (V.updateCol j b) (σ k) k| ≤
        ∑ σ : Equiv.Perm (Fin d),
          |Equiv.Perm.sign σ • ∏ k, (V.updateCol j b) (σ k) k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), C ^ (d - 1) * η := by
      gcongr with σ
      have hsign :
          |Equiv.Perm.sign σ • (∏ k, (V.updateCol j b) (σ k) k)| =
            |∏ k, (V.updateCol j b) (σ k) k| := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · simp [h]
        · simp [h]
      rw [hsign, Finset.abs_prod]
      rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin d))
        (fun k => |(V.updateCol j b) (σ k) k|) (Finset.mem_univ j)]
      apply mul_le_mul
      · calc
          ∏ k ∈ (Finset.univ.erase j), |(V.updateCol j b) (σ k) k| ≤
              ∏ _k ∈ (Finset.univ.erase j), C := by
                apply Finset.prod_le_prod
                · intros
                  positivity
                · intro k hk
                  simp only [Finset.mem_erase] at hk
                  simp [hk.1, hV]
          _ = C ^ (d - 1) := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
              Finset.card_univ, Fintype.card_fin]
      · simpa using hb (σ j)
      · positivity
      · positivity
    _ = (Nat.factorial d : ℝ) * C ^ (d - 1) * η := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]
      ring

private theorem diagonal_difference_mulVec {d : ℕ} (M : SqMatrix d)
    (s₁ s₀ : Fin d → ℝ) (i k : Fin d) :
    let V : SqMatrix d := fun _k a => s₁ a - s₀ a
    let y : Fin d → ℝ := fun a => M i a ^ 2 - if i = a then 1 else 0
    (V *ᵥ y) k =
      ((M * Matrix.diagonal s₁ * M.transpose - Matrix.diagonal s₁) i i) -
      ((M * Matrix.diagonal s₀ * M.transpose - Matrix.diagonal s₀) i i) := by
  dsimp only
  have hentry (t : Fin d → ℝ) :
      (M * Matrix.diagonal t * M.transpose) i i =
        ∑ a, M i a * t a * M i a := by
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.sub_apply]
  rw [hentry s₁, hentry s₀]
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, if_pos]
  have hsum :
      (∑ a : Fin d, if i = a then (s₁ a - s₀ a) else 0) = s₁ i - s₀ i := by
    simp
  have hsumprod :
      (∑ a, M i a ^ 2 * (s₁ a - s₀ a)) =
        (∑ a, M i a * s₁ a * M i a) -
          ∑ a, M i a * s₀ a * M i a := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  calc
    (∑ a, (s₁ a - s₀ a) * (M i a ^ 2 - if i = a then 1 else 0)) =
        ∑ a, (M i a ^ 2 * (s₁ a - s₀ a) -
          if i = a then (s₁ a - s₀ a) else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases h : i = a <;> simp [h] <;> ring
    _ = (∑ a, M i a ^ 2 * (s₁ a - s₀ a)) - (s₁ i - s₀ i) := by
      rw [Finset.sum_sub_distrib, hsum]
    _ = (∑ a, M i a * s₁ a * M i a) - s₁ i -
        ((∑ a, M i a * s₀ a * M i a) - s₀ i) := by
          rw [hsumprod]
          ring

private theorem offDiagonal_difference_mulVec {d : ℕ} (M : SqMatrix d)
    (s₁ s₀ : Fin d → ℝ) (i j k : Fin d) (hij : i ≠ j) :
    let V : SqMatrix d := fun _k a => s₁ a - s₀ a
    let y : Fin d → ℝ := fun a => M i a * M j a
    (V *ᵥ y) k =
      ((M * Matrix.diagonal s₁ * M.transpose - Matrix.diagonal s₁) i j) -
      ((M * Matrix.diagonal s₀ * M.transpose - Matrix.diagonal s₀) i j) := by
  dsimp only
  have hentry (t : Fin d → ℝ) :
      (M * Matrix.diagonal t * M.transpose) i j =
        ∑ a, M i a * t a * M j a := by
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.sub_apply]
  rw [hentry s₁, hentry s₀]
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, if_neg hij]
  rw [sub_zero, sub_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- For [a real square matrix](hyp:M) and [a selected row and column](hyp:i,j), [the
absolute value of that entry is bounded by the Euclidean operator norm](goal). -/
theorem abs_entry_le_opNorm {d : ℕ} (M : SqMatrix d) (i j : Fin d) :
    |M i j| ≤ ‖M‖ := by
  classical
  let e : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single j 1)
  have he : ‖e‖ = 1 := by simp [e]
  have hcoord :
      |((EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ e)) i| ≤
        ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ e)‖ := by
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ e)) i
  calc
    |M i j| = |((EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ e)) i| := by simp [e]
    _ ≤ ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ e)‖ := hcoord
    _ ≤ ‖M‖ * ‖e‖ := Matrix.l2_opNorm_mulVec M e
    _ = ‖M‖ := by rw [he, mul_one]

/-- For [a real square matrix](hyp:M), if [the proposed entry bound is nonnegative](hyp:hc)
and [every entry obeys that bound](hyp:hM), [its Euclidean operator norm is at most the
dimension times the bound](goal). -/
theorem opNorm_le_dimension_mul_of_entry_bound {d : ℕ} (M : SqMatrix d) {c : ℝ}
    (hc : 0 ≤ c) (hM : ∀ i j, |M i j| ≤ c) :
    ‖M‖ ≤ (d : ℝ) * c := by
  rw [Matrix.cstar_norm_def]
  calc
    ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) M‖ ≤
        @norm (SqMatrix d) Matrix.frobeniusNormedAddCommGroup.toNorm M :=
      l2CLM_norm_le_frobenius M
    _ = Real.sqrt (∑ i, ∑ j, |M i j| ^ 2) := by
      rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
      simp only [Real.rpow_two, Real.norm_eq_abs]
    _ ≤ (d : ℝ) * c := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · calc
          ∑ i, ∑ j, |M i j| ^ 2 ≤ ∑ _i : Fin d, ∑ _j : Fin d, c ^ 2 := by
            gcongr with i j
            exact hM i j
          _ = ((d : ℝ) * c) ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring

/-- For [a real square coefficient matrix](hyp:V) and [a solution vector](hyp:x), if [the
determinant margin is positive](hyp:hδ), [the scale bound is nonnegative](hyp:hL), [every
coefficient is bounded](hyp:hV), [the determinant has the stated margin](hyp:hdet), and
[the linear-system residual is uniformly bounded](hyp:hres), [every solution coordinate is
bounded by the explicit Cramer's-rule factor times the residual bound](goal). -/
-- Proof route: use `V⁻¹ *ᵥ (V *ᵥ x) = x`, expand `V⁻¹` through the adjugate (or use
-- `Matrix.det_smul_inv_mulVec_eq_cramer`), expand each `(d-1)`-minor determinant, and
-- bound its `factorial (d-1)` Leibniz terms by `(2L)^(d-1)`.
theorem coordinate_le_affineSolveFactor {d : ℕ} (V : SqMatrix d) (x : Fin d → ℝ)
    {L δ η : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hV : ∀ i j, |V i j| ≤ 2 * L)
    (hdet : δ ≤ |V.det|)
    (hres : ∀ i, |(V *ᵥ x) i| ≤ η) :
    ∀ j, |x j| ≤ affineSolveFactor d L δ * η := by
  classical
  intro j
  have hdet0 : V.det ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    linarith
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hdet0
  let b := V *ᵥ x
  have hx : V⁻¹ *ᵥ b = x := by
    rw [show b = V *ᵥ x from rfl, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul V hunit, Matrix.one_mulVec]
  have hcramer := congrFun (V.det_smul_inv_mulVec_eq_cramer b hunit) j
  have heq : V.det * x j = (V.updateCol j b).det := by
    simpa [hx, Matrix.cramer_apply] using hcramer
  have hbound :
      |(V.updateCol j b).det| ≤
        (Nat.factorial d : ℝ) * (2 * L) ^ (d - 1) * η :=
    abs_det_updateCol_le V b j (by positivity) hV hres
  have hmul :
      δ * |x j| ≤ (Nat.factorial d : ℝ) * (2 * L) ^ (d - 1) * η := by
    calc
      δ * |x j| ≤ |V.det| * |x j| := by gcongr
      _ = |(V.updateCol j b).det| := by rw [← abs_mul, heq]
      _ ≤ _ := hbound
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Fin.pos_iff_nonempty.mpr ⟨j⟩)
  have hfac : (d : ℝ) * (Nat.factorial (d - 1) : ℝ) =
      (Nat.factorial d : ℝ) := by
    norm_cast
    exact Nat.mul_factorial_pred hd0
  unfold affineSolveFactor
  rw [mul_assoc, div_mul_eq_mul_div]
  apply (le_div_iff₀ hδ).2
  calc
    |x j| * δ = δ * |x j| := mul_comm _ _
    _ ≤ (Nat.factorial d : ℝ) * (2 * L) ^ (d - 1) * η := hmul
    _ = (d : ℝ) * ((Nat.factorial (d - 1) : ℝ) * (2 * L) ^ (d - 1)) * η := by
      rw [← hfac]
      ring

/-- For [a real matrix family](hyp:A), [its diagonal shifts](hyp:s), [an exact reference
matrix](hyp:B₀), [a candidate matrix](hyp:B), if [the reference is invertible](hyp:hunit)
and [it exactly realizes every prescribed congruence](hyp:hexact), then [the transition
matrix conjugates each reference diagonal into the candidate congruence](goal). -/
theorem transition_diagonal_congruence {d : ℕ} {E : Type*} [Fintype E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B₀ B : SqMatrix d)
    (hunit : IsUnit B₀.det) (hexact : ExactCongruence A s B₀) (e : E) :
    transition B₀ B * Matrix.diagonal (s e) * (transition B₀ B).transpose =
      B * A e * B.transpose := by
  rw [← hexact e]
  unfold transition
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  have hut : IsUnit B₀.transpose.det := Matrix.isUnit_det_transpose B₀ hunit
  calc
    (B * B₀⁻¹) * (B₀ * A e * B₀.transpose) * ((B₀.transpose)⁻¹ * B.transpose) =
        B * (B₀⁻¹ * B₀) * A e * (B₀.transpose * (B₀.transpose)⁻¹) * B.transpose := by
          noncomm_ring
    _ = B * A e * B.transpose := by
      rw [Matrix.nonsing_inv_mul B₀ hunit,
        Matrix.mul_nonsing_inv B₀.transpose hut]
      simp

/-- For [a finite real matrix family](hyp:A), [its prescribed diagonal shifts](hyp:s), [an
exact reference](hyp:B₀), and [a candidate](hyp:B), if [the shift scale is nonnegative](hyp:hL),
[the affine separation margin is positive](hyp:hδ), [the shifts obey their scale bound](hyp:hscale),
[a separated affine minor exists](hyp:hsep), [the reference is invertible](hyp:hunit), [the
reference realizes the congruences exactly](hyp:hexact), and [the candidate has the stated
approximate residual](hyp:happrox), then [squared transition entries and cross-row products
have the explicit coordinatewise residual bounds](goal). -/
-- Proof route: choose `base,pick` from `hsep`, subtract each picked congruence equation
-- from the base equation, and apply `coordinate_le_affineSolveFactor`.  On diagonal
-- matrix entries solve for `M i a ^ 2 - 1_{i=a}`; off the diagonal solve for
-- `M i a * M j a`.  `abs_entry_le_opNorm` and the triangle inequality give `2ε`.
theorem transition_coordinate_product_control {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B₀ B : SqMatrix d)
    {L δ ε : ℝ}
    (hL : 0 ≤ L) (hδ : 0 < δ)
    (hscale : ShiftScaleBound s L) (hsep : AffineMinorSeparated s δ)
    (hunit : IsUnit B₀.det) (hexact : ExactCongruence A s B₀)
    (happrox : ApproximateCongruence A s B ε) :
    (∀ i a, |(transition B₀ B i a) ^ 2 - if i = a then 1 else 0| ≤
      productControlFactor d L δ * ε) ∧
    (∀ i j a, i ≠ j →
      |transition B₀ B i a * transition B₀ B j a| ≤
        productControlFactor d L δ * ε) := by
  classical
  obtain ⟨base, pick, hdet⟩ := hsep
  let M := transition B₀ B
  let V : SqMatrix d := fun k a => s (pick k) a - s base a
  have hV : ∀ k a, |V k a| ≤ 2 * L := by
    intro k a
    dsimp [V]
    calc
      |s (pick k) a - s base a| ≤ |s (pick k) a| + |s base a| := abs_sub _ _
      _ ≤ L + L := add_le_add (hscale _ _) (hscale _ _)
      _ = 2 * L := by ring
  have hdef : ∀ e i j, |congruenceDefect (A e) (s e) B i j| ≤ ε := by
    intro e i j
    calc
      |congruenceDefect (A e) (s e) B i j| ≤
          ‖congruenceDefect (A e) (s e) B‖ := abs_entry_le_opNorm _ _ _
      _ ≤ ε := (simultaneousCongruenceResidual_le_iff A s B ε).mp happrox e
  have hdefM : ∀ e i j,
      |(M * Matrix.diagonal (s e) * M.transpose - Matrix.diagonal (s e)) i j| ≤ ε := by
    intro e i j
    rw [transition_diagonal_congruence A s B₀ B hunit hexact e]
    exact hdef e i j
  constructor
  · intro i a
    let y : Fin d → ℝ := fun b => M i b ^ 2 - if i = b then 1 else 0
    have hres : ∀ k, |(V *ᵥ y) k| ≤ 2 * ε := by
      intro k
      have hid : (V *ᵥ y) k =
          ((M * Matrix.diagonal (s (pick k)) * M.transpose -
              Matrix.diagonal (s (pick k))) i i) -
            ((M * Matrix.diagonal (s base) * M.transpose -
              Matrix.diagonal (s base)) i i) :=
        diagonal_difference_mulVec M (s (pick k)) (s base) i k
      rw [hid]
      calc
        |_ - _| ≤
            |(M * Matrix.diagonal (s (pick k)) * M.transpose -
                Matrix.diagonal (s (pick k))) i i| +
              |(M * Matrix.diagonal (s base) * M.transpose -
                Matrix.diagonal (s base)) i i| := abs_sub _ _
        _ ≤ ε + ε := add_le_add (hdefM _ _ _) (hdefM _ _ _)
        _ = 2 * ε := by ring
    have hy := coordinate_le_affineSolveFactor V y hδ hL hV hdet hres a
    change |M i a ^ 2 - if i = a then 1 else 0| ≤ _
    change |y a| ≤ _ at hy
    unfold productControlFactor
    nlinarith
  · intro i j a hij
    let y : Fin d → ℝ := fun b => M i b * M j b
    have hres : ∀ k, |(V *ᵥ y) k| ≤ 2 * ε := by
      intro k
      have hid : (V *ᵥ y) k =
          ((M * Matrix.diagonal (s (pick k)) * M.transpose -
              Matrix.diagonal (s (pick k))) i j) -
            ((M * Matrix.diagonal (s base) * M.transpose -
              Matrix.diagonal (s base)) i j) :=
        offDiagonal_difference_mulVec M (s (pick k)) (s base) i j k hij
      rw [hid]
      calc
        |_ - _| ≤
            |(M * Matrix.diagonal (s (pick k)) * M.transpose -
                Matrix.diagonal (s (pick k))) i j| +
              |(M * Matrix.diagonal (s base) * M.transpose -
                Matrix.diagonal (s base)) i j| := abs_sub _ _
        _ ≤ ε + ε := add_le_add (hdefM _ _ _) (hdefM _ _ _)
        _ = 2 * ε := by ring
    have hy := coordinate_le_affineSolveFactor V y hδ hL hV hdet hres a
    change |M i a * M j a| ≤ _
    change |y a| ≤ _ at hy
    unfold productControlFactor
    nlinarith

/-- For [positive matrix dimension](hyp:hd), [positive shift scale](hyp:hL), [positive
affine separation](hyp:hδ), and [positive matrix scale](hyp:hR), if [the shifts have the
declared scale](hyp:hscale), [their affine minor is separated](hyp:hsep), [the reference is
unit-diagonal](hyp:hnorm₀), [the candidate is unit-diagonal](hyp:hnorm), [both matrices
obey the scale bound](hyp:hmatrixScale), [both matrices obey the condition bound](hyp:hcond),
[the reference congruences are exact](hyp:hexact), [the residual tolerance is nonnegative](hyp:hε),
[it is below the admissible radius](hyp:hsmall), and [the candidate is approximately
congruent](hyp:happrox), then [every transition diagonal entry is at least one half](goal). -/
-- Proof route: square control first gives `|M i a| ≤ sqrt(qε)` for `a ≠ i`.  From
-- `B = M B₀` and both unit diagonals, bound `|M i i - 1|` by the off-diagonal terms
-- times entries of `B₀`, hence by `d R sqrt(qε)`.  The second threshold makes this ≤ 1/2.
theorem transition_diagonal_ge_half {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B₀ B : SqMatrix d)
    {L δ R κ ε : ℝ}
    (hd : 0 < d) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (hscale : ShiftScaleBound s L) (hsep : AffineMinorSeparated s δ)
    (hnorm₀ : UnitDiagonal B₀) (hnorm : UnitDiagonal B)
    (hmatrixScale : PairMatrixScaleBound R B₀ B)
    (hcond : PairConditionBound κ B₀ B)
    (hexact : ExactCongruence A s B₀)
    (hε : 0 ≤ ε) (hsmall : ε ≤ admissibleRadius d L δ R κ)
    (happrox : ApproximateCongruence A s B ε) :
    ∀ i, (1 : ℝ) / 2 ≤ transition B₀ B i i := by
  classical
  let q := productControlFactor d L δ
  let K := R * max 1 κ
  let M := transition B₀ B
  have hq : 0 < q := productControlFactor_pos hd hL hδ
  have hmax : 0 < max 1 κ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK : 0 < K := mul_pos hR hmax
  have hunit : IsUnit B₀.det := hcond.1.1
  have hcontrol := transition_coordinate_product_control A s B₀ B hL.le hδ hscale hsep
    hunit hexact happrox
  have heps : ε ≤ 1 / (4 * (d : ℝ) ^ 2 * K ^ 2 * q) := by
    exact hsmall.trans (min_le_right _ _)
  have hqeps : q * ε ≤ (1 / (2 * (d : ℝ) * K)) ^ 2 := by
    calc
      q * ε ≤ q * (1 / (4 * (d : ℝ) ^ 2 * K ^ 2 * q)) :=
        mul_le_mul_of_nonneg_left heps hq.le
      _ = (1 / (2 * (d : ℝ) * K)) ^ 2 := by
        field_simp [ne_of_gt hq, ne_of_gt hK, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)]
        ring
  have hoff : ∀ i a, i ≠ a → |M i a| ≤ 1 / (2 * (d : ℝ) * K) := by
    intro i a hia
    have hsquare := hcontrol.1 i a
    change |M i a ^ 2 - (if i = a then 1 else 0)| ≤ q * ε at hsquare
    simp only [if_neg hia, sub_zero, abs_sq] at hsquare
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    exact hsquare.trans hqeps
  have hB₀entry : ∀ a i, |B₀ a i| ≤ R := by
    intro a i
    exact (abs_entry_le_opNorm B₀ a i).trans hmatrixScale.1
  have hMB : M * B₀ = B := by
    dsimp [M, transition]
    simpa only [Matrix.mul_assoc] using
      Matrix.nonsing_inv_mul_cancel_right B₀ B hunit
  intro i
  have hentry := congrArg (fun N : SqMatrix d => N i i) hMB
  simp only [Matrix.mul_apply] at hentry
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin d))
    (fun a => M i a * B₀ a i) (Finset.mem_univ i)
  rw [← hsplit] at hentry
  rw [hnorm₀ i, mul_one, hnorm i] at hentry
  have heq : M i i - 1 = -∑ a ∈ Finset.univ.erase i, M i a * B₀ a i := by
    linarith
  have habs : |M i i - 1| ≤ 1 / 2 := by
    rw [heq, abs_neg]
    calc
        |∑ a ∈ Finset.univ.erase i, M i a * B₀ a i| ≤
            ∑ a ∈ Finset.univ.erase i, |M i a * B₀ a i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ Finset.univ.erase i, 1 / (2 * (d : ℝ)) := by
          gcongr with a ha
          rw [abs_mul]
          have hia : i ≠ a := by
            exact fun h => (Finset.mem_erase.mp ha).1 h.symm
          calc
            |M i a| * |B₀ a i| ≤ (1 / (2 * (d : ℝ) * K)) * R := by
              gcongr
              exact hoff i a hia
              exact hB₀entry a i
            _ ≤ 1 / (2 * (d : ℝ)) := by
              have hRK : R ≤ K := by
                dsimp [K]
                nlinarith [le_max_left (1 : ℝ) κ]
              field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd), ne_of_gt hK]
              nlinarith
        _ ≤ ∑ _a ∈ Finset.univ, 1 / (2 * (d : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          intros
          positivity
        _ = 1 / 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]
          field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)]
  change (1 : ℝ) / 2 ≤ M i i
  have := (abs_le.mp habs).1
  linarith

/-- **Explicit simultaneous-congruence stability.** For [positive matrix dimension](hyp:hd),
[positive shift scale](hyp:hL), [positive affine separation](hyp:hδ), and [positive matrix
scale](hyp:hR), if [the diagonal shifts obey their scale bound](hyp:hscale), [the shift
family has a separated affine minor](hyp:hsep), [the reference is unit-diagonal](hyp:hnorm₀),
[the candidate is unit-diagonal](hyp:hnorm), [the pair obeys the matrix scale bound](hyp:hmatrixScale),
[the pair obeys the condition-number bound](hyp:hcond), [the reference realizes every
congruence exactly](hyp:hexact), [the residual tolerance is nonnegative](hyp:hε), [the
tolerance is admissibly small](hyp:hsmall), and [the candidate realizes the congruences up
to that tolerance](hyp:happrox), then [the candidate is within the explicit linear modulus
times the tolerance of the reference in Euclidean operator norm](goal). -/
-- Proof route: the preceding half-bound and cross-product control give
-- `|M i a| ≤ 2qε` for `i ≠ a`; square control bounds `|M i i - 1|`.  Convert this to
-- `‖M-I‖ ≤ 2d qε`, write `B-B₀ = (M-I)B₀`, use `‖B₀‖ ≤ R`, and weaken by
-- `1 ≤ max 1 κ`.
theorem opNorm_sub_le_of_approximate_simultaneous_congruence {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) (B₀ B : SqMatrix d)
    {L δ R κ ε : ℝ}
    (hd : 0 < d) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R)
    (hscale : ShiftScaleBound s L) (hsep : AffineMinorSeparated s δ)
    (hnorm₀ : UnitDiagonal B₀) (hnorm : UnitDiagonal B)
    (hmatrixScale : PairMatrixScaleBound R B₀ B)
    (hcond : PairConditionBound κ B₀ B)
    (hexact : ExactCongruence A s B₀)
    (hε : 0 ≤ ε) (hsmall : ε ≤ admissibleRadius d L δ R κ)
    (happrox : ApproximateCongruence A s B ε) :
    ‖B - B₀‖ ≤ stabilityConstant d L δ R κ * ε := by
  classical
  let q := productControlFactor d L δ
  let M := transition B₀ B
  have hq : 0 < q := productControlFactor_pos hd hL hδ
  have hqε : 0 ≤ q * ε := mul_nonneg hq.le hε
  have hunit : IsUnit B₀.det := hcond.1.1
  have hcontrol := transition_coordinate_product_control A s B₀ B hL.le hδ hscale hsep
    hunit hexact happrox
  have hhalf := transition_diagonal_ge_half A s B₀ B hd hL hδ hR hscale hsep
    hnorm₀ hnorm hmatrixScale hcond hexact hε hsmall happrox
  have hoff : ∀ i a, i ≠ a → |M i a| ≤ 2 * q * ε := by
    intro i a hia
    have hp := hcontrol.2 i a a hia
    change |M i a * M a a| ≤ q * ε at hp
    rw [abs_mul] at hp
    have haa : (1 : ℝ) / 2 ≤ |M a a| :=
      (show (1 : ℝ) / 2 ≤ M a a from hhalf a).trans (le_abs_self _)
    have hmul : |M i a| * ((1 : ℝ) / 2) ≤ |M i a| * |M a a| :=
      mul_le_mul_of_nonneg_left haa (abs_nonneg _)
    nlinarith
  have hdiag : ∀ i, |M i i - 1| ≤ 2 * q * ε := by
    intro i
    have hsquare := hcontrol.1 i i
    simp only [if_pos rfl] at hsquare
    change |M i i ^ 2 - 1| ≤ q * ε at hsquare
    have hi : (1 : ℝ) / 2 ≤ M i i := hhalf i
    have hplus : 1 ≤ |M i i + 1| := by
      rw [abs_of_nonneg]
      · linarith
      · linarith
    have hfactor : |M i i - 1| * |M i i + 1| = |M i i ^ 2 - 1| := by
      rw [← abs_mul]
      congr 1
      ring
    calc
      |M i i - 1| ≤ |M i i - 1| * |M i i + 1| := by
        nlinarith [mul_le_mul_of_nonneg_left hplus (abs_nonneg (M i i - 1))]
      _ = |M i i ^ 2 - 1| := hfactor
      _ ≤ q * ε := hsquare
      _ ≤ 2 * q * ε := by nlinarith
  have hentry : ∀ i a, |(M - 1) i a| ≤ 2 * q * ε := by
    intro i a
    by_cases hia : i = a
    · subst a
      simpa using hdiag i
    · simpa [Matrix.sub_apply, Matrix.one_apply, hia] using hoff i a hia
  have hMnorm : ‖M - 1‖ ≤ (d : ℝ) * (2 * q * ε) :=
    opNorm_le_dimension_mul_of_entry_bound (M - 1) (by positivity) hentry
  have hMB : M * B₀ = B := by
    dsimp [M, transition]
    simpa only [Matrix.mul_assoc] using
      Matrix.nonsing_inv_mul_cancel_right B₀ B hunit
  have hfactor : B - B₀ = (M - 1) * B₀ := by
    rw [Matrix.sub_mul, Matrix.one_mul, hMB]
  rw [hfactor]
  calc
    ‖(M - 1) * B₀‖ ≤ ‖M - 1‖ * ‖B₀‖ := norm_mul_le _ _
    _ ≤ ((d : ℝ) * (2 * q * ε)) * R := by
      exact mul_le_mul hMnorm hmatrixScale.1 (norm_nonneg _) (by positivity)
    _ = 2 * (d : ℝ) * R * q * ε := by ring
    _ ≤ 2 * (d : ℝ) * R * max 1 κ * q * ε := by
      have hm := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) κ)
        (show 0 ≤ 2 * (d : ℝ) * R * q * ε by positivity)
      calc
        2 * (d : ℝ) * R * q * ε = (2 * (d : ℝ) * R * q * ε) * 1 := by ring
        _ ≤ (2 * (d : ℝ) * R * q * ε) * max 1 κ := hm
        _ = 2 * (d : ℝ) * R * max 1 κ * q * ε := by ring
    _ = stabilityConstant d L δ R κ * ε := by
      dsimp [q]
      unfold stabilityConstant
      ring

end Causalean.Discovery.LinearDisentanglement.Quantitative
