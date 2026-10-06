/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Rowspan
public import Causalean.Discovery.LinearDisentanglement.SigmaSolutions
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part1
public import Causalean.Mathlib.LinearAlgebra.Cholesky
public import Mathlib.Data.Real.StarOrdered

/-!
# Linear causal disentanglement: conditional unnormalized uniqueness, part 2

This second proof file turns the summed Gram-difference identity from
`Uniqueness_Part1` into a diagonal conjugation identity and then an orthogonal
change of coordinates. It provides the permutation-conjugation calculations and
signed Cholesky lemmas needed to read monomial structure from that orthogonality.

`Uniqueness_Part3` uses these tools in the model-specific geometric collapse and
extracts the order-preserving permutation. The overall route and final theorem are
summarized in `Uniqueness`.
-/

public section

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

/-! ### The summed diagonal-conjugation identity -/
/-- **(S1+R1) The SUM TRICK after transport.**  The summed transport identity cancels the
observational Gram term and leaves a diagonal conjugation. -/
theorem diagonal_conj_from_sum_trick (S S' : Solution d p K)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : S'.H = M * S.H)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    (kof : Fin d → Fin K) (hkof : ∀ n, S.target (kof n) = n)
    (σ : Equiv.Perm (Fin d)) (hσtarget : ∀ n, S'.target (kof n) = σ n) :
    M.transpose * Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2) * M
      = Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) := by
  have hunprimed := sum_latent_diff_unprimed S kof hkof
  have hprimed := sum_latent_diff_primed_reindexed S' kof σ hσtarget
  have htransport := sum_gram_diff_transport S S' hM hΘ0 hΘ kof
  have h0 : S.B0.transpose * S.B0
      = M.transpose * (S'.B0.transpose * S'.B0) * M := by
    refine gram_identity_conj S S' hM ?_
    simp only [Solution.Theta0, Matrix.mul_assoc] at hΘ0 ⊢
    exact hΘ0
  have hsub :
      Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) - S.B0.transpose * S.B0
        = M.transpose * Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2) * M
          - S.B0.transpose * S.B0 := by
    calc
      Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) - S.B0.transpose * S.B0
          = (∑ n, ((S.Bint (kof n)).transpose * S.Bint (kof n)
              - S.B0.transpose * S.B0)) := hunprimed.symm
      _ = M.transpose *
            (∑ n, ((S'.Bint (kof n)).transpose * S'.Bint (kof n)
              - S'.B0.transpose * S'.B0)) * M := htransport
      _ = M.transpose *
            (Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2)
              - S'.B0.transpose * S'.B0) * M := by rw [hprimed]
      _ = M.transpose * Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2) * M
          - S.B0.transpose * S.B0 := by
            rw [Matrix.mul_sub, Matrix.sub_mul, h0]
  exact (sub_left_inj.mp hsub).symm

/-! ### (S2) Orthogonalizing the change-of-basis from a diagonal conjugation identity

If `Mᵀ diag(d') M = diag(d)` with `d, d' > 0`, then `O := diag(√d') M diag(1/√d)` is
orthogonal (`Oᵀ O = 1`).  This is the algebraic step turning the diagonalized SUM TRICK output
into an orthogonality statement on a *rescaled* `M`. -/

/-- **(S2) Diagonal conjugation ⟹ orthogonal rescaling.**  From `Mᵀ diag(d') M = diag(d)` with
`d, d'` strictly positive, the matrix `O = diag(fun i => √(d' i)) * M * diag(fun i => (√(d i))⁻¹)`
is orthogonal: `Oᵀ O = 1`. -/
theorem orthogonal_of_diag_conj {q : ℕ} {M : Matrix (Fin q) (Fin q) ℝ} {dv dv' : Fin q → ℝ}
    (hd : ∀ i, 0 < dv i) (hd' : ∀ i, 0 < dv' i)
    (hconj : M.transpose * Matrix.diagonal dv' * M = Matrix.diagonal dv) :
    (Matrix.diagonal (fun i => Real.sqrt (dv' i)) * M
        * Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹)).transpose
      * (Matrix.diagonal (fun i => Real.sqrt (dv' i)) * M
        * Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹)) = 1 := by
  -- `diag(√d')ᵀ diag(√d') = diag(d')` and `diag(1/√d) diag(d) diag(1/√d) = 1`.
  have hsqrt' : Matrix.diagonal (fun i => Real.sqrt (dv' i)) *
      Matrix.diagonal (fun i => Real.sqrt (dv' i)) = Matrix.diagonal dv' := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    exact Real.mul_self_sqrt (le_of_lt (hd' i))
  have hdpos : ∀ i, Real.sqrt (dv i) ≠ 0 := fun i => (Real.sqrt_pos.mpr (hd i)).ne'
  have hkill : Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹) * Matrix.diagonal dv
      * Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (Real.sqrt (dv i))⁻¹ * dv i * (Real.sqrt (dv i))⁻¹)
        = (fun _ => (1 : ℝ)) from ?_, Matrix.diagonal_one]
    funext i
    have hsq : Real.sqrt (dv i) * Real.sqrt (dv i) = dv i :=
      Real.mul_self_sqrt (le_of_lt (hd i))
    have : (Real.sqrt (dv i))⁻¹ * dv i * (Real.sqrt (dv i))⁻¹
        = (Real.sqrt (dv i))⁻¹ * (Real.sqrt (dv i) * Real.sqrt (dv i)) * (Real.sqrt (dv i))⁻¹ := by
      rw [hsq]
    rw [this]
    field_simp
    rw [div_self (hdpos i)]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.diagonal_transpose]
  -- Regroup everything right-associated, insert `D₁ D₁ = diag(d')`, then `Mᵀ diag(d') M = diag(d)`.
  -- Target: D₂ (Mᵀ (D₁ D₁) M) D₂ = D₂ (Mᵀ diag(d') M) D₂ = D₂ diag(d) D₂ = 1.
  have key : Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹)
        * (M.transpose * Matrix.diagonal dv' * M)
        * Matrix.diagonal (fun i => (Real.sqrt (dv i))⁻¹) = 1 := by
    rw [hconj]; exact hkill
  -- Normalize `key` to right-associated form, insert `diag(d') = D₁ D₁`, finish.
  have key' := key
  simp only [Matrix.mul_assoc] at key' ⊢
  rw [← hsqrt'] at key'
  simp only [Matrix.mul_assoc] at key'
  exact key'

/-! ### (L4) Orthogonal correctness — the geometric core

This is the geometric heart of the paper (`prop:orthogonal-correctness`).  After (L1)–(L3)
the change-of-basis `M` is invertible, `H' = M H`, and the **SUM TRICK** plus orthogonalization
build an orthogonal `O = diag(√d')·M·diag(√d⁻¹)`.  A decreasing topological-order induction on
the rows of `O` (support `⊆ Pa(n)` from `central_rank2_eq`, parent-rows eliminated by
orthogonality, unit norm) shows each row of `O` is `± eₙ`, so `O` is a signed permutation and
`M = diagonal μ · permMat σ` with `μ` nonzero.  The per-context relations then follow by a
signed-Cholesky read-off, whose only graph-theoretic input — the σ-triangularity
`S'.B₀ (σ a)(σ b) = 0` for `b < a` — is itself read off cleanly from the `(b,a)` entry of
`central_rank2_eq` (no extra induction).  `orthogonal_collapse` adds the
order-preservation `InSG σ`. -/

/-- `M = diagonal μ permMat σ` with nonzero `μ` has explicit inverse
`M⁻¹ = (permMat σ)ᵀ diagonal μ⁻¹`. -/
private theorem diagPerm_mul_inv (σ : Equiv.Perm (Fin d)) {μ : Fin d → ℝ}
    (hμ : ∀ i, μ i ≠ 0) :
    (Matrix.diagonal μ * permMat σ)
        * ((permMat σ).transpose * Matrix.diagonal (fun i => (μ i)⁻¹)) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permMat σ), permMat_mul_transpose, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal,
    show (fun i => μ i * (μ i)⁻¹) = (fun _ => (1 : ℝ)) from
      funext (fun i => mul_inv_cancel₀ (hμ i)), Matrix.diagonal_one]

/-- **Signed conjugation read-off.**  Given `M = diagonal μ permMat σ` and
`B' M = diagonal ν permMat σ B`, recover
`B' = diagonal ν permMat σ B (permMat σ)ᵀ diagonal μ⁻¹`. -/
theorem conj_readoff {σ : Equiv.Perm (Fin d)} {μ ν : Fin d → ℝ} (hμ : ∀ i, μ i ≠ 0)
    {M B B' : Matrix (Fin d) (Fin d) ℝ}
    (hMeq : M = Matrix.diagonal μ * permMat σ)
    (hrel : B' * M = Matrix.diagonal ν * permMat σ * B) :
    B' = Matrix.diagonal ν * permMat σ * B * (permMat σ).transpose
        * Matrix.diagonal (fun i => (μ i)⁻¹) := by
  have hMinv : M * ((permMat σ).transpose * Matrix.diagonal (fun i => (μ i)⁻¹)) = 1 := by
    rw [hMeq]; exact diagPerm_mul_inv σ hμ
  have hMU : M⁻¹ = (permMat σ).transpose * Matrix.diagonal (fun i => (μ i)⁻¹) :=
    Matrix.inv_eq_right_inv hMinv
  have hMMinv : M * M⁻¹ = 1 := by
    have hu : IsUnit M := IsUnit.of_mul_eq_one _ hMinv
    exact Matrix.mul_nonsing_inv M (by rwa [Matrix.isUnit_iff_isUnit_det] at hu)
  have hsplit : B' = (B' * M) * M⁻¹ := by rw [Matrix.mul_assoc, hMMinv, Matrix.mul_one]
  rw [hsplit, hrel, hMU]
  simp only [Matrix.mul_assoc]

/-- `(permMat σ) a c = 1` iff `c = σ.symm a`, else `0` (column read-off of `permMat`). -/
theorem permMat_apply_symm (σ : Equiv.Perm (Fin d)) (a c : Fin d) :
    permMat σ a c = if c = σ.symm a then (1 : ℝ) else 0 := by
  simp only [permMat, Matrix.of_apply]
  by_cases h : c = σ.symm a
  · subst h; simp [Equiv.apply_symm_apply]
  · rw [if_neg h, if_neg]
    exact fun hac => h (by rw [hac, Equiv.symm_apply_apply])

/-- **Permutation conjugation entry.**
`(permMat σ * X * (permMat σ)ᵀ) a b = X (σ.symm a) (σ.symm b)`:
conjugating `X` by `permMat σ` relabels rows and columns by `σ.symm`. -/
theorem permMat_conj_apply (σ : Equiv.Perm (Fin d)) (X : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d) :
    (permMat σ * X * (permMat σ).transpose) a b = X (σ.symm a) (σ.symm b) := by
  rw [Matrix.mul_apply]
  have hstep : ∀ c, (permMat σ * X) a c = X (σ.symm a) c := by
    intro c
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (σ.symm a)]
    · rw [permMat_apply_symm, if_pos rfl, one_mul]
    · intro x _ hx; rw [permMat_apply_symm, if_neg hx, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hstep, Matrix.transpose_apply, permMat_apply_symm]
  rw [Finset.sum_eq_single (σ.symm b)]
  · rw [if_pos rfl, mul_one]
  · intro x _ hx; rw [if_neg hx, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `(permMat σ)ᵀ = permMat σ⁻¹`: the transpose of a permutation matrix is the matrix of
the inverse permutation. -/
private theorem permMat_transpose_eq (σ : Equiv.Perm (Fin d)) :
    (permMat σ).transpose = permMat σ⁻¹ := by
  ext i j
  simp only [Matrix.transpose_apply, permMat, Matrix.of_apply]
  by_cases h : j = σ i
  · subst h; simp [Equiv.symm_apply_apply]
  · rw [if_neg h, if_neg (fun hc => h (by rw [hc]; simp))]

/-- **Inverse-permutation conjugation entry.**
`((permMat σ)ᵀ * X * permMat σ) a b = X (σ a) (σ b)`: conjugating `X` by `(permMat σ)ᵀ`
relabels rows and columns by `σ`. -/
theorem permMat_conj_apply' (σ : Equiv.Perm (Fin d)) (X : Matrix (Fin d) (Fin d) ℝ)
    (a b : Fin d) :
    ((permMat σ).transpose * X * permMat σ) a b = X (σ a) (σ b) := by
  rw [permMat_transpose_eq]
  have h2 : permMat σ = (permMat σ⁻¹).transpose := by
    rw [permMat_transpose_eq]; simp
  rw [h2, permMat_conj_apply σ⁻¹ X a b]
  rfl

/-- **Diagonal-through-permutation.**  `permMat σ * diagonal s = diagonal (s ∘ σ.symm) * permMat σ`:
moving a diagonal rescaling across a permutation matrix relabels its entries by `σ.symm`. -/
theorem permMat_mul_diagonal (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) :
    permMat σ * Matrix.diagonal s = Matrix.diagonal (fun i => s (σ.symm i)) * permMat σ := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, permMat_apply_symm]
  by_cases h : b = σ.symm a
  · subst h; rw [if_pos rfl]; simp
  · rw [if_neg h, mul_zero, zero_mul]

/-- **Orthogonal upper-triangular ⟹ signed diagonal.**  An orthogonal (`Wᵀ W = 1`)
upper-triangular matrix is diagonal with `±1` entries.  This is the signed analogue of
`orthogonal_upperTri_pos_diag_eq_one` (which assumed a positive diagonal and concluded `W = 1`):
without the sign condition the diagonal entries are pinned only up to sign. -/
theorem orthogonal_upperTri_signed_diag {q : ℕ} {W : Matrix (Fin q) (Fin q) ℝ}
    (hortho : Wᵀ * W = 1) (hupp : ∀ i j, j < i → W i j = 0) :
    (∀ i j, i ≠ j → W i j = 0) ∧ (∀ i, W i i = 1 ∨ W i i = -1) := by
  classical
  haveI : Invertible W := invertibleOfLeftInverse _ _ hortho
  have hinv : W⁻¹ = Wᵀ := Matrix.inv_eq_left_inv hortho
  have hWupp : W.BlockTriangular id := hupp
  have hWTupp : (Wᵀ).BlockTriangular id :=
    hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hWupp
  have hWTlow : (Wᵀ).BlockTriangular OrderDual.toDual := hWupp.transpose
  -- `Wᵀ` is both upper- and lower-triangular, hence diagonal.
  have hWTdiag : ∀ i j, i ≠ j → (Wᵀ) i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hWTlow (by simpa using h)
    · exact hWTupp (by simpa using h)
  -- Off-diagonal entries of `W` vanish (transpose of `Wᵀ`'s vanishing entries).
  have hWdiag : ∀ i j, i ≠ j → W i j = 0 := by
    intro i j hij
    have : (Wᵀ) j i = 0 := hWTdiag j i (Ne.symm hij)
    rwa [Matrix.transpose_apply] at this
  refine ⟨hWdiag, ?_⟩
  -- Diagonal entries square to one.
  intro i
  have hcol := congrFun (congrFun hortho i) i
  rw [Matrix.one_apply_eq, Matrix.mul_apply] at hcol
  simp only [Matrix.transpose_apply] at hcol
  rw [Finset.sum_eq_single i] at hcol
  · rw [← sq] at hcol; exact sq_eq_one_iff.mp hcol
  · intro l _ hli
    have : W l i = 0 := hWdiag l i hli
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- [An upper-triangular Gram factor is unique up to row signs](goal), making the remaining
ambiguity explicit for [matrices `P,B` in dimension `q`](hyp:q,P,B). This uses
[upper-triangularity of both factors](hyp:hPu,hBu), [positive diagonal for the reference](hyp:hBp),
and [equality of their Gram matrices](hyp:hgram).

**Signed Cholesky read-off.**  If `Pᵀ P = Bᵀ B` with `P` upper-triangular and `B`
upper-triangular with strictly positive diagonal, then `P = diagonal s · B` for a unique
`±1`-valued sign vector `s`, with `s i · B i i = P i i`.  This generalizes `cholesky_unique`
(both factors positive-diagonal) to the case where only one factor's diagonal sign is fixed. -/
theorem signed_cholesky {q : ℕ} {P B : Matrix (Fin q) (Fin q) ℝ}
    (hPu : ∀ i j, j < i → P i j = 0) (hBu : ∀ i j, j < i → B i j = 0)
    (hBp : ∀ i, 0 < B i i) (hgram : Pᵀ * P = Bᵀ * B) :
    ∃ s : Fin q → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      (∀ i, s i * B i i = P i i) ∧ P = Matrix.diagonal s * B := by
  classical
  have hBu' : B.BlockTriangular id := hBu
  have hBdet : (0 : ℝ) < B.det := by
    rw [Matrix.det_of_upperTriangular hBu']; exact Finset.prod_pos (fun i _ => hBp i)
  haveI : Invertible B := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hBdet.ne')
  have hBinvU : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hBu'
  have hBinv_diag : ∀ i, B⁻¹ i i = (B i i)⁻¹ := by
    intro i
    have hmul : (B⁻¹ * B) i i = 1 := by rw [Matrix.inv_mul_of_invertible]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at hmul
    · field_simp [(hBp i).ne'] at hmul ⊢; linarith [hmul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [hBinvU (by simpa using hk), zero_mul]
      · rw [hBu k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- `W := P * B⁻¹` is orthogonal and upper-triangular.
  set W : Matrix (Fin q) (Fin q) ℝ := P * B⁻¹ with hW
  have hWupp : ∀ i j, j < i → W i j = 0 := (Matrix.BlockTriangular.mul (hPu) hBinvU)
  have hWortho : Wᵀ * W = 1 := by
    rw [hW, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ P, hgram,
      Matrix.mul_assoc Bᵀ, Matrix.mul_inv_of_invertible, Matrix.mul_one,
      Matrix.transpose_nonsing_inv, Matrix.inv_mul_of_invertible]
  obtain ⟨hWoff, hWsign⟩ := orthogonal_upperTri_signed_diag hWortho hWupp
  -- The sign vector is the diagonal of `W`.
  refine ⟨fun i => W i i, hWsign, ?_, ?_⟩
  · -- `W i i · B i i = P i i`.
    intro i
    change W i i * B i i = P i i
    have hWii : W i i = P i i * (B i i)⁻¹ := by
      rw [hW, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [hBinv_diag i]
      · intro k _ hki
        rcases lt_or_gt_of_ne hki with hk | hk
        · rw [hPu i k (by simpa using hk), zero_mul]
        · rw [hBinvU (by simpa using hk), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hWii]
    field_simp [(hBp i).ne']
  · -- `P = diagonal (W ·ᵢᵢ) * B`, since `W = diagonal` and `P = W B`.
    have hWdiagonal : W = Matrix.diagonal (fun i => W i i) := by
      ext a b
      by_cases hab : a = b
      · subst hab; rw [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hab, hWoff a b hab]
    have hPWB : P = W * B := by
      rw [hW, Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]
    rw [hPWB]
    conv_lhs => rw [hWdiagonal]

end Causalean.Discovery.LinearDisentanglement
