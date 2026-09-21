/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Rowspan
public import Causalean.Discovery.LinearDisentanglement.SigmaSolutions
public import Causalean.Mathlib.LinearAlgebra.Cholesky
public import Mathlib.Data.Real.StarOrdered

/-!
# Linear causal disentanglement: conditional unnormalized uniqueness, part 1

This first proof file develops the algebraic infrastructure for conditional
unnormalized uniqueness. It proves invertibility of the structural matrices and
the latent Gram matrix, obtains the change of basis `H' = M H`, transports the
observable precision equalities to latent Gram identities, and rewrites them as
rank-two identities.

It also supplies the target read-off lemmas and the summed Gram-difference identity
used by `Uniqueness_Part2`, which continues with diagonal conjugation and
orthogonalization. The overall route and final theorem are summarized in
`Uniqueness`.
-/

@[expose] public section

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

/-! ### General matrix helpers (route-agnostic) -/
/-- **(L3) Gram ⟹ orthogonal.**  If `XᵀX = YᵀY` with `X`, `Y` invertible, then the
transition matrix `O = Y X⁻¹` is orthogonal: `Oᵀ O = 1`.  This is the algebraic step that
turns the equality of Gram matrices `BᵀB = (B' M)ᵀ(B' M)` into an orthogonality statement
about `O = B' M B⁻¹`. -/
theorem gram_to_orthogonal {q : ℕ} {X Y : Matrix (Fin q) (Fin q) ℝ}
    [Invertible X] [Invertible Y] (h : Xᵀ * X = Yᵀ * Y) :
    (Y * X⁻¹)ᵀ * (Y * X⁻¹) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Yᵀ Y, ← h, Matrix.mul_assoc Xᵀ,
    Matrix.mul_inv_of_invertible, Matrix.mul_one, Matrix.transpose_nonsing_inv,
    Matrix.inv_mul_of_invertible]

/-! ### Invertibility of the structural matrices

`B0` and every `Bint k` are upper triangular with strictly positive diagonal, hence have
positive determinant and are invertible. -/

/-- `B0` is upper triangular in the `BlockTriangular id` sense. -/
theorem B0_blockTriangular (S : Solution d p K) : S.B0.BlockTriangular id := S.hB0up

/-- `Bint k` is upper triangular: the perfect intervention only rewrites the target row
(which keeps the diagonal at `λₖ` and zeroes the strictly-lower entries already zero in
`B0`). -/
theorem Bint_blockTriangular (S : Solution d p K) (k : Fin K) :
    (S.Bint k).BlockTriangular id := by
  intro i j hji
  simp only [id_eq] at hji
  rw [S.hInt k, Matrix.add_apply, S.hB0up i j hji, zero_add, Matrix.vecMulVec_apply]
  by_cases hi : i = S.target k
  · -- target row: off-diagonal lower entries vanish since `j < i = target k`
    have hjlt : j < S.target k := hi ▸ hji
    have hjne : j ≠ S.target k := ne_of_lt hjlt
    rw [S.hB0up (S.target k) j hjlt]
    simp [stdVec, Pi.single_eq_of_ne hjne]
  · simp [stdVec, Pi.single_eq_of_ne hi]

/-- `det B0 = ∏ᵢ (B0)ᵢᵢ > 0`. -/
theorem B0_det_pos (S : Solution d p K) : 0 < S.B0.det := by
  rw [Matrix.det_of_upperTriangular (B0_blockTriangular S)]
  exact Finset.prod_pos (fun i _ => S.hB0pos i)

/-- `(Bint k)ᵢᵢ = (B0)ᵢᵢ` off the target, and `= λₖ` on the target — in both cases
strictly positive. -/
theorem Bint_diag_pos (S : Solution d p K) (k : Fin K) (i : Fin d) : 0 < S.Bint k i i := by
  rw [S.hInt k, Matrix.add_apply, Matrix.vecMulVec_apply]
  by_cases hi : i = S.target k
  · rw [hi]
    simp only [stdVec, Pi.single_eq_same, one_mul]
    have : S.B0 (S.target k) (S.target k)
        + (S.lam k * 1 - S.B0 (S.target k) (S.target k)) = S.lam k := by ring
    rw [this]; exact S.hlam k
  · simp only [stdVec, Pi.single_eq_of_ne hi, zero_mul, add_zero]
    exact S.hB0pos i

/-- `det (Bint k) = ∏ᵢ (Bint k)ᵢᵢ > 0`. -/
theorem Bint_det_pos (S : Solution d p K) (k : Fin K) : 0 < (S.Bint k).det := by
  rw [Matrix.det_of_upperTriangular (Bint_blockTriangular S k)]
  exact Finset.prod_pos (fun i _ => Bint_diag_pos S k i)

/-- [The observational structural matrix is invertible](goal), so baseline latent equations can be
solved for every [linear disentanglement solution and its latent, observed, and context
dimensions](hyp:d,p,K,S); the [certificate comes from its positive determinant](step:1).

`B0` is invertible. -/
noncomputable instance B0_invertible (S : Solution d p K) : Invertible S.B0 :=
  S.B0.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr (B0_det_pos S).ne')

/-- [Every interventional structural matrix is invertible](goal), so the perturbed latent equations
remain solvable in [context `k`](hyp:k) of any [linear disentanglement solution and its latent,
observed, and context dimensions](hyp:d,p,K,S); the [certificate comes from its positive
determinant](step:1).

`Bint k` is invertible. -/
noncomputable instance Bint_invertible (S : Solution d p K) (k : Fin K) :
    Invertible (S.Bint k) :=
  (S.Bint k).invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr (Bint_det_pos S k).ne')

/-! ### The latent Gram matrix `H Hᵀ` is positive definite, hence invertible -/

/-- `vecMul · H` is injective (full row rank of `H`). -/
theorem vecMul_H_injective (S : Solution d p K) :
    Function.Injective (fun v => Matrix.vecMul v S.H) :=
  Matrix.vecMul_injective_iff.mpr (by rw [Matrix.row_def]; exact S.hH)

/-- The latent Gram matrix `H Hᵀ` is positive definite. -/
theorem HHt_posDef (S : Solution d p K) : (S.H * S.H.transpose).PosDef := by
  have := Matrix.PosDef.mul_conjTranspose_self S.H (vecMul_H_injective S)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- [The latent Gram matrix of the mixing pseudoinverse is invertible](goal), allowing observed
relations to be pulled back to latent space for any [linear disentanglement solution and its
dimensions](hyp:d,p,K,S); the [certificate follows from positive definiteness](step:1).

`H Hᵀ` is invertible. -/
noncomputable instance HHt_invertible (S : Solution d p K) :
    Invertible (S.H * S.H.transpose) :=
  (S.H * S.H.transpose).invertibleOfIsUnitDet
    ((Matrix.isUnit_iff_isUnit_det _).mp (HHt_posDef S).isUnit)

/-- [The observational structural-loading Gram matrix is invertible](goal), enabling precision
identities to recover latent transformations for any [linear disentanglement solution and its
dimensions](hyp:d,p,K,S); its [certificate composes the component inverses](step:1).

The Gram matrix `(B₀H)(B₀H)ᵀ = B₀ (H Hᵀ) B₀ᵀ` is invertible (product of invertibles). -/
noncomputable instance B0H_gram_invertible (S : Solution d p K) :
    Invertible ((S.B0 * S.H) * (S.B0 * S.H).transpose) := by
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc S.B0]
  exact ((B0_invertible S).mul (HHt_invertible S)).mul
    (inferInstanceAs (Invertible S.B0.transpose))

/-- `R := Hᵀ (H Hᵀ)⁻¹` is a right inverse of `H`: `H R = 1`. -/
theorem H_mul_rightInv (S : Solution d p K) :
    S.H * (S.H.transpose * (S.H * S.H.transpose)⁻¹) = 1 := by
  rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible]

/-- `L := (H Hᵀ)⁻¹ H` is a left inverse of `Hᵀ`: `L Hᵀ = 1`. -/
theorem leftInv_mul_Ht (S : Solution d p K) :
    ((S.H * S.H.transpose)⁻¹ * S.H) * S.H.transpose = 1 := by
  rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible]

/-! ### (L1) Recovery of the mixing change-of-basis `M`

From `Θ₀ = Θ₀'`, the two mixing matrices `H`, `H'` have the same rowspace, so
`H' = M H` for an invertible `M`.  The cleanest derivation avoids any dimension count:
writing `C = B₀ H` (full row rank, `Θ₀ = Cᵀ C`), the Gram `C Cᵀ` is invertible, so
`H = B₀⁻¹ (C Cᵀ)⁻¹ C · Θ₀`, i.e. every row of `H` is an explicit `vecMul` of `Θ₀`.
Applied to the primed system and substituting `Θ₀' = Θ₀`, this exhibits `H' = M H`. -/

/-- **The recovery identity `H = W Θ₀`.**  With `C = B₀ H` and `Θ₀ = Cᵀ C`, the matrix
`W = B₀⁻¹ (C Cᵀ)⁻¹ C` satisfies `W Θ₀ = H`. -/
theorem H_eq_recover_mul_Theta0 (S : Solution d p K) :
    (S.B0⁻¹ * ((S.B0 * S.H) * (S.B0 * S.H).transpose)⁻¹ * (S.B0 * S.H)) * S.Theta0 = S.H := by
  have hΘ : S.Theta0 = (S.B0 * S.H).transpose * (S.B0 * S.H) := by
    simp only [Solution.Theta0, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hΘ]
  set G := (S.B0 * S.H) * (S.B0 * S.H).transpose with hG
  rw [Matrix.mul_assoc (S.B0⁻¹ * G⁻¹), ← Matrix.mul_assoc (S.B0 * S.H), ← hG,
    ← Matrix.mul_assoc, Matrix.mul_assoc S.B0⁻¹, Matrix.inv_mul_of_invertible, Matrix.mul_one,
    ← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]

/-- **(L1) The change-of-basis matrix.**  There is an invertible `M` with `H' = M H`.
`M` is built from the recovery identity for `H'` (`H' = W' Θ₀'`) by substituting
`Θ₀' = Θ₀ = Hᵀ B₀ᵀ B₀ H`, giving `H' = (W' Hᵀ B₀ᵀ B₀) H`.  Invertibility follows from
the symmetric matrix `N` with `H = N H'` by right-cancelling the full-row-rank `H`/`H'`. -/
theorem exists_change_of_basis (S S' : Solution d p K) (hΘ0 : S.Theta0 = S'.Theta0) :
    ∃ M : Matrix (Fin d) (Fin d) ℝ, IsUnit M ∧ S'.H = M * S.H := by
  -- `M := W' Hᵀ B₀ᵀ B₀` from `H' = W' Θ₀' = W' Θ₀ = W' (Hᵀ B₀ᵀ B₀ H)`.
  set W' := S'.B0⁻¹ * ((S'.B0 * S'.H) * (S'.B0 * S'.H).transpose)⁻¹ * (S'.B0 * S'.H) with hW'
  set N' := S.B0⁻¹ * ((S.B0 * S.H) * (S.B0 * S.H).transpose)⁻¹ * (S.B0 * S.H) with hN'
  have hH' : S'.H = (W' * S.H.transpose * S.B0.transpose * S.B0) * S.H := by
    have h1 : W' * S'.Theta0 = S'.H := H_eq_recover_mul_Theta0 S'
    rw [← hΘ0, Solution.Theta0] at h1
    rw [← h1]
    simp only [Matrix.mul_assoc]
  have hH : S.H = (N' * S'.H.transpose * S'.B0.transpose * S'.B0) * S'.H := by
    have h1 : N' * S.Theta0 = S.H := H_eq_recover_mul_Theta0 S
    rw [hΘ0, Solution.Theta0] at h1
    rw [← h1]
    simp only [Matrix.mul_assoc]
  set M := W' * S.H.transpose * S.B0.transpose * S.B0 with hM
  set N := N' * S'.H.transpose * S'.B0.transpose * S'.B0 with hN
  refine ⟨M, ?_, hH'⟩
  -- `M` is a unit: `M N = 1` via right-cancellation by the full-row-rank `H`.
  have hMN : M * N = 1 := by
    have hcomp : (M * N) * S'.H = (1 : Matrix (Fin d) (Fin d) ℝ) * S'.H := by
      rw [Matrix.mul_assoc, ← hH, ← hH', Matrix.one_mul]
    -- right-cancel `H'` (it has right inverse `H'ᵀ (H' H'ᵀ)⁻¹`).
    have hrcancel : ∀ A B : Matrix (Fin d) (Fin d) ℝ, A * S'.H = B * S'.H → A = B := by
      intro A B hAB
      have h2 := congrArg (fun X => X * (S'.H.transpose * (S'.H * S'.H.transpose)⁻¹)) hAB
      simp only [Matrix.mul_assoc] at h2
      rwa [H_mul_rightInv S', Matrix.mul_one, Matrix.mul_one] at h2
    exact hrcancel _ _ hcomp
  exact IsUnit.of_mul_eq_one N hMN

/-! ### (L2) Cancellation: the `d×d` Gram identity in each context

From `Θₖ = Θₖ'` and `H' = M H`, cancelling `Hᵀ` on the left and `H` on the right gives
the `d × d` identity `BₖᵀBₖ = (B'ₖ M)ᵀ (B'ₖ M)`. -/

/-- Left-cancel `Hᵀ` and right-cancel `H` in `Hᵀ X H = Hᵀ Y H`.  `H` has full row rank,
so `Hᵀ` has a left inverse and `H` a right inverse. -/
theorem cancel_Ht_H (S : Solution d p K) {X Y : Matrix (Fin d) (Fin d) ℝ}
    (h : S.H.transpose * X * S.H = S.H.transpose * Y * S.H) : X = Y := by
  set R := S.H.transpose * (S.H * S.H.transpose)⁻¹ with hR
  set L := (S.H * S.H.transpose)⁻¹ * S.H with hL
  -- right-cancel `H`: multiply by `R` on the right.
  have hr : S.H.transpose * X = S.H.transpose * Y := by
    have h2 := congrArg (fun Z => Z * R) h
    simp only [Matrix.mul_assoc] at h2
    rwa [H_mul_rightInv S, Matrix.mul_one, Matrix.mul_one] at h2
  -- left-cancel `Hᵀ`: multiply by `L` on the left.
  have h3 := congrArg (fun Z => L * Z) hr
  simp only [← Matrix.mul_assoc] at h3
  rwa [leftInv_mul_Ht S, Matrix.one_mul, Matrix.one_mul] at h3

/-- **(L2) The per-context Gram identity.**  Given `H' = M H` and `Θₖ = Θₖ'` for the
observational (`B₀`/`B'₀`) and interventional (`Bₖ`/`B'ₖ`) matrices, the `d × d` Gram
identity `BᵀB = (B' M)ᵀ (B' M)` holds. -/
theorem gram_identity (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) {B B' : Matrix (Fin d) (Fin d) ℝ}
    (hΘ : S.H.transpose * B.transpose * B * S.H
      = S'.H.transpose * B'.transpose * B' * S'.H) :
    B.transpose * B = (B' * M).transpose * (B' * M) := by
  apply cancel_Ht_H S
  have e1 : S.H.transpose * (B.transpose * B) * S.H
      = S'.H.transpose * B'.transpose * B' * S'.H := by
    rw [← hΘ]; simp only [Matrix.mul_assoc]
  rw [e1, hM]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-! ### Latent-level structural lemmas (sub-lemmas (A)–(D) of the roadmap)

These work entirely with `d × d` matrices and feed the orthogonal-correctness core.  They
isolate the **algebraic** content of perfect single-node interventions: the rank-one
perturbation `Bₖ − B₀ = e_{iₖ} cₖᵀ`, the orthogonality of the transition factor
`Oₖ = B'ₖ M Bₖ⁻¹`, and (the part that survives into the conclusion) the read-off of the
permuted intervention targets `i'ₖ = σ(iₖ)`. -/

/-- [The perfect-intervention perturbation row](goal) isolates how [context `k`](hyp:k) replaces the
target equation of [solution `S`](hyp:S), with [latent dimension `d`](hyp:d), [observed dimension
`p`](hyp:p), and [intervention count `K`](hyp:K). -/
def cvec (S : Solution d p K) (k : Fin K) : Fin d → ℝ :=
  fun j => S.lam k * stdVec d (S.target k) j - S.B0 (S.target k) j

/-- **Rank-one perturbation.**  `Bₖ − B₀ = e_{iₖ} cₖᵀ` (`Matrix.vecMulVec`): a perfect
single-node intervention rewrites only the target row of `B₀`. -/
theorem Bint_sub_B0 (S : Solution d p K) (k : Fin K) :
    S.Bint k - S.B0 = Matrix.vecMulVec (stdVec d (S.target k)) (cvec S k) := by
  rw [S.hInt k, add_sub_cancel_left]; rfl

/-- **(C, target-row form / sub-lemma (B)).**  The perturbation row is non-degenerate
exactly when the intervention changes the precision matrix.  Under `Θₖ ≠ Θ₀`, `cₖ ≠ 0`
(equivalently `Bₖ ≠ B₀`): if `cₖ = 0` then `Bₖ = B₀`, hence `Θₖ = Θ₀`. -/
theorem cvec_ne_zero (S : Solution d p K) (k : Fin K) (hk : S.Theta k ≠ S.Theta0) :
    cvec S k ≠ 0 := by
  intro hc
  apply hk
  have hBeq : S.Bint k = S.B0 := by
    have := Bint_sub_B0 S k
    rw [hc, Matrix.vecMulVec_zero] at this
    exact sub_eq_zero.mp this
  rw [Solution.Theta, Solution.Theta0, hBeq]

/-- **(B) Target row of `Bₖ`.**  `(Bₖ)ᵀ *ᵥ e_{iₖ} = λₖ • e_{iₖ}`: the `iₖ`-th row of a
perfect-intervention matrix is `λₖ e_{iₖ}ᵀ` (the intervention zeroes the parent entries and
sets the diagonal to `λₖ`). -/
theorem Bint_transpose_mulVec_target (S : Solution d p K) (k : Fin K) :
    (S.Bint k).transpose *ᵥ stdVec d (S.target k) = (S.lam k) • stdVec d (S.target k) := by
  funext j
  rw [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
  simp only [stdVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single (S.target k)]
  · by_cases hj : j = S.target k
    · rw [hj, S.hInt k]; simp [Matrix.add_apply, Matrix.vecMulVec_apply, stdVec]
    · simp only [if_neg hj, mul_zero]
      rw [S.hInt k]; simp [Matrix.add_apply, Matrix.vecMulVec_apply, stdVec, hj]
  · intro x _ hx; simp [if_neg hx]
  · intro hx; exact absurd (Finset.mem_univ _) hx

/-- **(C) Latent key identity.**  At the `d × d` (latent) level the difference of Gram
matrices is a difference of two rank-one (outer-product) matrices:
`BₖᵀBₖ − B₀ᵀB₀ = λₖ² (e_{iₖ} e_{iₖ}ᵀ) − wₖ wₖᵀ` where `wₖ = B₀ᵀ *ᵥ e_{iₖ}` is the `iₖ`-th
row of `B₀` (supported on `Pa(iₖ)`).  This is the latent analogue of `key_identity`, and
the structural engine of the orthogonal-correctness core. -/
theorem latent_key_identity (S : Solution d p K) (k : Fin K) :
    (S.Bint k).transpose * S.Bint k - S.B0.transpose * S.B0
      = (S.lam k) ^ 2 • Matrix.vecMulVec (stdVec d (S.target k)) (stdVec d (S.target k))
        - Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d (S.target k))
            (S.B0.transpose *ᵥ stdVec d (S.target k)) := by
  -- Off-target rows of `Bₖ` agree with `B₀`, so the rank-one decompositions cancel except
  -- in the target row (mirrors the latent step inside `key_identity`).
  set i := S.target k with hi
  have hrow : ∀ l : Fin d, l ≠ i →
      ((S.Bint k).transpose *ᵥ stdVec d l) = (S.B0.transpose *ᵥ stdVec d l) := by
    intro l hl
    have hl' : l ≠ S.target k := hi ▸ hl
    funext a
    rw [S.hInt k]
    simp only [stdVec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply,
      Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hl', zero_mul, add_zero]
  rw [fact_transpose_mul (S.Bint k), fact_transpose_mul S.B0,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hcancel :
      (∑ l ∈ Finset.univ.erase i, Matrix.vecMulVec
          ((S.Bint k).transpose *ᵥ stdVec d l) ((S.Bint k).transpose *ᵥ stdVec d l))
        = ∑ l ∈ Finset.univ.erase i,
          Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d l) (S.B0.transpose *ᵥ stdVec d l) := by
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [hrow l (Finset.ne_of_mem_erase hl)]
  rw [hcancel, Bint_transpose_mulVec_target, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec,
    smul_smul, ← pow_two]
  abel

/-- **(D) The transition factor is orthogonal.**  From the per-context Gram identity
`BₖᵀBₖ = (B'ₖ M)ᵀ(B'ₖ M)` and invertibility, `Oₖ = B'ₖ M Bₖ⁻¹` satisfies `Oₖᵀ Oₖ = 1`. -/
theorem transition_orthogonal (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) {B B' : Matrix (Fin d) (Fin d) ℝ} [Invertible B] [Invertible (B' * M)]
    (hΘ : S.H.transpose * B.transpose * B * S.H
      = S'.H.transpose * B'.transpose * B' * S'.H) :
    ((B' * M) * B⁻¹)ᵀ * ((B' * M) * B⁻¹) = 1 :=
  gram_to_orthogonal (gram_identity S S' hM hΘ)

/-! ### (R1) Latent Gram-difference transport

The per-context Gram identity (`gram_identity`) says `Bₖᵀ Bₖ = Mᵀ B'ₖᵀ B'ₖ M` for every
context (including `k = 0`).  Subtracting the observational equation gives the **latent
Gram-difference transport**: `Δₖ = Mᵀ Δ'ₖ M`, where `Δₖ = Bₖᵀ Bₖ − B₀ᵀ B₀` (and `Δ'ₖ`
likewise).  This is the algebraic content of (R1): the change-of-basis `M` conjugates the
primed Gram differences into the unprimed ones. -/

/-- The per-context Gram identity in the symmetric form `BᵀB = Mᵀ B'ᵀ B' M` (the conjugation
form of `gram_identity`). -/
theorem gram_identity_conj (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) {B B' : Matrix (Fin d) (Fin d) ℝ}
    (hΘ : S.H.transpose * B.transpose * B * S.H
      = S'.H.transpose * B'.transpose * B' * S'.H) :
    B.transpose * B = M.transpose * (B'.transpose * B') * M := by
  rw [gram_identity S S' hM hΘ, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **(R1) Latent Gram-difference transport.**  `Bₖᵀ Bₖ − B₀ᵀ B₀ = Mᵀ (B'ₖᵀ B'ₖ − B'₀ᵀ B'₀) M`.
Subtracting the observational conjugation identity from the `k`-th one. -/
theorem gram_diff_transport (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    (k : Fin K) :
    (S.Bint k).transpose * S.Bint k - S.B0.transpose * S.B0
      = M.transpose * ((S'.Bint k).transpose * S'.Bint k - (S'.B0).transpose * S'.B0) * M := by
  have hk : (S.Bint k).transpose * S.Bint k
      = M.transpose * ((S'.Bint k).transpose * S'.Bint k) * M := by
    refine gram_identity_conj S S' hM ?_
    have := hΘ k
    simp only [Solution.Theta, Matrix.mul_assoc] at this ⊢
    exact this
  have h0 : S.B0.transpose * S.B0
      = M.transpose * ((S'.B0).transpose * S'.B0) * M := by
    refine gram_identity_conj S S' hM ?_
    simp only [Solution.Theta0, Matrix.mul_assoc] at hΘ0 ⊢
    exact hΘ0
  rw [hk, h0, Matrix.mul_sub, Matrix.sub_mul]

/-- `Mᵀ (u vᵀ) M = (Mᵀ u)(Mᵀ v)ᵀ` (conjugation of a rank-one matrix by `Mᵀ · M`). -/
theorem conj_vecMulVec_transpose {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) (u v : Fin q → ℝ) :
    M.transpose * Matrix.vecMulVec u v * M
      = Matrix.vecMulVec (M.transpose *ᵥ u) (M.transpose *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose]

/-- [Equal observable precision families force the central rank-two latent identity](goal), which
equates intervention effects after change of basis. It compares [solutions `S,S'` and their
dimensions](hyp:d,p,K,S,S'), [latent transformation `M`](hyp:M), [the loading
relation](hyp:hM), [observational and interventional precision equality](hyp:hΘ0,hΘ), and
[selected context `k`](hyp:k).

**(R1+C) The central rank-≤2 equation.**  Combining the Gram-difference transport
`Δₖ = Mᵀ Δ'ₖ M` (`gram_diff_transport`) with the latent key identity (C) on both sides,
`Δₖ = λₖ²(eₖeₖᵀ) − wₖwₖᵀ` and `Δ'ₖ = λ'ₖ²(e'ₖe'ₖᵀ) − w'ₖw'ₖᵀ`, gives the rank-≤2 identity
in fully outer-product form, with the primed outer products transported by `Mᵀ`:
`λₖ²(eₖeₖᵀ) − wₖwₖᵀ = λ'ₖ²((Mᵀe'ₖ)(Mᵀe'ₖ)ᵀ) − (Mᵀw'ₖ)(Mᵀw'ₖ)ᵀ`. -/
theorem central_rank2_eq (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : S'.H = M * S.H) (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    (k : Fin K) :
    (S.lam k) ^ 2 • Matrix.vecMulVec (stdVec d (S.target k)) (stdVec d (S.target k))
        - Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d (S.target k))
            (S.B0.transpose *ᵥ stdVec d (S.target k))
      = (S'.lam k) ^ 2 • Matrix.vecMulVec (M.transpose *ᵥ stdVec d (S'.target k))
            (M.transpose *ᵥ stdVec d (S'.target k))
        - Matrix.vecMulVec (M.transpose *ᵥ (S'.B0.transpose *ᵥ stdVec d (S'.target k)))
            (M.transpose *ᵥ (S'.B0.transpose *ᵥ stdVec d (S'.target k))) := by
  have htrans := gram_diff_transport S S' hM hΘ0 hΘ k
  rw [latent_key_identity, latent_key_identity] at htrans
  rw [htrans, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    conj_vecMulVec_transpose, conj_vecMulVec_transpose]

/-- `Mᵀ *ᵥ eᵢ` is the `i`-th **row** of `M`, viewed as a vector: `(Mᵀ *ᵥ eᵢ) j = Mᵢⱼ`.
This is the bridge that turns the transported outer products of `central_rank2_eq` into
statements about the rows of `M`. -/
theorem transpose_mulVec_stdVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    M.transpose *ᵥ stdVec n i = (fun j => M i j) := by
  funext j
  rw [Matrix.mulVec_transpose, stdVec, Matrix.single_vecMul, one_smul, Matrix.row_apply]

/-- **(R3 ingredient) The `iₖ`-th row of `B₀` at a source.**  If `iₖ` is a *source* node
(no parents: `(B₀)_{iₖ,j} = 0` for every `j ≠ iₖ`), then `wₖ = B₀ᵀ *ᵥ e_{iₖ} = β e_{iₖ}`
with `β = (B₀)_{iₖ,iₖ} > 0`.  This collapses the latent key identity (C) to the rank-one
`Δₖ = (λₖ² − β²) e_{iₖ} e_{iₖ}ᵀ`, the base case of the monomial induction (R3): the
transported equation then forces the `i'ₖ`-th row of `M` to be a multiple of `e_{iₖ}`. -/
theorem B0_source_row (S : Solution d p K) (i : Fin d)
    (hsrc : ∀ j, j ≠ i → S.B0 i j = 0) :
    S.B0.transpose *ᵥ stdVec d i = (S.B0 i i) • stdVec d i := by
  funext j
  rw [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
  simp only [stdVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_mul]
    by_cases hj : j = i
    · subst hj; rw [Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne hj, mul_zero]; exact hsrc j hj
  · intro x _ hx; rw [Pi.single_eq_of_ne hx, zero_mul]
  · intro hx; exact absurd (Finset.mem_univ _) hx

/-! ### Reading off the permuted targets from the collapse (sub-lemma feeding the core)

If the orthogonal-correctness core has produced a single permutation `σ` and row-sign
diagonal `ν` with `B'ₖ M = diagonal ν permMat σ Bₖ` in every context (including `k = 0`),
then subtracting the observational equation isolates the rank-one rows and forces
`i'ₖ = σ(iₖ)`. -/

/-- `permMat σ *ᵥ eᵢ = e_{σ i}`: the permutation matrix sends the `i`-th basis vector to the
`σ(i)`-th. -/
theorem permMat_mulVec_stdVec (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    permMat σ *ᵥ stdVec d i = stdVec d (σ i) := by
  rw [stdVec, Matrix.mulVec_single_one]
  funext a
  simp only [permMat, Matrix.col_apply, Matrix.of_apply, stdVec, Pi.single_apply]

/-- A signed permutation matrix sends `eᵢ` to the signed basis vector
`ν (σ i) • e_{σ i}`. -/
theorem diag_permMat_mulVec_stdVec (σ : Equiv.Perm (Fin d)) (ν : Fin d → ℝ) (i : Fin d) :
    (Matrix.diagonal ν * permMat σ) *ᵥ stdVec d i =
      (ν (σ i)) • stdVec d (σ i) := by
  rw [← Matrix.mulVec_mulVec, permMat_mulVec_stdVec]
  funext a
  rw [Matrix.mulVec_diagonal]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases ha : a = σ i
  · subst ha
    rw [stdVec, Pi.single_eq_same, mul_one]
  · rw [stdVec, Pi.single_eq_of_ne ha, mul_zero, mul_zero]

/-- Left multiplication by a diagonal matrix rescales rows. -/
theorem diagonal_mul_apply (ν : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℝ)
    (a b : Fin d) :
    (Matrix.diagonal ν * X) a b = ν a * X a b := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single a]
  · rw [Matrix.diagonal_apply_eq]
  · intro x _ hx; rw [Matrix.diagonal_apply_ne _ (Ne.symm hx), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Signed target read-off.**  Suppose the collapse holds for context `k` and the
observational context:
`B'ₖ M = diagonal ν permMat σ Bₖ` and `B'₀ M = diagonal ν permMat σ B₀`, with `Θₖ ≠ Θ₀`.
Then the primed target equals the relabelled target: `i'ₖ = σ(iₖ)`.

Subtracting the two relations gives `(B'ₖ − B'₀) M = diagonal ν permMat σ (Bₖ − B₀)`,
i.e. `e_{i'ₖ} (Mᵀ c'ₖ)ᵀ = (ν_{σ iₖ} e_{σ iₖ}) cₖᵀ` as rank-one matrices.  Since
`cₖ ≠ 0` (`cvec_ne_zero`) and `ν_{σ iₖ} ≠ 0`, comparing the `(σ iₖ, ·)` row forces the
basis index `i'ₖ` to be `σ iₖ`. -/
theorem target_readoff (S S' : Solution d p K) {M : Matrix (Fin d) (Fin d) ℝ}
    {σ : Equiv.Perm (Fin d)} {ν : Fin d → ℝ} (k : Fin K) (hk : S.Theta k ≠ S.Theta0)
    (hν : ∀ i, ν i = 1 ∨ ν i = -1)
    (hBk : S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k)
    (hB0 : S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0) :
    S'.target k = σ (S.target k) := by
  -- Subtract the observational relation:
  -- `(B'ₖ − B'₀) M = diagonal ν permMat σ (Bₖ − B₀)`.
  have hsub : (S'.Bint k - S'.B0) * M =
      Matrix.diagonal ν * permMat σ * (S.Bint k - S.B0) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hBk, hB0]
  -- Rewrite both sides as rank-one (outer-product) matrices.
  rw [Bint_sub_B0, Bint_sub_B0, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec,
    diag_permMat_mulVec_stdVec] at hsub
  -- Pick an index `b` where `cₖ` is non-zero.
  obtain ⟨b, hb⟩ := Function.ne_iff.mp (cvec_ne_zero S k hk)
  rw [Pi.zero_apply] at hb
  -- Compare the `(σ iₖ, b)` entries of the two rank-one matrices.
  have hentry := congrFun (congrFun hsub (σ (S.target k))) b
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, stdVec,
    Pi.single_eq_same] at hentry
  have hνne : ν (σ (S.target k)) ≠ 0 := by
    rcases hν (σ (S.target k)) with h | h <;> rw [h] <;> norm_num
  -- LHS `(e_{i'ₖ})_{σ iₖ} · (Mᵀ c'ₖ)_b = (cₖ)_b ≠ 0` forces `(e_{i'ₖ})_{σ iₖ} ≠ 0`.
  by_contra hne
  rw [Pi.single_eq_of_ne (fun h => hne h.symm), zero_mul] at hentry
  exact (mul_ne_zero (mul_ne_zero hνne one_ne_zero) hb) hentry.symm

/-! ### (S1) The SUM TRICK — diagonalizing the unprimed Gram differences

Summing the latent key identity (C) over a *section* `kof` of the (surjective) target map
`S.target` collapses the unprimed side to `diagonal(d) − B₀ᵀB₀` with `d n = (λ_{kof n})² > 0`:
the rank-one targets `e_{i_{kof n}} = e_n` sum to the identity-weighting `diagonal(d)`, and the
rows `w_n = B₀ᵀ e_n` sum, via `fact_transpose_mul`, to `B₀ᵀB₀`. -/

/-- `∑ n, (c n) • (e_n e_nᵀ) = diagonal c` (the rank-one standard-basis outer products sum to a
diagonal matrix). -/
theorem sum_smul_vecMulVec_stdVec_eq_diagonal {n : ℕ} (c : Fin n → ℝ) :
    (∑ i, (c i) • Matrix.vecMulVec (stdVec n i) (stdVec n i)) = Matrix.diagonal c := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, stdVec,
    Pi.single_apply, smul_eq_mul, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  · intro x _ hx; simp [Ne.symm hx]
  · intro hx; exact absurd (Finset.mem_univ a) hx

/-- **(S1) The unprimed SUM TRICK.**  Let `kof` be a section of the surjective target map
(`S.target (kof n) = n`).  Summing the latent key identity over `kof` gives
`∑ₙ (B_{kof n}ᵀ B_{kof n} − B₀ᵀB₀) = diagonal(d) − B₀ᵀB₀` with `d n = (λ_{kof n})²`. -/
theorem sum_latent_diff_unprimed (S : Solution d p K)
    (kof : Fin d → Fin K) (hkof : ∀ n, S.target (kof n) = n) :
    (∑ n, ((S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0))
      = Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) - S.B0.transpose * S.B0 := by
  -- Rewrite each summand by the latent key identity.
  have hterm : ∀ n,
      (S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0
        = (S.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n)
          - Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d n) (S.B0.transpose *ᵥ stdVec d n) := by
    intro n
    rw [latent_key_identity S (kof n), hkof n]
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  have hdistrib :
      (∑ n, ((S.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n)
          - Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d n) (S.B0.transpose *ᵥ stdVec d n)))
        = (∑ n, (S.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n))
          - ∑ n, Matrix.vecMulVec (S.B0.transpose *ᵥ stdVec d n) (S.B0.transpose *ᵥ stdVec d n) :=
    Finset.sum_sub_distrib ..
  rw [hdistrib, sum_smul_vecMulVec_stdVec_eq_diagonal, ← fact_transpose_mul S.B0]

/-- **(S1') The primed SUM TRICK with reindexed targets.**  If the primed targets along
the same section `kof` are `σ n`, summing the primed latent key identities gives a diagonal
whose `m`-th entry comes from the unique preimage `σ.symm m`. -/
theorem sum_latent_diff_primed_reindexed (S' : Solution d p K)
    (kof : Fin d → Fin K) (σ : Equiv.Perm (Fin d))
    (hσtarget : ∀ n, S'.target (kof n) = σ n) :
    (∑ n, ((S'.Bint (kof n)).transpose * S'.Bint (kof n)
        - S'.B0.transpose * S'.B0))
      = Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2)
        - S'.B0.transpose * S'.B0 := by
  have hterm : ∀ n,
      (S'.Bint (kof n)).transpose * S'.Bint (kof n) - S'.B0.transpose * S'.B0
        = (S'.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d (σ n)) (stdVec d (σ n))
          - Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d (σ n))
              (S'.B0.transpose *ᵥ stdVec d (σ n)) := by
    intro n
    rw [latent_key_identity S' (kof n), hσtarget n]
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  have hdistrib :
      (∑ n, ((S'.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d (σ n)) (stdVec d (σ n))
          - Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d (σ n))
              (S'.B0.transpose *ᵥ stdVec d (σ n))))
        = (∑ n, (S'.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d (σ n)) (stdVec d (σ n)))
          - ∑ n, Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d (σ n))
              (S'.B0.transpose *ᵥ stdVec d (σ n)) :=
    Finset.sum_sub_distrib ..
  rw [hdistrib]
  have hdiag :
      (∑ n, (S'.lam (kof n)) ^ 2 • Matrix.vecMulVec (stdVec d (σ n)) (stdVec d (σ n)))
        = ∑ m, (S'.lam (kof (σ.symm m))) ^ 2 • Matrix.vecMulVec (stdVec d m) (stdVec d m) := by
    let f : Fin d → Matrix (Fin d) (Fin d) ℝ :=
      fun m => (S'.lam (kof (σ.symm m))) ^ 2 • Matrix.vecMulVec (stdVec d m) (stdVec d m)
    simpa [f] using (Equiv.sum_comp σ f)
  have hgram :
      (∑ n, Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d (σ n))
              (S'.B0.transpose *ᵥ stdVec d (σ n)))
        = ∑ m, Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d m)
              (S'.B0.transpose *ᵥ stdVec d m) := by
    let f : Fin d → Matrix (Fin d) (Fin d) ℝ :=
      fun m => Matrix.vecMulVec (S'.B0.transpose *ᵥ stdVec d m)
        (S'.B0.transpose *ᵥ stdVec d m)
    simpa [f] using (Equiv.sum_comp σ f)
  rw [hdiag, hgram, sum_smul_vecMulVec_stdVec_eq_diagonal, ← fact_transpose_mul S'.B0]

/-- Summing the per-context Gram-difference transport pulls the common conjugation
`Mᵀ · _ · M` outside the finite sum. -/
theorem sum_gram_diff_transport (S S' : Solution d p K)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : S'.H = M * S.H)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    (kof : Fin d → Fin K) :
    (∑ n, ((S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0))
      = M.transpose *
          (∑ n, ((S'.Bint (kof n)).transpose * S'.Bint (kof n)
            - S'.B0.transpose * S'.B0)) * M := by
  calc
    (∑ n, ((S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0))
        = ∑ n, M.transpose *
            (((S'.Bint (kof n)).transpose * S'.Bint (kof n)
              - S'.B0.transpose * S'.B0)) * M := by
          exact Finset.sum_congr rfl
            (fun n _ => gram_diff_transport S S' hM hΘ0 hΘ (kof n))
    _ = M.transpose *
          (∑ n, ((S'.Bint (kof n)).transpose * S'.Bint (kof n)
            - S'.B0.transpose * S'.B0)) * M := by
          rw [Finset.mul_sum, Finset.sum_mul]

end Causalean.Discovery.LinearDisentanglement
