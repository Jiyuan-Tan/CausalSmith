/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Rowspan
public import Causalean.Discovery.LinearDisentanglement.SigmaSolutions
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part1
public import Causalean.Discovery.LinearDisentanglement.Uniqueness_Part2
public import Causalean.Mathlib.LinearAlgebra.Cholesky
public import Mathlib.Data.Real.StarOrdered

/-!
# Linear causal disentanglement: conditional unnormalized uniqueness, part 3

This third proof file contains the model-specific geometric core. Starting from
the orthogonalized change of basis supplied by `Uniqueness_Part2`, it proves that
the change of basis is monomial, pins its permutation to the graph order, and
reads off the transformed structural matrices and intervention targets.

Its public result `exists_orderPerm` packages that collapse. `Uniqueness_Part4`
substitutes it into the recovered change of basis to state the final conditional
uniqueness theorem. The overall route is summarized in `Uniqueness`.
-/

public section

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

/-! ### Model-specific monomial collapse -/
/-- The remaining geometric core after the permutation choice, SUM TRICK, and diagonal
orthogonalization have all been made explicit.

The proof has three parts.  **(D)** A decreasing strong induction on the rows of
`O = diag(√d') M diag(√d⁻¹)` (orthogonal by `hO`), using `central_rank2_eq` and the
`e_c`-support / parent-elimination argument, shows that the `σ n`-row of `O` is `±eₙ`;
**(E)** reading `O`'s monomial structure back through the positive diagonal
rescalings gives `M = diagonal μ · permMat σ` with nonzero `μ`; and **(F)** the
signed-Cholesky read-off (`signed_cholesky`, `orthogonal_upperTri_signed_diag`)
then produces the per-context relations
`B'ₖ M = diagonal ν · permMat σ · Bₖ` with the shared sign vector `ν = sign ∘ μ`.  Its only
graph-theoretic input — the σ-triangularity `S'.B₀ (σ a)(σ b) = 0` for `b < a` (that `σ`
carries the partial order of `𝒢` into that of `𝒢'`) — is read off directly from the `(b,a)`
entry of `central_rank2_eq` (`hB0σtri`). -/
private theorem monomial_relations_from_orthogonal_core (S S' : Solution d p K)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : S'.H = M * S.H)
    (kof : Fin d → Fin K) (hkof : ∀ n, S.target (kof n) = n)
    (σ : Equiv.Perm (Fin d)) (hσtarget : ∀ n, S'.target (kof n) = σ n)
    (hO :
      (Matrix.diagonal (fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2)) * M
          * Matrix.diagonal (fun n => (Real.sqrt ((S.lam (kof n)) ^ 2))⁻¹)).transpose
        * (Matrix.diagonal (fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2)) * M
          * Matrix.diagonal (fun n => (Real.sqrt ((S.lam (kof n)) ^ 2))⁻¹)) = 1) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ),
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      M = Matrix.diagonal μ * permMat σ ∧
      S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k) := by
  classical
  -- Positive diagonal rescalings turning `M` into the orthogonal `O`.
  set sd : Fin d → ℝ := fun n => Real.sqrt ((S.lam (kof n)) ^ 2) with hsd
  set sd' : Fin d → ℝ := fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2) with hsd'
  have hsd_pos : ∀ n, 0 < sd n := fun n =>
    Real.sqrt_pos.mpr (sq_pos_of_ne_zero (ne_of_gt (S.hlam (kof n))))
  have hsd'_pos : ∀ m, 0 < sd' m := fun m =>
    Real.sqrt_pos.mpr (sq_pos_of_ne_zero (ne_of_gt (S'.hlam (kof (σ.symm m)))))
  set O : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal sd' * M * Matrix.diagonal (fun n => (sd n)⁻¹) with hOdef
  -- Entrywise: `O a b = sd' a · M a b · (sd b)⁻¹`.
  have hOentry : ∀ a b : Fin d, O a b = sd' a * M a b * (sd b)⁻¹ := by
    intro a b
    rw [hOdef, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hO1 : Oᵀ * O = 1 := hO
  -- `O` is square with left inverse `Oᵀ`, hence `O Oᵀ = 1` (orthonormal rows too).
  haveI : Invertible O := invertibleOfLeftInverse _ _ hO1
  have hO2 : O * Oᵀ = 1 := by
    have := Matrix.mul_inv_of_invertible O
    rwa [Matrix.inv_eq_left_inv hO1] at this
  -- `M a b = (sd' a)⁻¹ · O a b · sd b`.
  have hMentry : ∀ a b : Fin d, M a b = (sd' a)⁻¹ * O a b * sd b := by
    intro a b
    rw [hOentry]
    have ha : sd' a ≠ 0 := ne_of_gt (hsd'_pos a)
    have hb : sd b ≠ 0 := ne_of_gt (hsd_pos b)
    field_simp
  -- `O a b = 0 ↔ M a b = 0` (the scalings are nonzero).
  have hMO_zero : ∀ a b : Fin d, M a b = 0 ↔ O a b = 0 := by
    intro a b
    rw [hOentry]
    constructor
    · intro h; rw [h]; ring
    · intro h
      have := mul_eq_zero.mp h
      rcases this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (ne_of_gt (hsd'_pos a))
        · exact h2
      · exact absurd h1 (inv_ne_zero (ne_of_gt (hsd_pos b)))
  -- **STEP (D).** Decreasing induction: the `σ n`-th row of `O` is `(O (σ n) n) • eₙ`
  -- with `O (σ n) n = ±1`.
  have hD : ∀ n : Fin d,
      (∀ j, j ≠ n → O (σ n) j = 0) ∧ (O (σ n) n = 1 ∨ O (σ n) n = -1) := by
    intro n
    induction n using WellFoundedGT.induction with
    | _ n hIH =>
      -- Abbreviations for `central_rank2_eq` at context `kof n`.
      set lam := S.lam (kof n) with hlam
      set lam' := S'.lam (kof n) with hlam'
      set wn : Fin d → ℝ := fun j => S.B0 n j with hwn
      set mrow : Fin d → ℝ := fun j => M (σ n) j with hmrow
      set wn' : Fin d → ℝ :=
        Mᵀ *ᵥ (S'.B0.transpose *ᵥ stdVec d (σ n)) with hwn'
      -- The central rank-≤2 equation, rewritten with the target identifications.
      have hCR :
          lam ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n)
              - Matrix.vecMulVec wn wn
            = lam' ^ 2 • Matrix.vecMulVec mrow mrow - Matrix.vecMulVec wn' wn' := by
        have hbase := central_rank2_eq S S' hM hΘ0 hΘ (kof n)
        rw [hkof n, hσtarget n] at hbase
        rw [transpose_mulVec_stdVec S.B0 n] at hbase
        rw [transpose_mulVec_stdVec M (σ n)] at hbase
        simpa [hlam, hlam', hwn, hmrow, hwn'] using hbase
      -- **(D1) Support of `mrow ⊆ Pa(n)`.**
      have hD1 : ∀ c, c ≠ n → ¬ S.Edge c n → mrow c = 0 := by
        intro c hcn hce
        -- `wn c = B0 n c = 0`: off-diagonal nonzero requires an edge.
        have hwnc : wn c = 0 := by
          rw [hwn]
          by_contra h
          exact hce ((S.hB0supp n c (Ne.symm hcn)).mp h)
        have hsnc : (stdVec d n) c = 0 := by simp [stdVec, hcn]
        -- Take the `(·, c)` column of (CR).  LHS vanishes (`eₙ c = 0`, `wn c = 0`).
        -- Result: `lam'² (mrow c) • mrow = (wn' c) • wn'`  as functions of `a`.
        have hstar : ∀ a, lam' ^ 2 * mrow c * mrow a = wn' c * wn' a := by
          intro a
          have hcol := congrFun (congrFun hCR a) c
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
            smul_eq_mul] at hcol
          rw [hsnc, mul_zero, mul_zero,
            hwnc, mul_zero, sub_zero] at hcol
          -- `0 = lam'² (mrow a)(mrow c) - (wn' a)(wn' c)`
          have : lam' ^ 2 * (mrow a * mrow c) - wn' a * wn' c = 0 := by linarith [hcol]
          nlinarith [this]
        by_contra hmc
        -- `mrow c ≠ 0`.  Two cases on `wn' c`.
        by_cases hwc : wn' c = 0
        · -- Then `lam'² (mrow c) • mrow = 0`, forcing `mrow c = 0`.
          have := hstar c
          rw [hwc, zero_mul] at this
          have hl2 : (0 : ℝ) < lam' ^ 2 := sq_pos_of_ne_zero (ne_of_gt (S'.hlam (kof n)))
          have : mrow c = 0 := by
            rcases mul_eq_zero.mp this with h | h
            · rcases mul_eq_zero.mp h with h' | h'
              · exact absurd h' (ne_of_gt hl2)
              · exact h'
            · exact h
          exact hmc this
        · -- `wn' = β • mrow` with `β = lam'² (mrow c)/(wn' c)`.
          set β := lam' ^ 2 * mrow c / wn' c with hβ
          have hwn'_eq : ∀ a, wn' a = β * mrow a := by
            intro a
            rw [hβ]
            field_simp
            linarith [hstar a]
          -- Substitute into (CR): the primed side collapses to `(lam'² - β²) • mrow⊗mrow`.
          have hCR2 :
              lam ^ 2 • Matrix.vecMulVec (stdVec d n) (stdVec d n)
                  - Matrix.vecMulVec wn wn
                = (lam' ^ 2 - β ^ 2) • Matrix.vecMulVec mrow mrow := by
            rw [hCR]
            ext a b
            simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
              smul_eq_mul]
            rw [hwn'_eq a, hwn'_eq b]
            ring
          -- The `(c,c)` entry: LHS `= 0`, RHS `= (lam'²-β²)(mrow c)²`, so `lam'² = β²`.
          have hcc := congrFun (congrFun hCR2 c) c
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
            smul_eq_mul] at hcc
          rw [hsnc, mul_zero, mul_zero,
            hwnc, mul_zero, sub_zero] at hcc
          -- `0 = (lam'² - β²)(mrow c)²`, `mrow c ≠ 0`, so `lam'² = β²`.
          have hβsq : lam' ^ 2 - β ^ 2 = 0 := by
            have : (lam' ^ 2 - β ^ 2) * (mrow c * mrow c) = 0 := by linarith [hcc]
            rcases mul_eq_zero.mp this with h | h
            · exact h
            · exact absurd (mul_self_eq_zero.mp h) hmc
          -- Then the whole primed side is `0`, so the latent Gram difference is `0`,
          -- contradicting `hNondeg`.
          rw [hβsq, zero_smul] at hCR2
          -- `λ²(eₙeₙᵀ) − wₙwₙᵀ = 0`, hence `Bₖᵀ Bₖ − B₀ᵀ B₀ = 0`, so `Θₖ = Θ₀`.
          have hlatent :
              (S.Bint (kof n)).transpose * S.Bint (kof n) - S.B0.transpose * S.B0 = 0 := by
            rw [latent_key_identity S (kof n), hkof n]
            rw [show (S.B0.transpose *ᵥ stdVec d n) = wn from transpose_mulVec_stdVec S.B0 n]
            rw [show (S.lam (kof n)) = lam from rfl]
            exact hCR2
          apply hNondeg (kof n)
          rw [Solution.Theta, Solution.Theta0]
          have hΘdiff :
              (S.Bint (kof n)).transpose * S.Bint (kof n) = S.B0.transpose * S.B0 :=
            sub_eq_zero.mp hlatent
          have : S.H.transpose * ((S.Bint (kof n)).transpose * S.Bint (kof n)) * S.H
              = S.H.transpose * (S.B0.transpose * S.B0) * S.H := by rw [hΘdiff]
          simpa [Matrix.mul_assoc] using this
      -- **(D2) Parent elimination** + combine to get the row collapse.
      -- First: the `σn`-row of `O` vanishes off `{n}`.
      have hrow_off : ∀ j, j ≠ n → O (σ n) j = 0 := by
        intro j hjn
        by_cases hedge : S.Edge j n
        · -- `j` is a parent: `n < j`, so IH applies to `j`.
          have hnj : n < j := S.hAcyc j n hedge
          obtain ⟨hIHzero, hIHsign⟩ := hIH j hnj
          -- `(σn, σj)` entry of `Oᵀ O = 1`: `∑ᵢ O (σn) i · O (σj) i = 0`.
          have hne : σ n ≠ σ j := fun h => (ne_of_lt hnj) (σ.injective h)
          have hsum := congrFun (congrFun hO2 (σ n)) (σ j)
          rw [Matrix.one_apply_ne hne, Matrix.mul_apply] at hsum
          simp only [Matrix.transpose_apply] at hsum
          -- `O (σj) i = 0` unless `i = j`; collapse the sum.
          rw [Finset.sum_eq_single j] at hsum
          · -- `O (σn) j · O (σj) j = 0`, `O (σj) j ≠ 0`.
            have hOjj : O (σ j) j ≠ 0 := by
              rcases hIHsign with h | h <;> rw [h] <;> norm_num
            rcases mul_eq_zero.mp hsum with h | h
            · exact h
            · exact absurd h hOjj
          · intro i _ hij
            rw [hIHzero i hij, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        · -- `j` is not a parent and `j ≠ n`: D1 + the `M↔O` zero transfer.
          have hmrowj : M (σ n) j = 0 := hD1 j hjn hedge
          exact (hMO_zero (σ n) j).mp hmrowj
      -- The `(σn, σn)` entry of `Oᵀ O = 1` collapses to `(O (σn) n)² = 1`.
      have hsq : (O (σ n) n) ^ 2 = 1 := by
        have hsum := congrFun (congrFun hO2 (σ n)) (σ n)
        rw [Matrix.one_apply_eq, Matrix.mul_apply] at hsum
        simp only [Matrix.transpose_apply] at hsum
        rw [Finset.sum_eq_single n] at hsum
        · rw [← sq] at hsum; exact hsum
        · intro i _ hin
          have : O (σ n) i = 0 := hrow_off i hin
          rw [this, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      exact ⟨hrow_off, sq_eq_one_iff.mp hsq⟩
  -- **STEP (E).** Monomial form of `M`.
  -- The `σ n`-row of `M` vanishes off `{n}`, and `M (σ n) n ≠ 0`.
  have hMrow_off : ∀ n j, j ≠ n → M (σ n) j = 0 := by
    intro n j hjn
    exact (hMO_zero (σ n) j).mpr ((hD n).1 j hjn)
  have hMdiag_ne : ∀ n, M (σ n) n ≠ 0 := by
    intro n
    rw [Ne, hMO_zero (σ n) n]
    rcases (hD n).2 with h | h <;> rw [h] <;> norm_num
  -- The scalings `μ` (nonzero diagonal of `M`) and `ν` (row signs of `O`).
  set μ : Fin d → ℝ := fun i => M i (σ.symm i) with hμdef
  set ν : Fin d → ℝ := fun i => O i (σ.symm i) with hνdef
  have hμ : ∀ i, μ i ≠ 0 := by
    intro i
    have : μ i = M (σ (σ.symm i)) (σ.symm i) := by rw [hμdef, Equiv.apply_symm_apply]
    rw [this]; exact hMdiag_ne (σ.symm i)
  have hν : ∀ i, ν i = 1 ∨ ν i = -1 := by
    intro i
    have : ν i = O (σ (σ.symm i)) (σ.symm i) := by rw [hνdef, Equiv.apply_symm_apply]
    rw [this]; exact (hD (σ.symm i)).2
  -- `M = diagonal μ * permMat σ`.
  have hMeq : M = Matrix.diagonal μ * permMat σ := by
    ext i j
    rw [Matrix.diagonal_mul, permMat_apply_symm]
    by_cases hij : j = σ.symm i
    · -- `i = σ j`, the diagonal entry.
      subst hij
      rw [if_pos rfl, mul_one, hμdef]
    · -- off-diagonal: `M i j = 0`.
      rw [if_neg hij, mul_zero]
      -- `i = σ (σ.symm i)`; row `σ (σ.symm i)` of `M` vanishes off `{σ.symm i}`.
      have hi : i = σ (σ.symm i) := (Equiv.apply_symm_apply σ i).symm
      rw [hi]
      exact hMrow_off (σ.symm i) j hij
  -- **STEP (F).** The signed per-context relations, with the shared sign vector
  -- `ν i = sign(μ i)`.
  set νF : Fin d → ℝ := fun i => if 0 < μ i then (1 : ℝ) else -1 with hνF
  have hνF_sign : ∀ i, νF i = 1 ∨ νF i = -1 := by
    intro i; rw [hνF]; by_cases h : 0 < μ i <;> simp [h]
  -- **(F-core) The per-context signed relation**, given the σ-triangularity of `B'`.
  -- `B' M = diagonal νF · permMat σ · B`.
  have bRel : ∀ B B' : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, j < i → B i j = 0) → (∀ i, 0 < B i i) →
      (∀ i, 0 < B' i i) →
      (∀ a b, b < a → B' (σ a) (σ b) = 0) →
      B.transpose * B = M.transpose * (B'.transpose * B') * M →
      B' * M = Matrix.diagonal νF * permMat σ * B := by
    intro B B' hBu hBp hB'p hB'tri hgram
    -- `P := (permMat σ)ᵀ * B' * M`, then `Pᵀ P = Bᵀ B` and `P` is upper-triangular.
    set P : Matrix (Fin d) (Fin d) ℝ := (permMat σ).transpose * B' * M with hP
    -- `P a b = B' (σ a) (σ b) · μ (σ b)`.
    have hPentry : ∀ a b, P a b = B' (σ a) (σ b) * μ (σ b) := by
      intro a b
      have hPeq : P = (permMat σ).transpose * (B' * Matrix.diagonal μ) * permMat σ := by
        rw [hP, hMeq]; simp only [Matrix.mul_assoc]
      rw [hPeq, permMat_conj_apply' σ (B' * Matrix.diagonal μ) a b, Matrix.mul_diagonal]
    -- `P` is upper-triangular (from `B'`'s σ-triangularity).
    have hPu : ∀ i j, j < i → P i j = 0 := by
      intro i j hji
      rw [hPentry, hB'tri i j hji, zero_mul]
    -- `Pᵀ P = Bᵀ B`.
    have hPgram : P.transpose * P = B.transpose * B := by
      rw [hP, hgram]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (permMat σ) (permMat σ).transpose, permMat_mul_transpose,
        Matrix.one_mul]
    -- Signed Cholesky: `P = diagonal s · B` with `s i = ±1` and `s i · B i i = P i i`.
    obtain ⟨s, hssign, hsval, hPsB⟩ := signed_cholesky hPu hBu hBp hPgram
    -- The sign equals `νF (σ ·)`: `s i = sign(μ (σ i))`.
    have hs_eq : ∀ i, s i = νF (σ i) := by
      intro i
      have hval := hsval i
      rw [hPentry] at hval
      -- `s i · B i i = B' (σ i)(σ i) · μ (σ i)`; both diagonals positive.
      have hBii : 0 < B i i := hBp i
      have hB'ii : 0 < B' (σ i) (σ i) := hB'p (σ i)
      change s i = if 0 < μ (σ i) then (1 : ℝ) else -1
      by_cases hμpos : 0 < μ (σ i)
      · rw [if_pos hμpos]
        rcases hssign i with h | h
        · exact h
        · -- `s i = -1` contradicts the signs: LHS `< 0`, RHS `> 0`.
          exfalso
          rw [h] at hval
          have hlhs : (-1 : ℝ) * B i i < 0 := by nlinarith [hBii]
          have hrhs : 0 < B' (σ i) (σ i) * μ (σ i) := mul_pos hB'ii hμpos
          linarith [hval]
      · rw [if_neg hμpos]
        have hμneg : μ (σ i) < 0 := lt_of_le_of_ne (not_lt.mp hμpos) (hμ (σ i))
        rcases hssign i with h | h
        · exfalso
          rw [h] at hval
          have hlhs : (0 : ℝ) < 1 * B i i := by nlinarith [hBii]
          have hrhs : B' (σ i) (σ i) * μ (σ i) < 0 := mul_neg_of_pos_of_neg hB'ii hμneg
          linarith [hval]
        · exact h
    -- Assemble: `B' M = permMat σ · P = permMat σ · diagonal s · B`.
    have hBM : B' * M = permMat σ * P := by
      rw [hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, permMat_mul_transpose, Matrix.one_mul]
    rw [hBM, hPsB, ← Matrix.mul_assoc, permMat_mul_diagonal]
    -- `s ∘ σ.symm = νF`.
    have hsσ : (fun i => s (σ.symm i)) = νF := by
      funext i; rw [hs_eq, Equiv.apply_symm_apply]
    rw [hsσ]
  -- The per-context Gram identities (conjugation form).
  have hgram0 : S.B0.transpose * S.B0
      = M.transpose * (S'.B0.transpose * S'.B0) * M := by
    refine gram_identity_conj S S' hM ?_
    simp only [Solution.Theta0, Matrix.mul_assoc] at hΘ0 ⊢
    exact hΘ0
  have hgramk : ∀ k, (S.Bint k).transpose * S.Bint k
      = M.transpose * ((S'.Bint k).transpose * S'.Bint k) * M := by
    intro k
    refine gram_identity_conj S S' hM ?_
    have := hΘ k
    simp only [Solution.Theta, Matrix.mul_assoc] at this ⊢
    exact this
  -- **(F-crux) The σ-triangularity / graph correspondence: `S'.B0 (σ a)(σ b) = 0` for `b < a`.**
  -- (`σ` carries the order support of `𝒢` into that of `𝒢'`.)  This is read off directly from
  -- the `(b, a)` entry of `central_rank2_eq` at context `kof a`: since `M` is monomial (its
  -- `σ a`-row is `μ_{σa}·eₐ`) and `B₀` is upper triangular (`(B₀)_{a,b} = 0` for `b < a`), the
  -- unprimed side of that entry vanishes, forcing `μ_{σb}·(B'₀)_{σa,σb}·μ_{σa}·(B'₀)_{σa,σa} = 0`;
  -- the three known-nonzero factors then give `(B'₀)_{σa,σb} = 0`.  No extra induction needed.
  have hB0σtri : ∀ a b, b < a → S'.B0 (σ a) (σ b) = 0 := by
    -- `(Mᵀ *ᵥ w) j = w (σ j) * M (σ j) j`, since `M` is monomial (row `σ j` supported on `{j}`).
    have hMtw : ∀ (w : Fin d → ℝ) (j : Fin d),
        (M.transpose *ᵥ w) j = w (σ j) * M (σ j) j := by
      intro w j
      rw [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (σ j)]
      · intro l _ hl
        have hMlj : M l j = 0 := by
          have hlj : j ≠ σ.symm l := fun h => hl (by rw [h, Equiv.apply_symm_apply])
          have h2 := hMrow_off (σ.symm l) j hlj
          rwa [Equiv.apply_symm_apply] at h2
        rw [hMlj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    intro a b hba
    have hba' : b ≠ a := ne_of_lt hba
    have hcr := central_rank2_eq S S' hM hΘ0 hΘ (kof a)
    rw [hkof a, hσtarget a] at hcr
    have h := congrFun (congrFun hcr b) a
    -- Evaluate the `(b, a)` entry; the unprimed (LHS) part vanishes (`b < a`, `B₀` upper-tri).
    have hub : (stdVec d a) b = 0 := by rw [stdVec, Pi.single_eq_of_ne hba']
    have hvb : (S.B0.transpose *ᵥ stdVec d a) b = 0 := by
      rw [transpose_mulVec_stdVec]; exact S.hB0up a b hba
    have hu'b : (M.transpose *ᵥ stdVec d (σ a)) b = 0 := by
      rw [hMtw, stdVec, Pi.single_eq_of_ne (show σ b ≠ σ a from fun h => hba' (σ.injective h)),
        zero_mul]
    have hw''b : (M.transpose *ᵥ (S'.B0.transpose *ᵥ stdVec d (σ a))) b
        = S'.B0 (σ a) (σ b) * M (σ b) b := by
      rw [hMtw, transpose_mulVec_stdVec]
    have hw''a : (M.transpose *ᵥ (S'.B0.transpose *ᵥ stdVec d (σ a))) a
        = S'.B0 (σ a) (σ a) * M (σ a) a := by
      rw [hMtw, transpose_mulVec_stdVec]
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply,
      Matrix.vecMulVec_apply, hub, hvb, hu'b, hw''b, hw''a] at h
    simp only [zero_mul, mul_zero, sub_zero, zero_sub, smul_eq_mul] at h
    -- `h : 0 = -(S'.B0 (σ a) (σ b) * M (σ b) b * (S'.B0 (σ a) (σ a) * M (σ a) a))`.
    have hprod : S'.B0 (σ a) (σ b) * M (σ b) b * (S'.B0 (σ a) (σ a) * M (σ a) a) = 0 := by
      linarith [h]
    have h1 : M (σ b) b ≠ 0 := hMdiag_ne b
    have h2 : M (σ a) a ≠ 0 := hMdiag_ne a
    have h3 : S'.B0 (σ a) (σ a) ≠ 0 := ne_of_gt (S'.hB0pos (σ a))
    have hsnd : S'.B0 (σ a) (σ a) * M (σ a) a ≠ 0 := mul_ne_zero h3 h2
    rcases mul_eq_zero.mp hprod with hx | hx
    · rcases mul_eq_zero.mp hx with hy | hy
      · exact hy
      · exact absurd hy h1
    · exact absurd hx hsnd
  -- The interventional σ-triangularity follows from the observational one: an intervention
  -- only rewrites the target row, which (off its diagonal) vanishes; all other rows agree
  -- with `B'₀`.
  have hBintσtri : ∀ k a b, b < a → S'.Bint k (σ a) (σ b) = 0 := by
    intro k a b hba
    have hσne : σ b ≠ σ a := fun h => (ne_of_lt hba) (σ.injective h)
    by_cases hi : σ a = S'.target k
    · -- target row of `B'ₖ` is `λ'ₖ · e_{target}`; off the diagonal it vanishes.
      have hrow : (fun j => S'.Bint k (S'.target k) j)
          = (S'.lam k) • stdVec d (S'.target k) := by
        rw [← transpose_mulVec_stdVec (S'.Bint k) (S'.target k)]
        exact Bint_transpose_mulVec_target S' k
      have hbne : σ b ≠ S'.target k := hi ▸ hσne
      have := congrFun hrow (σ b)
      rw [hi]
      simp only [Pi.smul_apply, smul_eq_mul, stdVec, Pi.single_eq_of_ne hbne, mul_zero] at this
      exact this
    · -- non-target row: agrees with `B'₀`.
      rw [S'.hInt k, Matrix.add_apply, Matrix.vecMulVec_apply]
      rw [hB0σtri a b hba, zero_add]
      simp only [stdVec, Pi.single_eq_of_ne hi, zero_mul]
  -- Apply `bRel` per context.
  have hB0rel : S'.B0 * M = Matrix.diagonal νF * permMat σ * S.B0 :=
    bRel S.B0 S'.B0 S.hB0up S.hB0pos S'.hB0pos hB0σtri hgram0
  have hBintrel : ∀ k, S'.Bint k * M = Matrix.diagonal νF * permMat σ * S.Bint k := by
    intro k
    exact bRel (S.Bint k) (S'.Bint k) (Bint_blockTriangular S k) (Bint_diag_pos S k)
      (Bint_diag_pos S' k) (hBintσtri k) (hgramk k)
  exact ⟨σ, μ, νF, hμ, hνF_sign, hMeq, hB0rel, hBintrel⟩

/-- **(S3 — the geometric core: monomial collapse + per-context relations.)**

This is the paper's `prop:orthogonal-correctness`, without a sign-fixing assumption.  It
produces the order relabeling `σ`, a nonzero signed diagonal scaling `μ`, a row-sign diagonal
`ν`, the signed monomial form `M = diagonal μ · permMat σ`, and the per-context structural
relations `B'₀ M = diagonal ν permMat σ B₀`, `B'ₖ M = diagonal ν permMat σ Bₖ`.  It is
everything in `orthogonal_collapse` except the order-preservation `InSG σ`, derived from
these relations below.

The SUM TRICK (`sum_latent_diff_unprimed`) and orthogonalization
(`orthogonal_of_diag_conj`) produce an orthogonal `O`; a decreasing topological
induction on its rows (`central_rank2_eq` support + orthogonality + unit norm)
makes `O` a signed permutation, hence `M = diagonal μ · permMat σ`.  The
per-context relations follow by the signed-Cholesky read-off, whose
σ-triangularity input is read off from the `(b,a)` entry of `central_rank2_eq`
(`monomial_relations_from_orthogonal_core`). -/
private theorem monomial_relations (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : S'.H = M * S.H) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ),
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      M = Matrix.diagonal μ * permMat σ ∧
      S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k) := by
  classical
  let τ : Fin K ≃ Fin d := Equiv.ofBijective S.target hcov
  let kof : Fin d → Fin K := τ.symm
  have hkof : ∀ n, S.target (kof n) = n := by
    intro n
    exact τ.apply_symm_apply n
  let ψ : Fin d → Fin d := fun n => S'.target (kof n)
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro a b hab
      apply τ.symm.injective
      exact hcov'.1 hab
    · intro y
      obtain ⟨k, hk⟩ := hcov'.2 y
      refine ⟨τ k, ?_⟩
      simp [ψ, kof, hk]
  let σ : Equiv.Perm (Fin d) := Equiv.ofBijective ψ hψbij
  have hσtarget : ∀ n, S'.target (kof n) = σ n := by
    intro n
    rfl
  have hdiag :
      M.transpose * Matrix.diagonal (fun m => (S'.lam (kof (σ.symm m))) ^ 2) * M
        = Matrix.diagonal (fun n => (S.lam (kof n)) ^ 2) :=
    diagonal_conj_from_sum_trick S S' hM hΘ0 hΘ kof hkof σ hσtarget
  have hd : ∀ n, 0 < (S.lam (kof n)) ^ 2 := by
    intro n
    exact sq_pos_of_ne_zero (ne_of_gt (S.hlam (kof n)))
  have hd' : ∀ m, 0 < (S'.lam (kof (σ.symm m))) ^ 2 := by
    intro m
    exact sq_pos_of_ne_zero (ne_of_gt (S'.hlam (kof (σ.symm m))))
  have hO :
      (Matrix.diagonal (fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2)) * M
          * Matrix.diagonal (fun n => (Real.sqrt ((S.lam (kof n)) ^ 2))⁻¹)).transpose
        * (Matrix.diagonal (fun m => Real.sqrt ((S'.lam (kof (σ.symm m))) ^ 2)) * M
          * Matrix.diagonal (fun n => (Real.sqrt ((S.lam (kof n)) ^ 2))⁻¹)) = 1 :=
    orthogonal_of_diag_conj hd hd' hdiag
  exact monomial_relations_from_orthogonal_core S S' hNondeg hΘ0 hΘ hM
    kof hkof σ hσtarget hO

private theorem orthogonal_collapse (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : S'.H = M * S.H) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ), S.InSG σ ∧
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      M = Matrix.diagonal μ * permMat σ ∧
      S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k) := by
  -- Get the monomial collapse and per-context relations (the isolated residual core).
  obtain ⟨σ, μ, ν, hμ, hν, hMeq, hB0rel, hBintrel⟩ :=
    monomial_relations S S' hcov hcov' hNondeg hΘ0 hΘ hM
  refine ⟨σ, μ, ν, ?_, hμ, hν, hMeq, hB0rel, hBintrel⟩
  -- **(S4) Derive `InSG σ`** from the signed `B'₀ M` relation and monomial form.
  -- Signed conjugation read-off: row signs and nonzero column scalings do not affect support.
  have hB0' : S'.B0 =
      Matrix.diagonal ν * permMat σ * S.B0 * (permMat σ).transpose
        * Matrix.diagonal (fun i => (μ i)⁻¹) :=
    conj_readoff hμ hMeq hB0rel
  intro j i hEdge
  -- `Edge j i ⟹ i < j` (acyclicity), so `i ≠ j`.
  have hij : i < j := S.hAcyc j i hEdge
  have hine : i ≠ j := ne_of_lt hij
  -- `B₀ i j ≠ 0` since `Edge j i` is in the off-diagonal support of `B₀`.
  have hB0ne : S.B0 i j ≠ 0 := (S.hB0supp i j hine).mpr hEdge
  -- Suppose `σ j < σ i`; read off `B'₀` at the upper-triangular zero entry `(σ i, σ j)`.
  by_contra hnotlt
  push_neg at hnotlt  -- `σ j ≤ σ i`
  have hlt : σ j < σ i := lt_of_le_of_ne hnotlt (fun h => hine.symm (σ.injective h))
  -- `B'₀ (σ i) (σ j) = 0` by upper-triangularity (`σ j < σ i`).
  have hzero : S'.B0 (σ i) (σ j) = 0 := S'.hB0up (σ i) (σ j) hlt
  -- But the read-off gives `B'₀ (σ i) (σ j) = ν (σ i) · B₀ i j · (μ (σ j))⁻¹ ≠ 0`.
  rw [hB0', Matrix.mul_apply] at hzero
  have hentry : (permMat σ * S.B0 * (permMat σ).transpose) (σ i) (σ j) = S.B0 i j := by
    rw [permMat_conj_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hAentry :
      (Matrix.diagonal ν * permMat σ * S.B0 * (permMat σ).transpose) (σ i) (σ j)
        = ν (σ i) * S.B0 i j := by
    calc
      (Matrix.diagonal ν * permMat σ * S.B0 * (permMat σ).transpose) (σ i) (σ j)
          = (Matrix.diagonal ν * (permMat σ * S.B0 * (permMat σ).transpose))
              (σ i) (σ j) := by
            simp only [Matrix.mul_assoc]
      _ = ν (σ i) * (permMat σ * S.B0 * (permMat σ).transpose) (σ i) (σ j) := by
            rw [diagonal_mul_apply]
      _ = ν (σ i) * S.B0 i j := by rw [hentry]
  have hνne : ν (σ i) ≠ 0 := by
    rcases hν (σ i) with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_eq_single (σ j)] at hzero
  · rw [Matrix.diagonal_apply_eq, hAentry] at hzero
    exact (mul_ne_zero (mul_ne_zero hνne hB0ne) (inv_ne_zero (hμ (σ j)))) hzero
  · intro x _ hx; rw [Matrix.diagonal_apply_ne _ hx, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- [Two observationally equivalent solutions differ only by an order-preserving relabeling,
nonzero coordinate scales, and row signs](goal), giving the full recoverable ambiguity. For
[solutions `S,S'` and their dimensions](hyp:d,p,K,S,S'), this requires [bijective targeting in
both solutions](hyp:hcov,hcov'), [nondegenerate interventions](hyp:hNondeg), [equal observational
and interventional precision families](hyp:hΘ0,hΘ), and [a latent transformation `M` satisfying
the loading relation](hyp:M,hM).

**(L4) Orthogonal correctness (full statement).**

Given the recovered invertible change-of-basis `M` with `H' = M H`, there is a single
order-preserving relabeling `σ ∈ S(𝒢)`, a nonzero signed diagonal scaling `μ`, and a row-sign
diagonal `ν` such that `M = diagonal μ · permMat σ` and, in every context, the structural
matrices satisfy `B'ₖ M = diagonal ν permMat σ Bₖ` (`k=0` and interventional), and the
intervention targets relabel as `i'ₖ = σ(iₖ)`.

The monomial collapse `orthogonal_collapse` supplies `σ`, `μ`, `ν`, `InSG σ` and the
per-context signed relations; the order-preservation `InSG σ` and the target relabeling
`i'ₖ = σ(iₖ)` are derived from those relations. -/
theorem exists_orderPerm (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : S'.H = M * S.H) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ), S.InSG σ ∧
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      M = Matrix.diagonal μ * permMat σ ∧
      S'.B0 * M = Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * M = Matrix.diagonal ν * permMat σ * S.Bint k) ∧
      (∀ k, S'.target k = σ (S.target k)) := by
  obtain ⟨σ, μ, ν, hσ, hμ, hν, hMeq, hB0rel, hBintrel⟩ :=
    orthogonal_collapse S S' hcov hcov' hNondeg hΘ0 hΘ hM
  exact ⟨σ, μ, ν, hσ, hμ, hν, hMeq, hB0rel, hBintrel,
    fun k => target_readoff S S' k (hNondeg k) hν (hBintrel k) hB0rel⟩

end Causalean.Discovery.LinearDisentanglement
