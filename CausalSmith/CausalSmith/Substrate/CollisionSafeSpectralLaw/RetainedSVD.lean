import CausalSmith.Substrate.CollisionSafeSpectralLaw.MoorePenrose

/-! # Retained finite singular-value decompositions -/

namespace CausalSmith.Substrate.CollisionSafeSpectralLaw

open scoped Matrix.Norms.L2Operator

/-- A finite collection of positive singular directions.  It represents the matrix obtained by
retaining precisely these directions, independently of how the ambient SVD was chosen. -/
structure RetainedSVD (r rows cols : ℕ) where
  sigma : Fin r → ℝ
  left : RectMatrix rows r
  right : RectMatrix r cols
  sigma_pos : ∀ i, 0 < sigma i
  left_orthonormal : left.transpose * left = (1 : RectMatrix r r)
  right_orthonormal : right * right.transpose = (1 : RectMatrix r r)

noncomputable def RetainedSVD.matrix {r rows cols : ℕ} (S : RetainedSVD r rows cols) :
    RectMatrix rows cols :=
  S.left * Matrix.diagonal S.sigma * S.right

noncomputable def RetainedSVD.inverse {r rows cols : ℕ} (S : RetainedSVD r rows cols) :
    RectMatrix cols rows :=
  S.right.transpose * Matrix.diagonal (fun i => (S.sigma i)⁻¹) * S.left.transpose

theorem RetainedSVD.matrix_apply {r rows cols : ℕ} (S : RetainedSVD r rows cols)
    (i : Fin rows) (j : Fin cols) :
    S.matrix i j = ∑ a, S.sigma a * S.left i a * S.right a j := by
  rw [RetainedSVD.matrix]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem RetainedSVD.inverse_apply {r rows cols : ℕ} (S : RetainedSVD r rows cols)
    (i : Fin cols) (j : Fin rows) :
    S.inverse i j = ∑ a, (S.sigma a)⁻¹ * S.right a i * S.left j a := by
  rw [RetainedSVD.inverse]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A common lower bound on the retained singular coefficients bounds the reciprocal
expansion in operator norm. -/
theorem RetainedSVD.norm_inverse_le {r rows cols : ℕ} (S : RetainedSVD r rows cols)
    {s : ℝ} (hs : 0 < s) (hlower : ∀ a, s ≤ S.sigma a) :
    ‖S.inverse‖ ≤ s⁻¹ := by
  let u : Fin r → Euc rows := fun a => WithLp.toLp 2 (fun i => S.left i a)
  let v : Fin r → Euc cols := fun a => WithLp.toLp 2 (S.right a)
  have hu : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro a b
    have hab := congrFun (congrFun S.left_orthonormal b) a
    simpa only [u, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm] using hab
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro a b
    have hab := congrFun (congrFun S.right_orthonormal b) a
    simpa only [v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm] using hab
  change ‖matrixCLM S.inverse‖ ≤ s⁻¹
  apply ContinuousLinearMap.opNorm_le_bound _ (le_of_lt (inv_pos.mpr hs))
  intro x
  let c : Fin r → ℝ := fun a => (S.sigma a)⁻¹ * inner ℝ (u a) x
  have haction : matrixCLM S.inverse x = ∑ a, c a • v a := by
    ext i
    simp [matrixCLM, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
      S.inverse_apply, c, u, v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [haction]
  have hinner := hv.inner_sum c c Finset.univ
  have hsq : ‖∑ a, c a • v a‖ ^ 2 ≤ s⁻¹ ^ 2 * ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hinner]
    calc
      (∑ a, c a * c a) ≤ ∑ a, s⁻¹ ^ 2 * ‖inner ℝ (u a) x‖ ^ 2 := by
        apply Finset.sum_le_sum (s := Finset.univ)
        intro a _
        have hsig : 0 < S.sigma a := S.sigma_pos a
        have hinv : (S.sigma a)⁻¹ ≤ s⁻¹ := inv_anti₀ hs (hlower a)
        have hinv0 : 0 ≤ (S.sigma a)⁻¹ := le_of_lt (inv_pos.mpr hsig)
        have hinv2 : (S.sigma a)⁻¹ ^ 2 ≤ s⁻¹ ^ 2 := by nlinarith
        dsimp [c]
        calc
          (S.sigma a)⁻¹ * inner ℝ (u a) x *
              ((S.sigma a)⁻¹ * inner ℝ (u a) x) =
              (S.sigma a)⁻¹ ^ 2 * inner ℝ (u a) x ^ 2 := by ring
          _ ≤ s⁻¹ ^ 2 * inner ℝ (u a) x ^ 2 :=
            mul_le_mul_of_nonneg_right hinv2 (sq_nonneg _)
          _ = s⁻¹ ^ 2 * ‖inner ℝ (u a) x‖ ^ 2 := by
            rw [Real.norm_eq_abs, sq_abs]
      _ = s⁻¹ ^ 2 * ∑ a, ‖inner ℝ (u a) x‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ s⁻¹ ^ 2 * ‖x‖ ^ 2 := by
        gcongr
        exact hu.sum_inner_products_le x
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr (le_of_lt hs))
    (norm_nonneg _))).mp (by simpa [mul_pow] using hsq)

/-- The reciprocal retained expansion is exactly the neutral Moore--Penrose inverse. -/
theorem RetainedSVD.inverse_eq_moorePenroseInverse {r rows cols : ℕ}
    (S : RetainedSVD r rows cols) :
    S.inverse = moorePenroseInverse S.matrix := by
  let D : RectMatrix r r := Matrix.diagonal S.sigma
  let E : RectMatrix r r := Matrix.diagonal (fun i => (S.sigma i)⁻¹)
  have hDE : D * E = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, E, Matrix.mul_apply, Matrix.diagonal_apply,
        mul_inv_cancel₀ (ne_of_gt (S.sigma_pos i))]
    · simp [D, E, Matrix.mul_apply, Matrix.diagonal_apply, hij]
  have hED : E * D = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, E, Matrix.mul_apply, Matrix.diagonal_apply,
        inv_mul_cancel₀ (ne_of_gt (S.sigma_pos i))]
    · simp [D, E, Matrix.mul_apply, Matrix.diagonal_apply, hij]
  have hspec : IsMoorePenroseInverse S.matrix S.inverse := by
    change IsMoorePenroseInverse
      (S.left * D * S.right) (S.right.transpose * E * S.left.transpose)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc S.right S.right.transpose, S.right_orthonormal,
        Matrix.one_mul, ← Matrix.mul_assoc D E, hDE, Matrix.one_mul,
        ← Matrix.mul_assoc S.left.transpose S.left, S.left_orthonormal,
        Matrix.one_mul]
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc S.left.transpose S.left, S.left_orthonormal,
        Matrix.one_mul, ← Matrix.mul_assoc E D, hED, Matrix.one_mul,
        ← Matrix.mul_assoc S.right S.right.transpose, S.right_orthonormal,
        Matrix.one_mul]
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc S.right S.right.transpose, S.right_orthonormal,
        Matrix.one_mul, ← Matrix.mul_assoc D E, hDE, Matrix.one_mul]
      simp [Matrix.transpose_mul]
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc S.left.transpose S.left, S.left_orthonormal,
        Matrix.one_mul, ← Matrix.mul_assoc E D, hED, Matrix.one_mul]
      simp [Matrix.transpose_mul]
  exact isMoorePenroseInverse_unique hspec (moorePenroseInverse_spec _)

/-- A retained positive `r`-frame has matrix rank exactly `r`. -/
theorem RetainedSVD.rank_matrix {r rows cols : ℕ} (S : RetainedSVD r rows cols) :
    S.matrix.rank = r := by
  let D : RectMatrix r r := Matrix.diagonal S.sigma
  let E : RectMatrix r r := Matrix.diagonal (fun i => (S.sigma i)⁻¹)
  have hED : E * D = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, E, Matrix.mul_apply, Matrix.diagonal_apply,
        inv_mul_cancel₀ (ne_of_gt (S.sigma_pos i))]
    · simp [D, E, Matrix.mul_apply, Matrix.diagonal_apply, hij]
  have hid : (E * S.left.transpose) * S.matrix * S.right.transpose =
      (1 : RectMatrix r r) := by
    change (E * S.left.transpose) * (S.left * D * S.right) * S.right.transpose = 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S.left.transpose S.left, S.left_orthonormal,
      Matrix.one_mul, S.right_orthonormal, Matrix.mul_one, hED]
  apply le_antisymm
  · change (S.left * D * S.right).rank ≤ r
    exact (Matrix.rank_mul_le_left (S.left * D) S.right).trans
      ((Matrix.rank_mul_le_left S.left D).trans (Matrix.rank_le_width S.left))
  · calc
      r = (1 : RectMatrix r r).rank := by
        simpa only [Fintype.card_fin] using
          (Matrix.rank_one (n := Fin r) (R := ℝ)).symm
      _ = ((E * S.left.transpose) * S.matrix * S.right.transpose).rank :=
        congrArg Matrix.rank hid.symm
      _ ≤ (S.matrix * S.right.transpose).rank :=
        by simpa only [Matrix.mul_assoc] using
          Matrix.rank_mul_le_right (E * S.left.transpose)
            (S.matrix * S.right.transpose)
      _ ≤ S.matrix.rank := Matrix.rank_mul_le_left S.matrix S.right.transpose

end CausalSmith.Substrate.CollisionSafeSpectralLaw
