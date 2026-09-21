import Causalean.Mathlib.Analysis.SymmetricTensorPencil.Conditioning

/-!
# Inverse and tensor-pencil perturbation bounds

This module packages the finite-dimensional inverse perturbation estimates needed after tensor
contractions are compressed to the lifted signal space.  The constants are exposed separately
so applications can assemble a local radius without unfolding proofs.
-/

namespace Causalean.Mathlib.Analysis.SymmetricTensorPencil

open scoped Matrix.Norms.L2Operator

/-- The right generalized-eigenvalue pencil formed from a numerator and denominator matrix. With [its explicit inputs](hyp:Aw,Au), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def rightPencil {n : ℕ} (Aw Au : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Aw * Au⁻¹

/-- The explicit Lipschitz coefficient for a right pencil whose denominator has lower singular
value `eta` and whose numerator norm is at most `n * Lambda`. With [its explicit inputs](hyp:n,eta,Lambda), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def pencilPerturbationConstant (n : ℕ) (eta Lambda : ℝ) : ℝ :=
  2 / eta + 2 * n * Lambda / eta ^ 2

/-- A positive lower bound on the least singular value of a real square matrix makes its
determinant a unit and bounds the operator norm of its inverse by the reciprocal margin. Under [the listed assumptions](hyp:heta,hsv), [the stated conclusion follows](goal). -/
-- Proof route: diagonalize `A†A`; positivity of its last eigenvalue eliminates the kernel and
-- gives the inverse bound after applying the least-singular-value expansion inequality.  The
-- preceding module already contains the required ingredients:
-- `injective_of_pos_le_leastColumnSingularValue`, `Matrix.mulVec_injective_iff_isUnit`, and the
-- proof pattern of `squareInverse_operatorNorm_le_reciprocal`.
theorem inverse_operatorNorm_le_reciprocal {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) {eta : ℝ}
    (heta : 0 < eta) (hsv : eta ≤ leastColumnSingularValue A) :
    IsUnit A.det ∧ squareOperatorNorm A⁻¹ ≤ eta⁻¹ := by
  have hinj := injective_of_pos_le_leastColumnSingularValue A heta hsv
  have hmulVec : Function.Injective A.mulVec := by
    intro x y hxy
    have hlp : A.toEuclideanLin (WithLp.toLp 2 x) =
        A.toEuclideanLin (WithLp.toLp 2 y) := by
      simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.toLp 2) hxy
    have := hinj hlp
    simpa using congrArg WithLp.ofLp this
  have hunitA : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hmulVec
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunitA
  refine ⟨hdet, ?_⟩
  rw [squareOperatorNorm]
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr heta.le)
  intro x
  let E := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
  have hcancel : E A (E A⁻¹ x) = x := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, Matrix.mul_nonsing_inv A hdet,
      map_one, ContinuousLinearMap.one_apply]
  have hleast := Causalean.Mathlib.Analysis.least_singularValue_mul_norm_le
    A.toEuclideanLin hinj (E A⁻¹ x)
  have heta_mul : eta * ‖E A⁻¹ x‖ ≤ ‖x‖ := by
    calc
      eta * ‖E A⁻¹ x‖ ≤ leastColumnSingularValue A * ‖E A⁻¹ x‖ :=
        mul_le_mul_of_nonneg_right hsv (norm_nonneg _)
      _ ≤ ‖A.toEuclideanLin (E A⁻¹ x)‖ := by
        simpa [leastColumnSingularValue, finrank_euclideanSpace] using hleast
      _ = ‖x‖ := by
        change ‖E A (E A⁻¹ x)‖ = ‖x‖
        rw [hcancel]
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ heta).2 (by simpa [mul_comm] using heta_mul)

/-- If a square matrix with least singular value at least `eta` is perturbed by at most
`e < eta / 2`, the perturbed matrix stays invertible and its inverse norm is at most `2 / eta`. Under [the listed assumptions](hyp:heta,he,hsv,hpert,hsmall), [the stated conclusion follows](goal). -/
-- Proof route: turn the determinant-unit witness for `A` into a matrix unit and use
-- `Units.ofNearby`/`Units.val_ofNearby` after proving
-- `‖A' - A‖ < ‖A⁻¹‖⁻¹`.  Bound the new inverse by factoring through the inverse of
-- `1 + A⁻¹(A'-A)` (or its geometric series), then use `Matrix.inv_sub_inv` for
-- `A'⁻¹-A⁻¹ = A'⁻¹(A-A')A⁻¹`.
theorem inverse_perturbation_bound {n : ℕ} [NeZero n]
    (A A' : Matrix (Fin n) (Fin n) ℝ) {eta e : ℝ}
    (heta : 0 < eta) (he : 0 ≤ e) (hsv : eta ≤ leastColumnSingularValue A)
    (hpert : squareOperatorNorm (A' - A) ≤ e) (hsmall : e < eta / 2) :
    IsUnit A'.det ∧ squareOperatorNorm A'⁻¹ ≤ 2 / eta ∧
      squareOperatorNorm (A'⁻¹ - A⁻¹) ≤ 2 * e / eta ^ 2 := by
  obtain ⟨hdetA, hinvA⟩ := inverse_operatorNorm_le_reciprocal A heta hsv
  change ‖A⁻¹‖ ≤ eta⁻¹ at hinvA
  change ‖A' - A‖ ≤ e at hpert
  let D := A' - A
  let Q := A⁻¹ * D
  have hQ : ‖Q‖ < 1 / 2 := by
    calc
      ‖Q‖ ≤ ‖A⁻¹‖ * ‖D‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ eta⁻¹ * e :=
        mul_le_mul hinvA hpert (norm_nonneg _) (inv_nonneg.mpr heta.le)
      _ < 1 / 2 := by
        rw [inv_mul_eq_div, div_lt_iff₀ heta]
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsmall
  have hnegQ : ‖-Q‖ < 1 := by simpa using hQ.trans (by norm_num)
  let B : Matrix (Fin n) (Fin n) ℝ := 1 + Q
  have hdetB : IsUnit B.det := by
    apply (Matrix.isUnit_iff_isUnit_det B).mp
    have hu := (Units.oneSub (-Q) hnegQ).isUnit
    simpa [B] using hu
  have hfactor : A' = A * B := by
    calc
      A' = A + D := by simp [D]
      _ = A * (1 + Q) := by
        simp only [Matrix.mul_add, Matrix.mul_one, Q, D]
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hdetA, Matrix.one_mul]
      _ = A * B := rfl
  have hdetA' : IsUnit A'.det := by
    rw [hfactor, Matrix.det_mul]
    exact hdetA.mul hdetB
  have hinvB : ‖B⁻¹‖ ≤ 2 := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [show B = 1 - (-Q) by simp [B], NormedRing.inverse_one_sub (-Q) hnegQ]
    change ‖∑' k : ℕ, (-Q) ^ k‖ ≤ 2
    have hgeom := tsum_geometric_le_of_norm_lt_one (-Q) hnegQ
    have hden : (1 - ‖-Q‖)⁻¹ ≤ 2 := by
      have : ‖-Q‖ < 1 / 2 := by simpa using hQ
      exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
    have hgeom' : ‖∑' k : ℕ, (-Q) ^ k‖ ≤ (1 - ‖-Q‖)⁻¹ := by
      simpa only [norm_one, sub_self, zero_add] using hgeom
    exact hgeom'.trans hden
  have hinvA' : ‖A'⁻¹‖ ≤ 2 / eta := by
    rw [hfactor, Matrix.mul_inv_rev]
    calc
      ‖B⁻¹ * A⁻¹‖ ≤ ‖B⁻¹‖ * ‖A⁻¹‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 2 * eta⁻¹ := mul_le_mul hinvB hinvA (norm_nonneg _) (by norm_num)
      _ = 2 / eta := by rw [div_eq_mul_inv]
  refine ⟨hdetA', hinvA', ?_⟩
  change ‖A'⁻¹ - A⁻¹‖ ≤ 2 * e / eta ^ 2
  have hunitA' : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').2 hdetA'
  have hunitA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 hdetA
  rw [Matrix.inv_sub_inv ⟨fun _ => hunitA, fun _ => hunitA'⟩]
  calc
    ‖A'⁻¹ * (A - A') * A⁻¹‖ ≤ ‖A'⁻¹ * (A - A')‖ * ‖A⁻¹‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖A'⁻¹‖ * ‖A - A'‖) * ‖A⁻¹‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ ((2 / eta) * e) * eta⁻¹ := by
      have hdiff : ‖A - A'‖ ≤ e := by simpa [norm_sub_rev] using hpert
      have hleft : ‖A'⁻¹‖ * ‖A - A'‖ ≤ (2 / eta) * e :=
        mul_le_mul hinvA' hdiff (norm_nonneg _) (div_nonneg (by norm_num) heta.le)
      exact mul_le_mul hleft hinvA (norm_nonneg _)
        (mul_nonneg (div_nonneg (by norm_num) heta.le) he)
    _ = 2 * e / eta ^ 2 := by field_simp [heta.ne']

/-- Given reference and perturbed numerator and denominator contractions,
positive denominator, numerator, and error margins, a denominator
singular-value bound, a numerator norm bound, numerator and denominator
perturbation bounds, and a small-error condition, the two right
generalized-eigenvalue pencils are invertible where required and differ by the explicit Lipschitz
bound. Under [the listed assumptions](hyp:heta,hLambda,he,hsv,hnumer,hnumPert,hdenPert,hsmall), [the stated conclusion follows](goal). -/
-- Proof route: add and subtract `Aw * Au'⁻¹`, then combine the numerator perturbation with the
-- inverse-difference bound and `‖Aw‖ ≤ n Lambda`; use `Matrix.l2_opNorm_mul` throughout.
theorem rightPencil_perturbation_bound {n : ℕ} [NeZero n]
    (Aw Au Aw' Au' : Matrix (Fin n) (Fin n) ℝ) {eta Lambda e : ℝ}
    (heta : 0 < eta) (hLambda : 0 ≤ Lambda) (he : 0 ≤ e)
    (hsv : eta ≤ leastColumnSingularValue Au)
    (hnumer : squareOperatorNorm Aw ≤ n * Lambda)
    (hnumPert : squareOperatorNorm (Aw' - Aw) ≤ e)
    (hdenPert : squareOperatorNorm (Au' - Au) ≤ e)
    (hsmall : e < eta / 2) :
    IsUnit Au.det ∧ IsUnit Au'.det ∧
      squareOperatorNorm (rightPencil Aw' Au' - rightPencil Aw Au) ≤
        pencilPerturbationConstant n eta Lambda * e := by
  obtain ⟨hdetAu, _⟩ := inverse_operatorNorm_le_reciprocal Au heta hsv
  obtain ⟨hdetAu', hinvAu', hdiffInv⟩ :=
    inverse_perturbation_bound Au Au' heta he hsv hdenPert hsmall
  change ‖Aw‖ ≤ n * Lambda at hnumer
  change ‖Aw' - Aw‖ ≤ e at hnumPert
  change ‖Au'⁻¹‖ ≤ 2 / eta at hinvAu'
  change ‖Au'⁻¹ - Au⁻¹‖ ≤ 2 * e / eta ^ 2 at hdiffInv
  refine ⟨hdetAu, hdetAu', ?_⟩
  change ‖Aw' * Au'⁻¹ - Aw * Au⁻¹‖ ≤
    (2 / eta + 2 * n * Lambda / eta ^ 2) * e
  have hsplit : Aw' * Au'⁻¹ - Aw * Au⁻¹ =
      (Aw' - Aw) * Au'⁻¹ + Aw * (Au'⁻¹ - Au⁻¹) := by
    noncomm_ring
  rw [hsplit]
  calc
    ‖(Aw' - Aw) * Au'⁻¹ + Aw * (Au'⁻¹ - Au⁻¹)‖ ≤
        ‖(Aw' - Aw) * Au'⁻¹‖ + ‖Aw * (Au'⁻¹ - Au⁻¹)‖ := norm_add_le _ _
    _ ≤ ‖Aw' - Aw‖ * ‖Au'⁻¹‖ + ‖Aw‖ * ‖Au'⁻¹ - Au⁻¹‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ e * (2 / eta) + (n * Lambda) * (2 * e / eta ^ 2) := by
      apply add_le_add
      · exact mul_le_mul hnumPert hinvAu' (norm_nonneg _)
          he
      · exact mul_le_mul hnumer hdiffInv (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg n) hLambda)
    _ = (2 / eta + 2 * n * Lambda / eta ^ 2) * e := by ring

/-- Exact contracted factorizations produce a simultaneous diagonalization of every right
pencil, with diagonal entries equal to probe-loading ratios. Under [the listed assumptions](hyp:hS,hload), [the stated conclusion follows](goal). -/
-- Proof route: use determinant-unit closure for `S`, `S.transpose`, and the nonzero diagonal
-- core, expand the nonsingular inverse of a product, cancel `S.transpose`, and check the
-- remaining diagonal identity entrywise with `Matrix.diagonal_mul_diagonal`.
theorem rightPencil_eq_diagonalization {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (lam den num : Fin n → ℝ)
    (hS : IsUnit S.det) (hload : ∀ j, lam j * den j ≠ 0) :
    rightPencil
      (S * Matrix.diagonal (fun j => lam j * num j) * S.transpose)
      (S * Matrix.diagonal (fun j => lam j * den j) * S.transpose) =
        S * Matrix.diagonal (fun j => num j / den j) * S⁻¹ := by
  let Dnum := Matrix.diagonal (fun j => lam j * num j)
  let Dden := Matrix.diagonal (fun j => lam j * den j)
  let Drat := Matrix.diagonal (fun j => num j / den j)
  have hSt : IsUnit S.transpose.det := Matrix.isUnit_det_transpose S hS
  have hdiag : Dnum * Dden⁻¹ = Drat := by
    let f : Fin n → ℝ := fun j => lam j * den j
    have hf : IsUnit f := Pi.isUnit_iff.mpr fun j =>
      isUnit_iff_ne_zero.mpr (hload j)
    obtain ⟨u, hu⟩ := hf
    have hinvf : Ring.inverse f = ↑u⁻¹ := by
      rw [← hu, Ring.inverse_unit]
    rw [Matrix.inv_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    have hlam : lam j ≠ 0 := left_ne_zero_of_mul (hload j)
    have hden : den j ≠ 0 := right_ne_zero_of_mul (hload j)
    have hcancel : f j * Ring.inverse f j = 1 := by
      rw [hinvf, ← hu]
      exact congrFun u.val_inv j
    have hinv_entry : Ring.inverse f j = (f j)⁻¹ := by
      apply mul_left_cancel₀ (hload j)
      rw [hcancel, mul_inv_cancel₀ (hload j)]
    change lam j * num j * Ring.inverse f j = num j / den j
    rw [hinv_entry]
    dsimp only [f]
    field_simp [hlam, hden]
  change (S * Dnum * S.transpose) * (S * Dden * S.transpose)⁻¹ = S * Drat * S⁻¹
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S.transpose S.transpose⁻¹,
    Matrix.mul_nonsing_inv S.transpose hSt, Matrix.one_mul]
  rw [← Matrix.mul_assoc Dnum Dden⁻¹, hdiag]

end Causalean.Mathlib.Analysis.SymmetricTensorPencil
