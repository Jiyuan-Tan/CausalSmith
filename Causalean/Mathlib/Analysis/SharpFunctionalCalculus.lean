module
public import Causalean.Mathlib.Analysis.DiagonalizableFunctionalCalculus

/-!
# Lipschitz perturbation of the functional calculus for two diagonalizable matrices

For two real n × n matrices A and B, each with a chosen real diagonalization, and a 1-Lipschitz
scalar function f, the matrices f(A) and f(B) satisfy ‖f(A) − f(B)‖ ≤ √n·κ_A·κ_B·‖A − B‖ in
operator norm, where κ_A and κ_B bound the condition numbers of the two diagonalizing bases. The
proof writes f(A) − f(B) as a Hadamard product of divided differences of f with the perturbation
A − B expressed between the two eigenbases; the divided difference is set to zero where an
eigenvalue of A coincides with one of B, so no spectral separation is assumed.

## Main definitions

* `crossDividedDifference` — the matrix of divided differences (f(λ_i) − f(μ_j))/(λ_i − μ_j)
  between eigenvalues of A and of B, zero where λ_i = μ_j.
* `crossPerturbation`, `crossHadamard` — A − B written between the two eigenbases, and its
  entrywise product with the divided differences.

## Main results

* `applyFunction_sub_eq_crossHadamard` — f(A) − f(B) is the cross Hadamard matrix conjugated by
  the two bases.
* `norm_applyFunction_sub_le_sqrt_dim` — the √n·κ_A·κ_B·‖A − B‖ perturbation bound.
* `abs_anchorEval_applyFunction_sub_le_sqrt_dim` — the resulting bound on the difference of the
  bilinear evaluations ⟨a, f(A)c⟩ and ⟨b, f(B)d⟩, when f(0) = 0 and both spectra lie in [−R, R].
* `matrix_norm_le_sqrt_card_mul_of_column_norm_le` — a matrix whose columns have Euclidean norm
  at most M has operator norm at most √(number of columns)·M.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- A columnwise Euclidean envelope controls the operator norm with only the square root of the
number of columns. -/
lemma matrix_norm_le_sqrt_card_mul_of_column_norm_le
    {rows cols : ℕ} (A : RectMatrix rows cols) {M : ℝ} (hM : 0 ≤ M)
    (hcol : ∀ j, ‖(WithLp.toLp 2 (fun i => A i j) : Euc rows)‖ ≤ M) :
    ‖A‖ ≤ Real.sqrt cols * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hM)
  intro x
  let c : Fin cols → Euc rows := fun j => WithLp.toLp 2 (fun i => A i j)
  have haction : Matrix.toEuclideanLin A x = ∑ j, x j • c j := by
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, c, mul_comm]
  change ‖Matrix.toEuclideanLin A x‖ ≤ _
  rw [haction]
  calc
    ‖∑ j, x j • c j‖ ≤ ∑ j, ‖x j • c j‖ := norm_sum_le Finset.univ _
    _ ≤ ∑ j, |x j| * M := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hcol j) (abs_nonneg _)
    _ = M * ∑ j, |x j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ M * (Real.sqrt cols * ‖x‖) := by
      gcongr
      let one : Euc cols := WithLp.toLp 2 (fun _ => (1 : ℝ))
      let ax : Euc cols := WithLp.toLp 2 (fun j => |x j|)
      have hinner : ∑ j, |x j| = inner ℝ one ax := by
        simp [one, ax, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      rw [hinner]
      calc
        inner ℝ one ax ≤ |inner ℝ one ax| := le_abs_self _
        _ ≤ ‖one‖ * ‖ax‖ := abs_real_inner_le_norm _ _
        _ = Real.sqrt cols * ‖x‖ := by
          congr 1
          · rw [EuclideanSpace.norm_eq]
            simp [one]
          · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
            simp [ax, Real.norm_eq_abs]
    _ = (Real.sqrt cols * M) * ‖x‖ := by ring

/-- The collision-safe divided-difference matrix of a scalar function for two real
diagonalizations: its (i, j) entry is the divided difference (f(λᵢ) − f(μⱼ))/(λᵢ − μⱼ) of the
i-th eigenvalue λᵢ of the first diagonalization and the j-th eigenvalue μⱼ of the second, and
is zero when the two eigenvalues coincide. -/
noncomputable def crossDividedDifference {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) (f : ℝ → ℝ) :
    RectMatrix n n := fun i j =>
  if DA.eigenvalue i = DB.eigenvalue j then 0
  else (f (DA.eigenvalue i) - f (DB.eigenvalue j)) /
    (DA.eigenvalue i - DB.eigenvalue j)

/-- The difference A − B of two diagonalized matrices written in cross coordinates: the
inverse eigenbasis of the first diagonalization times A − B times the eigenbasis of the
second diagonalization. -/
noncomputable def crossPerturbation {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) : RectMatrix n n :=
  DA.basisInv * (A - B) * DB.basis

/-- [Two real diagonalizations and a scalar function](hyp:n,A,B,DA,DB,f) determine [their entrywise divided-difference perturbation matrix](goal). -/
noncomputable def crossHadamard {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) (f : ℝ → ℝ) :
    RectMatrix n n := fun i j =>
  crossDividedDifference DA DB f i j * crossPerturbation DA DB i j

/-- [Two real diagonalizations and coordinate indices](hyp:n,A,B,DA,DB,i,j) give [the eigenvalue-difference formula for one cross-coordinate perturbation](goal). -/
lemma crossPerturbation_entry
    {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) (i j : Fin n) :
    crossPerturbation DA DB i j =
      (DA.eigenvalue i - DB.eigenvalue j) * (DA.basisInv * DB.basis) i j := by
  have hA : DA.basisInv * A * DB.basis =
      Matrix.diagonal DA.eigenvalue * (DA.basisInv * DB.basis) := by
    have hr := congrArg (fun X : RectMatrix n n => DA.basisInv * X * DB.basis)
      DA.reconstruct
    calc
      _ = DA.basisInv * (DA.basis * Matrix.diagonal DA.eigenvalue * DA.basisInv) *
          DB.basis := hr
      _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc DA.basisInv DA.basis, DA.inv_mul_basis,
          Matrix.one_mul]
  have hB : DA.basisInv * B * DB.basis =
      (DA.basisInv * DB.basis) * Matrix.diagonal DB.eigenvalue := by
    have hr := congrArg (fun X : RectMatrix n n => DA.basisInv * X * DB.basis)
      DB.reconstruct
    calc
      _ = DA.basisInv * (DB.basis * Matrix.diagonal DB.eigenvalue * DB.basisInv) *
          DB.basis := hr
      _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [DB.inv_mul_basis, Matrix.mul_one]
  have hE : crossPerturbation DA DB =
      Matrix.diagonal DA.eigenvalue * (DA.basisInv * DB.basis) -
        (DA.basisInv * DB.basis) * Matrix.diagonal DB.eigenvalue := by
    unfold crossPerturbation
    rw [Matrix.mul_sub, Matrix.sub_mul, hA, hB]
  rw [hE]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]
  ring

/-- [Two real diagonalizations and a scalar function](hyp:n,A,B,DA,DB,f) give [the factorization of their functional-calculus difference through the cross Hadamard matrix](goal). -/
lemma applyFunction_sub_eq_crossHadamard
    {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) (f : ℝ → ℝ) :
    DA.applyFunction f - DB.applyFunction f =
      DA.basis * crossHadamard DA DB f * DB.basisInv := by
  let C := DA.basisInv * DB.basis
  let H : RectMatrix n n := fun i j =>
    crossDividedDifference DA DB f i j * crossPerturbation DA DB i j
  have hH (i j : Fin n) : H i j =
      (f (DA.eigenvalue i) - f (DB.eigenvalue j)) * C i j := by
    dsimp [H, crossDividedDifference]
    rw [crossPerturbation_entry DA DB]
    by_cases hij : DA.eigenvalue i = DB.eigenvalue j
    · simp [hij]
    · rw [if_neg hij]
      field_simp [sub_ne_zero.mpr hij]
      rfl
  have hcoord : H = Matrix.diagonal (f ∘ DA.eigenvalue) * C -
      C * Matrix.diagonal (f ∘ DB.eigenvalue) := by
    ext i j
    rw [hH]
    simp [C, Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply]
    ring
  unfold RealDiagonalization.applyFunction
  change _ = DA.basis * H * DB.basisInv
  rw [show DA.basis * H * DB.basisInv =
      DA.basis * (Matrix.diagonal (f ∘ DA.eigenvalue) * C) * DB.basisInv -
        DA.basis * (C * Matrix.diagonal (f ∘ DB.eigenvalue)) * DB.basisInv by
      rw [hcoord, Matrix.mul_sub, Matrix.sub_mul]]
  dsimp [C]
  simp only [Matrix.mul_assoc]
  rw [DB.basis_mul_inv, Matrix.mul_one,
    ← Matrix.mul_assoc DA.basis DA.basisInv, DA.basis_mul_inv, Matrix.one_mul]

/-- [A matrix dimension and two real matrices](hyp:n,A,B), [their real diagonalizations](hyp:DA,DB), [a one-Lipschitz scalar function](hyp:f,hf), and [condition-number bounds](hyp:κA,κB,hκA,hκB) give [the perturbation bound: the operator norm of the difference of the function applied to the two matrices through their diagonalizations is at most √n·κA·κB times the operator norm of A − B](goal). -/
theorem norm_applyFunction_sub_le_sqrt_dim
    {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f) {κA κB : ℝ}
    (hκA : DA.conditionNumber ≤ κA) (hκB : DB.conditionNumber ≤ κB) :
    ‖DA.applyFunction f - DB.applyFunction f‖ ≤
      Real.sqrt n * κA * κB * ‖A - B‖ := by
  let E := crossPerturbation DA DB
  let H : RectMatrix n n := fun i j => crossDividedDifference DA DB f i j * E i j
  have hcoef (i j : Fin n) : |crossDividedDifference DA DB f i j| ≤ 1 := by
    unfold crossDividedDifference
    by_cases hij : DA.eigenvalue i = DB.eigenvalue j
    · simp [hij]
    · rw [if_neg hij, abs_div]
      exact (div_le_one (abs_pos.mpr (sub_ne_zero.mpr hij))).2 (by
        simpa [Real.norm_eq_abs] using hf.norm_sub_le
          (DA.eigenvalue i) (DB.eigenvalue j))
  have hcol (j : Fin n) :
      ‖(WithLp.toLp 2 (fun i => H i j) : Euc n)‖ ≤ ‖E‖ := by
    have hsq : ∑ i, (H i j) ^ 2 ≤ ∑ i, (E i j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [H]
      have hc2 : (crossDividedDifference DA DB f i j) ^ 2 ≤ 1 := by
        have hc := abs_le.mp (hcoef i j)
        nlinarith
      rw [mul_pow]
      simpa using mul_le_mul_of_nonneg_right hc2 (sq_nonneg (E i j))
    have hcolE := Matrix.l2_opNorm_mulVec E (EuclideanSpace.single j (1 : ℝ))
    rw [EuclideanSpace.norm_single, norm_one, mul_one] at hcolE
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i, (E i j) ^ 2 := hsq
      _ = ‖Matrix.toEuclideanLin E (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]
      _ ≤ ‖E‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hcolE
  have hH : ‖H‖ ≤ Real.sqrt n * ‖E‖ :=
    matrix_norm_le_sqrt_card_mul_of_column_norm_le H (norm_nonneg _) hcol
  rw [applyFunction_sub_eq_crossHadamard DA DB f]
  change ‖DA.basis * H * DB.basisInv‖ ≤ _
  have hE : ‖E‖ ≤ ‖DA.basisInv‖ * ‖A - B‖ * ‖DB.basis‖ := by
    exact (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
  have hκA0 : 0 ≤ κA := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hκA
  have hκB0 : 0 ≤ κB := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hκB
  calc
    ‖DA.basis * H * DB.basisInv‖ ≤ ‖DA.basis‖ * ‖H‖ * ‖DB.basisInv‖ := by
      exact (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖DA.basis‖ * (Real.sqrt n * ‖E‖) * ‖DB.basisInv‖ := by gcongr
    _ ≤ ‖DA.basis‖ * (Real.sqrt n *
        (‖DA.basisInv‖ * ‖A - B‖ * ‖DB.basis‖)) * ‖DB.basisInv‖ := by gcongr
    _ = Real.sqrt n * DA.conditionNumber * DB.conditionNumber * ‖A - B‖ := by
      unfold RealDiagonalization.conditionNumber
      ring
    _ ≤ Real.sqrt n * κA * κB * ‖A - B‖ := by
      have hp : DA.conditionNumber * DB.conditionNumber ≤ κA * κB :=
        mul_le_mul hκA hκB
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hκA0
      have := mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg n)
      exact mul_le_mul_of_nonneg_right (by simpa [mul_assoc] using this) (norm_nonneg _)

/-- Anchored form of the sharp collision-safe two-diagonalizer estimate. -/
theorem abs_anchorEval_applyFunction_sub_le_sqrt_dim
    {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B)
    (a b c d : Euc n) (f : ℝ → ℝ) (hf : LipschitzWith 1 f) (hf0 : f 0 = 0)
    {κA κB R : ℝ} (hκA : DA.conditionNumber ≤ κA)
    (hκB : DB.conditionNumber ≤ κB) (hR0 : 0 ≤ R)
    (hRA : DA.SpectrumBound R) (hRB : DB.SpectrumBound R) :
    |anchorEval a c (DA.applyFunction f) - anchorEval b d (DB.applyFunction f)| ≤
      ‖a - b‖ * (κA * R) * ‖c‖ +
      ‖b‖ * (Real.sqrt n * κA * κB * ‖A - B‖) * ‖c‖ +
      ‖b‖ * (κB * R) * ‖c - d‖ := by
  have hFA := norm_applyFunction_le DA f hf hf0 hκA hR0 hRA
  have hFB := norm_applyFunction_le DB f hf hf0 hκB hR0 hRB
  have hdiff := norm_applyFunction_sub_le_sqrt_dim DA DB f hf hκA hκB
  have hdecomp :
      anchorEval a c (DA.applyFunction f) - anchorEval b d (DB.applyFunction f) =
        anchorEval (a - b) c (DA.applyFunction f) +
        anchorEval b c (DA.applyFunction f - DB.applyFunction f) +
        anchorEval b (c - d) (DB.applyFunction f) := by
    unfold anchorEval matrixCLM
    simp only [map_sub, sub_apply, inner_sub_left, inner_sub_right]
    ring
  rw [hdecomp]
  calc
    |_ + _ + _| ≤ |anchorEval (a - b) c (DA.applyFunction f)| +
        |anchorEval b c (DA.applyFunction f - DB.applyFunction f)| +
        |anchorEval b (c - d) (DB.applyFunction f)| := by
      calc
        |_ + _ + _| ≤ |anchorEval (a - b) c (DA.applyFunction f) +
            anchorEval b c (DA.applyFunction f - DB.applyFunction f)| +
            |anchorEval b (c - d) (DB.applyFunction f)| := abs_add_le _ _
        _ ≤ _ := by gcongr; exact abs_add_le _ _
    _ ≤ (‖a - b‖ * ‖DA.applyFunction f‖ * ‖c‖) +
        (‖b‖ * ‖DA.applyFunction f - DB.applyFunction f‖ * ‖c‖) +
        (‖b‖ * ‖DB.applyFunction f‖ * ‖c - d‖) := by
      gcongr
      · exact abs_anchorEval_le _ _ _
      · exact abs_anchorEval_le _ _ _
      · exact abs_anchorEval_le _ _ _
    _ ≤ _ := by gcongr

end

end Causalean.Mathlib.Analysis
