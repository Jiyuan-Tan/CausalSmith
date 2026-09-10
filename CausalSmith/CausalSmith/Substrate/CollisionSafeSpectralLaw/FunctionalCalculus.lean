import CausalSmith.Substrate.CollisionSafeSpectralLaw.Basic

/-!
# Collision-safe two-diagonalizer functional calculus

This module treats separately diagonalized real matrices, including nonnormal matrices and
arbitrary eigenvalue multiplicities.  Equal eigenvalues are aggregated into canonical spectral
projectors.  The cross-projector identity makes common-eigenvalue summands vanish before any
divided difference is formed, yielding a gap-free two-diagonalizer bound.
-/

namespace CausalSmith.Substrate.CollisionSafeSpectralLaw

open scoped BigOperators Matrix.Norms.L2Operator

/-- A real diagonalization certificate `A = S diag(α) S⁻¹`, carrying both inverse identities. -/
structure RealDiagonalization {n : ℕ} (A : RectMatrix n n) where
  basis : RectMatrix n n
  basisInv : RectMatrix n n
  eigenvalue : Fin n → ℝ
  basis_mul_inv : basis * basisInv = 1
  inv_mul_basis : basisInv * basis = 1
  reconstruct : A = basis * Matrix.diagonal eigenvalue * basisInv

/-- The finite set of distinct real eigenvalues in a diagonalization certificate. -/
noncomputable def RealDiagonalization.spectralValues {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) : Finset ℝ :=
  Finset.univ.image D.eigenvalue

/-- The number of distinct real eigenvalues in a diagonalization certificate. -/
noncomputable def RealDiagonalization.specCount {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) : ℕ :=
  D.spectralValues.card

/-- The condition number certificate `‖S‖ ‖S⁻¹‖` of a chosen diagonalizer. -/
noncomputable def RealDiagonalization.conditionNumber {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) : ℝ :=
  ‖D.basis‖ * ‖D.basisInv‖

/-- The aggregate spectral projector at a value, summing every diagonal coordinate whose
eigenvalue equals that value. -/
noncomputable def RealDiagonalization.projector {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) (x : ℝ) : RectMatrix n n :=
  D.basis * Matrix.diagonal (fun i => if D.eigenvalue i = x then 1 else 0) * D.basisInv

/-- Applying a scalar function through a real diagonalization certificate. -/
noncomputable def RealDiagonalization.applyFunction {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) (f : ℝ → ℝ) : RectMatrix n n :=
  D.basis * Matrix.diagonal (f ∘ D.eigenvalue) * D.basisInv

private lemma diagonal_intertwine {n : ℕ} {A : RectMatrix n n}
    (D D' : RealDiagonalization A) :
    Matrix.diagonal D.eigenvalue * (D.basisInv * D'.basis) =
      (D.basisInv * D'.basis) * Matrix.diagonal D'.eigenvalue := by
  calc
    Matrix.diagonal D.eigenvalue * (D.basisInv * D'.basis) =
        (D.basisInv * D.basis) * Matrix.diagonal D.eigenvalue *
          (D.basisInv * D'.basis) := by rw [D.inv_mul_basis, Matrix.one_mul]
    _ =
        D.basisInv * (D.basis * Matrix.diagonal D.eigenvalue * D.basisInv) *
          D'.basis := by simp only [Matrix.mul_assoc]
    _ = D.basisInv *
        (D'.basis * Matrix.diagonal D'.eigenvalue * D'.basisInv) * D'.basis := by
          rw [← D.reconstruct, ← D'.reconstruct]
    _ = (D.basisInv * D'.basis) * Matrix.diagonal D'.eigenvalue := by
          simp only [Matrix.mul_assoc, D'.inv_mul_basis, Matrix.mul_one]

private lemma function_diagonal_intertwine {n : ℕ} {A : RectMatrix n n}
    (D D' : RealDiagonalization A) (f : ℝ → ℝ) :
    Matrix.diagonal (f ∘ D.eigenvalue) * (D.basisInv * D'.basis) =
      (D.basisInv * D'.basis) * Matrix.diagonal (f ∘ D'.eigenvalue) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : D.eigenvalue i = D'.eigenvalue j
  · simp [Function.comp_apply, hij, mul_comm]
  · have hentry := congrArg (fun M : RectMatrix n n => M i j)
        (diagonal_intertwine D D')
    have hzero : (D.basisInv * D'.basis) i j = 0 := by
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
      have : (D.eigenvalue i - D'.eigenvalue j) *
          (D.basisInv * D'.basis) i j = 0 := by nlinarith
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hij)
    simp [hzero]

private lemma applyFunction_independent_aux {n : ℕ} {A : RectMatrix n n}
    (D D' : RealDiagonalization A) (f : ℝ → ℝ) :
    D.applyFunction f = D'.applyFunction f := by
  unfold RealDiagonalization.applyFunction
  calc
    D.basis * Matrix.diagonal (f ∘ D.eigenvalue) * D.basisInv =
        D.basis * Matrix.diagonal (f ∘ D.eigenvalue) *
          (D.basisInv * D'.basis) * D'.basisInv := by
            simp only [Matrix.mul_assoc, D'.basis_mul_inv, Matrix.mul_one]
    _ = D.basis * (D.basisInv * D'.basis) *
          Matrix.diagonal (f ∘ D'.eigenvalue) * D'.basisInv := by
            calc
              D.basis * Matrix.diagonal (f ∘ D.eigenvalue) *
                    (D.basisInv * D'.basis) * D'.basisInv =
                  D.basis * (Matrix.diagonal (f ∘ D.eigenvalue) *
                    (D.basisInv * D'.basis)) * D'.basisInv := by
                      simp only [Matrix.mul_assoc]
              _ = D.basis * ((D.basisInv * D'.basis) *
                    Matrix.diagonal (f ∘ D'.eigenvalue)) * D'.basisInv := by
                      rw [function_diagonal_intertwine D D' f]
              _ = _ := by simp only [Matrix.mul_assoc]
    _ = D'.basis * Matrix.diagonal (f ∘ D'.eigenvalue) * D'.basisInv := by
          simp only [← Matrix.mul_assoc, D.basis_mul_inv, Matrix.one_mul]

/-- Aggregate projectors are independent of the eigenbasis and of coordinate choices within
repeated eigenspaces. -/
theorem projector_independent {n : ℕ} {A : RectMatrix n n}
    (D D' : RealDiagonalization A) (x : ℝ) :
    D.projector x = D'.projector x := by
  simpa [RealDiagonalization.projector, RealDiagonalization.applyFunction,
    Function.comp_def] using
    applyFunction_independent_aux D D' (fun z => if z = x then 1 else 0)

/-- Finite functional calculus is independent of the chosen real diagonalization certificate. -/
theorem applyFunction_independent {n : ℕ} {A : RectMatrix n n}
    (D D' : RealDiagonalization A) (f : ℝ → ℝ) :
    D.applyFunction f = D'.applyFunction f := by
  exact applyFunction_independent_aux D D' f

/-- The aggregate spectral projectors sum to the identity. -/
theorem sum_projector_eq_one {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) :
    ∑ x ∈ D.spectralValues, D.projector x = 1 := by
  unfold RealDiagonalization.projector RealDiagonalization.spectralValues
  rw [← Finset.sum_mul, ← Matrix.mul_sum]
  have hdiag : (∑ x ∈ Finset.univ.image D.eigenvalue,
      Matrix.diagonal (fun i => if D.eigenvalue i = x then 1 else 0)) =
      (1 : RectMatrix n n) := by
    funext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  change D.basis * (∑ x ∈ Finset.univ.image D.eigenvalue,
      Matrix.diagonal (fun i => if D.eigenvalue i = x then 1 else 0)) * D.basisInv = 1
  rw [hdiag, Matrix.mul_one]
  exact D.basis_mul_inv

/-- Functional calculus is the sum of the scalar values times aggregate spectral projectors. -/
theorem applyFunction_eq_sum_projector {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) (f : ℝ → ℝ) :
    D.applyFunction f = ∑ x ∈ D.spectralValues, f x • D.projector x := by
  unfold RealDiagonalization.applyFunction RealDiagonalization.projector
  have hdiag : Matrix.diagonal (f ∘ D.eigenvalue) =
      ∑ x ∈ D.spectralValues, f x •
        Matrix.diagonal (fun i => if D.eigenvalue i = x then 1 else 0) := by
    funext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      simp [RealDiagonalization.spectralValues, Function.comp_apply]
    · simp [hij]
  rw [hdiag]
  simp [Finset.mul_sum, Finset.sum_mul]

/-- An aggregate projector extracts its own eigenvalue on either side of its operator. -/
theorem projector_mul_operator {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) {x : ℝ} (hx : x ∈ D.spectralValues) :
    D.projector x * A = x • D.projector x ∧
      A * D.projector x = x • D.projector x := by
  have _ := hx
  let E : RectMatrix n n :=
    Matrix.diagonal (fun i => if D.eigenvalue i = x then (1 : ℝ) else 0)
  let L : RectMatrix n n := Matrix.diagonal D.eigenvalue
  have hEL : E * L = x • E := by
    funext i j
    by_cases hij : i = j
    · subst j
      by_cases hix : D.eigenvalue i = x <;> simp [E, L, hix]
    · simp [E, L, hij]
  have hLE : L * E = x • E := by
    funext i j
    by_cases hij : i = j
    · subst j
      by_cases hix : D.eigenvalue i = x <;> simp [E, L, hix]
    · simp [E, L, hij]
  constructor
  · calc
      D.projector x * A =
          D.projector x * (D.basis * L * D.basisInv) := by
            exact congrArg (fun M => D.projector x * M) D.reconstruct
      _ = (D.basis * E * D.basisInv) * (D.basis * L * D.basisInv) := by rfl
      _ = D.basis * (E * L) * D.basisInv := by
        rw [Matrix.mul_assoc (D.basis * E) D.basisInv,
          Matrix.mul_assoc D.basis L,
          ← Matrix.mul_assoc D.basisInv D.basis, D.inv_mul_basis,
          Matrix.one_mul]
        simp only [Matrix.mul_assoc]
      _ = D.basis * (x • E) * D.basisInv := by rw [hEL]
      _ = x • (D.basis * E * D.basisInv) := by simp
      _ = x • D.projector x := by rfl
  · calc
      A * D.projector x =
          (D.basis * L * D.basisInv) * D.projector x := by
            exact congrArg (fun M => M * D.projector x) D.reconstruct
      _ = (D.basis * L * D.basisInv) * (D.basis * E * D.basisInv) := by rfl
      _ =
          D.basis * (L * E) * D.basisInv := by
        rw [Matrix.mul_assoc (D.basis * L) D.basisInv,
          Matrix.mul_assoc D.basis E,
          ← Matrix.mul_assoc D.basisInv D.basis, D.inv_mul_basis,
          Matrix.one_mul]
        simp only [Matrix.mul_assoc]
      _ = D.basis * (x • E) * D.basisInv := by rw [hLE]
      _ = x • (D.basis * E * D.basisInv) := by simp
      _ = x • D.projector x := by rfl

/-- Cross-projecting two separately diagonalized operators gives
`E_λ (A-B) F_γ = (λ-γ) E_λ F_γ`. -/
theorem crossProjector_sub {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B)
    {x y : ℝ} (hx : x ∈ DA.spectralValues) (hy : y ∈ DB.spectralValues) :
    DA.projector x * (A - B) * DB.projector y =
      (x - y) • (DA.projector x * DB.projector y) := by
  have hAx := (projector_mul_operator DA hx).1
  have hBy := (projector_mul_operator DB hy).2
  calc
    DA.projector x * (A - B) * DB.projector y =
        (DA.projector x * A) * DB.projector y -
          DA.projector x * (B * DB.projector y) := by
            simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = (x • DA.projector x) * DB.projector y -
          DA.projector x * (y • DB.projector y) := by rw [hAx, hBy]
    _ = (x - y) • (DA.projector x * DB.projector y) := by
          simp [sub_smul]

/-- At a common eigenvalue the cross-projected perturbation vanishes, so the corresponding
divided-difference summand is zero without division by `λ-γ`. -/
theorem crossProjector_common_eigenvalue_vanish {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B)
    {x : ℝ} (hAx : x ∈ DA.spectralValues) (hBx : x ∈ DB.spectralValues) :
    DA.projector x * (A - B) * DB.projector x = 0 := by
  rw [crossProjector_sub DA DB hAx hBx, sub_self, zero_smul]

/-- Collision-safe divided-difference expansion for two unrelated diagonalizers.  Equal-node
summands are explicitly zero and therefore never divide by zero. -/
theorem applyFunction_sub_eq_dividedDifference {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B) (f : ℝ → ℝ) :
    DA.applyFunction f - DB.applyFunction f =
      ∑ x ∈ DA.spectralValues, ∑ y ∈ DB.spectralValues,
        if x = y then 0 else
          ((f x - f y) / (x - y)) •
            (DA.projector x * (A - B) * DB.projector y) := by
  have hsummand (x : ℝ) (hx : x ∈ DA.spectralValues)
      (y : ℝ) (hy : y ∈ DB.spectralValues) :
      (if x = y then 0 else
        ((f x - f y) / (x - y)) •
          (DA.projector x * (A - B) * DB.projector y)) =
        (f x - f y) • (DA.projector x * DB.projector y) := by
    by_cases hxy : x = y
    · subst y
      simp
    · rw [if_neg hxy, crossProjector_sub DA DB hx hy, smul_smul]
      congr 1
      field_simp [sub_ne_zero.mpr hxy]
  rw [applyFunction_eq_sum_projector DA f,
    applyFunction_eq_sum_projector DB f]
  have hfirst :
      (∑ x ∈ DA.spectralValues, f x • DA.projector x) *
          (∑ y ∈ DB.spectralValues, DB.projector y) =
        ∑ x ∈ DA.spectralValues, ∑ y ∈ DB.spectralValues,
          f x • (DA.projector x * DB.projector y) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    simp
  have hsecond :
      (∑ x ∈ DA.spectralValues, DA.projector x) *
          (∑ y ∈ DB.spectralValues, f y • DB.projector y) =
        ∑ x ∈ DA.spectralValues, ∑ y ∈ DB.spectralValues,
          f y • (DA.projector x * DB.projector y) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    simp
  calc
    (∑ x ∈ DA.spectralValues, f x • DA.projector x) -
          ∑ y ∈ DB.spectralValues, f y • DB.projector y =
        (∑ x ∈ DA.spectralValues, f x • DA.projector x) *
            (∑ y ∈ DB.spectralValues, DB.projector y) -
          (∑ x ∈ DA.spectralValues, DA.projector x) *
            (∑ y ∈ DB.spectralValues, f y • DB.projector y) := by
              rw [sum_projector_eq_one DA, sum_projector_eq_one DB,
                Matrix.mul_one, Matrix.one_mul]
    _ = ∑ x ∈ DA.spectralValues, ∑ y ∈ DB.spectralValues,
          (f x - f y) • (DA.projector x * DB.projector y) := by
            rw [hfirst, hsecond]
            simp [← Finset.sum_sub_distrib, sub_smul]
    _ = ∑ x ∈ DA.spectralValues, ∑ y ∈ DB.spectralValues,
          if x = y then 0 else
            ((f x - f y) / (x - y)) •
              (DA.projector x * (A - B) * DB.projector y) := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            exact (hsummand x hx y hy).symm

/-- Every aggregate projector has norm at most the condition number of its diagonalizer. -/
theorem norm_projector_le_conditionNumber {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) (x : ℝ) :
    ‖D.projector x‖ ≤ D.conditionNumber := by
  let E : RectMatrix n n :=
    Matrix.diagonal (fun i => if D.eigenvalue i = x then (1 : ℝ) else 0)
  have hE : ‖E‖ ≤ 1 := by
    rw [show E = Matrix.diagonal
      (fun i => if D.eigenvalue i = x then (1 : ℝ) else 0) from rfl,
      Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    split <;> simp
  unfold RealDiagonalization.projector RealDiagonalization.conditionNumber
  calc
    ‖D.basis * Matrix.diagonal (fun i => if D.eigenvalue i = x then 1 else 0) *
        D.basisInv‖ ≤
      ‖D.basis * Matrix.diagonal (fun i => if D.eigenvalue i = x then 1 else 0)‖ *
        ‖D.basisInv‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖D.basis‖ *
        ‖Matrix.diagonal (fun i => if D.eigenvalue i = x then (1 : ℝ) else 0)‖) *
        ‖D.basisInv‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul D.basis
            (Matrix.diagonal (fun i => if D.eigenvalue i = x then (1 : ℝ) else 0))
    _ ≤ (‖D.basis‖ * 1) * ‖D.basisInv‖ := by
          gcongr
    _ = ‖D.basis‖ * ‖D.basisInv‖ := by ring

/-- A one-Lipschitz scalar function obeys the two-diagonalizer, collision-free perturbation
bound with the product of the numbers of distinct eigenvalues. -/
theorem norm_applyFunction_sub_le {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f) {κA κB : ℝ}
    (hκA : DA.conditionNumber ≤ κA) (hκB : DB.conditionNumber ≤ κB) :
    ‖DA.applyFunction f - DB.applyFunction f‖ ≤
      (DA.specCount : ℝ) * (DB.specCount : ℝ) * κA * κB * ‖A - B‖ := by
  have hκA0 : 0 ≤ κA := le_trans
    (mul_nonneg (norm_nonneg DA.basis) (norm_nonneg DA.basisInv)) hκA
  have hκB0 : 0 ≤ κB := le_trans
    (mul_nonneg (norm_nonneg DB.basis) (norm_nonneg DB.basisInv)) hκB
  have hsummand (x : ℝ) (hx : x ∈ DA.spectralValues)
      (y : ℝ) (hy : y ∈ DB.spectralValues) :
      ‖if x = y then 0 else
        ((f x - f y) / (x - y)) •
          (DA.projector x * (A - B) * DB.projector y)‖ ≤
        κA * κB * ‖A - B‖ := by
    by_cases hxy : x = y
    · rw [if_pos hxy, norm_zero]
      positivity
    · rw [if_neg hxy, norm_smul]
      have hcoef : ‖(f x - f y) / (x - y)‖ ≤ 1 := by
        rw [norm_div]
        apply (div_le_one (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).2
        simpa using hf.norm_sub_le x y
      have htriple :
          ‖DA.projector x * (A - B) * DB.projector y‖ ≤
            κA * κB * ‖A - B‖ := by
        calc
          ‖DA.projector x * (A - B) * DB.projector y‖ ≤
              ‖DA.projector x * (A - B)‖ * ‖DB.projector y‖ :=
                Matrix.l2_opNorm_mul _ _
          _ ≤ (‖DA.projector x‖ * ‖A - B‖) * ‖DB.projector y‖ := by
                gcongr
                exact Matrix.l2_opNorm_mul _ _
          _ ≤ (κA * ‖A - B‖) * κB := by
                gcongr
                · exact le_trans (norm_projector_le_conditionNumber DA x) hκA
                · exact le_trans (norm_projector_le_conditionNumber DB y) hκB
          _ = κA * κB * ‖A - B‖ := by ring
      calc
        ‖(f x - f y) / (x - y)‖ *
            ‖DA.projector x * (A - B) * DB.projector y‖ ≤
          1 * (κA * κB * ‖A - B‖) := by gcongr
        _ = κA * κB * ‖A - B‖ := one_mul _
  rw [applyFunction_sub_eq_dividedDifference DA DB f]
  calc
    ‖∑ x ∈ DA.spectralValues, ∑ y ∈ DB.spectralValues,
        if x = y then 0 else
          ((f x - f y) / (x - y)) •
            (DA.projector x * (A - B) * DB.projector y)‖ ≤
      ∑ x ∈ DA.spectralValues, ‖∑ y ∈ DB.spectralValues,
        if x = y then 0 else
          ((f x - f y) / (x - y)) •
            (DA.projector x * (A - B) * DB.projector y)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ DA.spectralValues, ∑ y ∈ DB.spectralValues,
        ‖if x = y then 0 else
          ((f x - f y) / (x - y)) •
            (DA.projector x * (A - B) * DB.projector y)‖ := by
          apply Finset.sum_le_sum
          intro x hx
          exact norm_sum_le _ _
    _ ≤ ∑ x ∈ DA.spectralValues, ∑ y ∈ DB.spectralValues,
        κA * κB * ‖A - B‖ := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          exact hsummand x hx y hy
    _ = (DA.specCount : ℝ) * (DB.specCount : ℝ) * κA * κB * ‖A - B‖ := by
          simp [RealDiagonalization.specCount]
          ring

/-- The distinct-spectrum bound is at most the corresponding dimension-squared bound. -/
theorem norm_applyFunction_sub_le_dim_sq {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f) {κA κB : ℝ}
    (hκA : DA.conditionNumber ≤ κA) (hκB : DB.conditionNumber ≤ κB) :
    ‖DA.applyFunction f - DB.applyFunction f‖ ≤
      (n : ℝ) ^ 2 * κA * κB * ‖A - B‖ := by
  have hcountA : (DA.specCount : ℝ) ≤ n := by
    unfold RealDiagonalization.specCount RealDiagonalization.spectralValues
    exact_mod_cast (show (Finset.univ.image DA.eigenvalue).card ≤ n by
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
        (f := DA.eigenvalue)))
  have hcountB : (DB.specCount : ℝ) ≤ n := by
    unfold RealDiagonalization.specCount RealDiagonalization.spectralValues
    exact_mod_cast (show (Finset.univ.image DB.eigenvalue).card ≤ n by
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
        (f := DB.eigenvalue)))
  have hκA0 : 0 ≤ κA := le_trans
    (mul_nonneg (norm_nonneg DA.basis) (norm_nonneg DA.basisInv)) hκA
  have hκB0 : 0 ≤ κB := le_trans
    (mul_nonneg (norm_nonneg DB.basis) (norm_nonneg DB.basisInv)) hκB
  calc
    ‖DA.applyFunction f - DB.applyFunction f‖ ≤
        (DA.specCount : ℝ) * (DB.specCount : ℝ) * κA * κB * ‖A - B‖ :=
      norm_applyFunction_sub_le DA DB f hf hκA hκB
    _ ≤ (n : ℝ) * (n : ℝ) * κA * κB * ‖A - B‖ := by gcongr
    _ = (n : ℝ) ^ 2 * κA * κB * ‖A - B‖ := by ring

/-- A diagonalization has spectrum bounded by `R` when all listed real eigenvalues have
absolute value at most `R`. -/
def RealDiagonalization.SpectrumBound {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) (R : ℝ) : Prop :=
  ∀ i, |D.eigenvalue i| ≤ R

/-- If `f(0)=0`, `f` is one-Lipschitz, and the spectrum lies in `[-R,R]`, then functional
calculus has norm at most the diagonalizer condition number times `R`. -/
theorem norm_applyFunction_le {n : ℕ} {A : RectMatrix n n}
    (D : RealDiagonalization A) (f : ℝ → ℝ) (hf : LipschitzWith 1 f)
    (hf0 : f 0 = 0) {κ R : ℝ} (hκ : D.conditionNumber ≤ κ)
    (hR0 : 0 ≤ R) (hR : D.SpectrumBound R) :
    ‖D.applyFunction f‖ ≤ κ * R := by
  have hdiag : ‖Matrix.diagonal (f ∘ D.eigenvalue)‖ ≤ R := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hR0]
    intro i
    calc
      ‖(f ∘ D.eigenvalue) i‖ = ‖f (D.eigenvalue i) - f 0‖ := by
        simp [hf0]
      _ ≤ ‖D.eigenvalue i - 0‖ := by
        simpa using hf.norm_sub_le (D.eigenvalue i) 0
      _ = |D.eigenvalue i| := by simp [Real.norm_eq_abs]
      _ ≤ R := hR i
  unfold RealDiagonalization.applyFunction
  have hcond0 : 0 ≤ D.conditionNumber :=
    mul_nonneg (norm_nonneg D.basis) (norm_nonneg D.basisInv)
  calc
    ‖D.basis * Matrix.diagonal (f ∘ D.eigenvalue) * D.basisInv‖ ≤
        ‖D.basis * Matrix.diagonal (f ∘ D.eigenvalue)‖ * ‖D.basisInv‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖D.basis‖ * ‖Matrix.diagonal (f ∘ D.eigenvalue)‖) *
        ‖D.basisInv‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
    _ ≤ (‖D.basis‖ * R) * ‖D.basisInv‖ := by gcongr
    _ = D.conditionNumber * R := by
          unfold RealDiagonalization.conditionNumber
          ring
    _ ≤ κ * R := mul_le_mul_of_nonneg_right hκ hR0

/-- The left-right evaluation of a matrix between two Euclidean anchor vectors. -/
noncomputable def anchorEval {n : ℕ} (a c : Euc n) (M : RectMatrix n n) : ℝ :=
  inner ℝ a (matrixCLM M c)

/-- A left-right matrix evaluation is bounded by the two anchor norms and the operator norm. -/
theorem abs_anchorEval_le {n : ℕ} (a c : Euc n) (M : RectMatrix n n) :
    |anchorEval a c M| ≤ ‖a‖ * ‖M‖ * ‖c‖ := by
  unfold anchorEval
  calc
    |inner ℝ a (matrixCLM M c)| ≤ ‖a‖ * ‖matrixCLM M c‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖a‖ * (‖matrixCLM M‖ * ‖c‖) := by
      gcongr
      exact (matrixCLM M).le_opNorm c
    _ = ‖a‖ * ‖M‖ * ‖c‖ := by
      rw [show matrixCLM M =
          Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M from rfl,
        Matrix.l2_opNorm_toEuclideanCLM]
      ring

/-- Normalized one-Lipschitz functional calculus is stable under simultaneous operator and
left/right anchor perturbations, without eigenvalue matching or diagonalizer matching. -/
theorem abs_anchorEval_applyFunction_sub_le {n : ℕ} {A B : RectMatrix n n}
    (DA : RealDiagonalization A) (DB : RealDiagonalization B)
    (a b c d : Euc n) (f : ℝ → ℝ) (hf : LipschitzWith 1 f) (hf0 : f 0 = 0)
    {κA κB R : ℝ} (hκA : DA.conditionNumber ≤ κA)
    (hκB : DB.conditionNumber ≤ κB) (hR0 : 0 ≤ R)
    (hRA : DA.SpectrumBound R)
    (hRB : DB.SpectrumBound R) :
    |anchorEval a c (DA.applyFunction f) - anchorEval b d (DB.applyFunction f)| ≤
      ‖a - b‖ * (κA * R) * ‖c‖ +
      ‖b‖ * ((n : ℝ) ^ 2 * κA * κB * ‖A - B‖) * ‖c‖ +
      ‖b‖ * (κB * R) * ‖c - d‖ := by
  have hFA : ‖DA.applyFunction f‖ ≤ κA * R :=
    norm_applyFunction_le DA f hf hf0 hκA hR0 hRA
  have hFB : ‖DB.applyFunction f‖ ≤ κB * R :=
    norm_applyFunction_le DB f hf hf0 hκB hR0 hRB
  have hdiff : ‖DA.applyFunction f - DB.applyFunction f‖ ≤
      (n : ℝ) ^ 2 * κA * κB * ‖A - B‖ :=
    norm_applyFunction_sub_le_dim_sq DA DB f hf hκA hκB
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
    |anchorEval (a - b) c (DA.applyFunction f) +
        anchorEval b c (DA.applyFunction f - DB.applyFunction f) +
        anchorEval b (c - d) (DB.applyFunction f)| ≤
      |anchorEval (a - b) c (DA.applyFunction f)| +
        |anchorEval b c (DA.applyFunction f - DB.applyFunction f)| +
        |anchorEval b (c - d) (DB.applyFunction f)| := by
          calc
            |anchorEval (a - b) c (DA.applyFunction f) +
                anchorEval b c (DA.applyFunction f - DB.applyFunction f) +
                anchorEval b (c - d) (DB.applyFunction f)| ≤
              |anchorEval (a - b) c (DA.applyFunction f) +
                anchorEval b c (DA.applyFunction f - DB.applyFunction f)| +
                |anchorEval b (c - d) (DB.applyFunction f)| := abs_add_le _ _
            _ ≤ _ := by
              gcongr
              exact abs_add_le _ _
    _ ≤ (‖a - b‖ * ‖DA.applyFunction f‖ * ‖c‖) +
        (‖b‖ * ‖DA.applyFunction f - DB.applyFunction f‖ * ‖c‖) +
        (‖b‖ * ‖DB.applyFunction f‖ * ‖c - d‖) := by
          gcongr
          · exact abs_anchorEval_le _ _ _
          · exact abs_anchorEval_le _ _ _
          · exact abs_anchorEval_le _ _ _
    _ ≤ ‖a - b‖ * (κA * R) * ‖c‖ +
        ‖b‖ * ((n : ℝ) ^ 2 * κA * κB * ‖A - B‖) * ‖c‖ +
        ‖b‖ * (κB * R) * ‖c - d‖ := by gcongr

end CausalSmith.Substrate.CollisionSafeSpectralLaw
