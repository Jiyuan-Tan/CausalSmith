import Causalean.Mathlib.Analysis.SymmetricTensorPencil.SpectralMatching
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Gap-based matching of spectral projectors

This module states a quantitative finite-dimensional matching theorem for two real matrices
with simple, separated, real spectra.  Projectors are represented algebraically through the
respective diagonalizers, while the proof route is the usual complex Riesz-contour argument.
Mathlib's circle-integral Cauchy formulas supply the scalar residue calculation; the resolvent
bounds themselves use the explicitly supplied reference diagonalizer and a Neumann argument.
-/

namespace Causalean.Mathlib.Analysis.SymmetricTensorPencil

open scoped Matrix.Norms.L2Operator

/-- The trace of a real square matrix is at most the dimension times its Euclidean operator norm
in absolute value. [The stated conclusion follows](goal). -/
theorem abs_trace_le_card_mul_operatorNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |Matrix.trace A| ≤ n * squareOperatorNorm A := by
  classical
  have hentry (i : Fin n) : |A i i| ≤ squareOperatorNorm A := by
    let e : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Pi.single i 1)
    have he : ‖e‖ = 1 := by simp [e]
    have hcoord :
        |((EuclideanSpace.equiv (Fin n) ℝ).symm (Matrix.mulVec A e)) i| ≤
          ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (Matrix.mulVec A e)‖ := by
      simpa only [Real.norm_eq_abs] using
        PiLp.norm_apply_le
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (Matrix.mulVec A e)) i
    calc
      |A i i| = |((EuclideanSpace.equiv (Fin n) ℝ).symm (Matrix.mulVec A e)) i| := by
        simp [e]
      _ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (Matrix.mulVec A e)‖ := hcoord
      _ ≤ ‖A‖ * ‖e‖ := Matrix.l2_opNorm_mulVec A e
      _ = ‖A‖ := by rw [he, mul_one]
      _ = ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) A‖ :=
        (Matrix.l2_opNorm_toEuclideanCLM A).symm
      _ = squareOperatorNorm A := rfl
  calc
    |Matrix.trace A| = |∑ i, A i i| := rfl
    _ ≤ ∑ i, |A i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, squareOperatorNorm A :=
      Finset.sum_le_sum fun i _ => hentry i
    _ = n * squareOperatorNorm A := by simp

private noncomputable def complexMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  A.map Complex.ofReal

private theorem realVector_complex_norm {n : ℕ} (x : Fin n → ℝ) :
    ‖WithLp.toLp 2 (fun i => (x i : ℂ))‖ = ‖WithLp.toLp 2 x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_ofReal]
  ring

private theorem complexVector_norm_sq {n : ℕ} (z : Fin n → ℂ) :
    ‖WithLp.toLp 2 z‖ ^ 2 =
      ‖WithLp.toLp 2 (fun k => (z k).re)‖ ^ 2 +
      ‖WithLp.toLp 2 (fun k => (z k).im)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp_rw [Complex.sq_norm, Complex.normSq_apply]
  rw [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

private theorem complexMatrix_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℂ) :
    (complexMatrix A).mulVec z =
      fun i => ((A.mulVec (fun k => (z k).re) i : ℂ) +
        Complex.I * (A.mulVec (fun k => (z k).im) i : ℂ)) := by
  ext i <;> simp [complexMatrix, Matrix.mulVec, dotProduct, Complex.ext_iff,
    Complex.mul_re, Complex.mul_im]

private theorem complexMatrix_real_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    (complexMatrix A).mulVec (fun i => (x i : ℂ)) =
      fun i => (A.mulVec x i : ℂ) := by
  ext i
  simp [complexMatrix, Matrix.mulVec, dotProduct]

/-- Complexifying a real matrix preserves its Euclidean operator norm. -/
private theorem complexMatrix_norm_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖complexMatrix A‖ = ‖A‖ := by
  apply le_antisymm
  · rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro z
    change ‖WithLp.toLp 2 ((complexMatrix A).mulVec z)‖ ≤ ‖A‖ * ‖z‖
    let xr : Fin n → ℝ := fun k => (z k).re
    let xi : Fin n → ℝ := fun k => (z k).im
    have hr : ‖WithLp.toLp 2 (A.mulVec xr)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 xr‖ := by
      simpa using Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 xr)
    have hi : ‖WithLp.toLp 2 (A.mulVec xi)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 xi‖ := by
      simpa using Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 xi)
    have hout :
        ‖WithLp.toLp 2 ((complexMatrix A).mulVec z)‖ ^ 2 =
          ‖WithLp.toLp 2 (A.mulVec xr)‖ ^ 2 +
          ‖WithLp.toLp 2 (A.mulVec xi)‖ ^ 2 := by
      rw [complexMatrix_mulVec]
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
        EuclideanSpace.real_norm_sq_eq]
      simp_rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im]
      simp_rw [Complex.mul_re, Complex.mul_im]
      simp only [Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_self, add_zero, one_mul, zero_add]
      rw [Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [hout, mul_pow, complexVector_norm_sq z]
    have hr2 := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hr
    have hi2 := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
    nlinarith
  · rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (complexMatrix A))
    intro x
    change ‖WithLp.toLp 2 (A.mulVec x)‖ ≤ ‖complexMatrix A‖ * ‖x‖
    have h := Matrix.l2_opNorm_mulVec (complexMatrix A)
      (WithLp.toLp 2 (fun i => (x i : ℂ)))
    rw [complexMatrix_real_mulVec] at h
    change ‖WithLp.toLp 2 (fun i => (A.mulVec x i : ℂ))‖ ≤
      ‖complexMatrix A‖ * ‖WithLp.toLp 2 (fun i => (x i : ℂ))‖ at h
    simpa only [realVector_complex_norm] using h

private theorem complexMatrix_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    complexMatrix (A * B) = complexMatrix A * complexMatrix B := by
  ext a b
  simp [complexMatrix, Matrix.mul_apply]

private theorem complexMatrix_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    complexMatrix (A - B) = complexMatrix A - complexMatrix B := by
  ext a b
  simp [complexMatrix]

private theorem complexMatrix_one {n : ℕ} :
    complexMatrix (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext a b
  by_cases h : a = b <;> simp [complexMatrix, Matrix.one_apply, h]

private theorem complexMatrix_diagonal {n : ℕ} (values : Fin n → ℝ) :
    complexMatrix (Matrix.diagonal values) =
      Matrix.diagonal (fun k => (values k : ℂ)) := by
  ext a b
  by_cases h : a = b <;> simp [complexMatrix, Matrix.diagonal_apply, h]

private theorem complexMatrix_inv_mul {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) : complexMatrix S⁻¹ * complexMatrix S = 1 := by
  rw [← complexMatrix_mul, Matrix.nonsing_inv_mul S hS, complexMatrix_one]

private theorem complexMatrix_mul_inv {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) : complexMatrix S * complexMatrix S⁻¹ = 1 := by
  rw [← complexMatrix_mul, Matrix.mul_nonsing_inv S hS, complexMatrix_one]

private theorem complexMatrix_diagonalizableMatrix {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (values : Fin n → ℝ) :
    complexMatrix (diagonalizableMatrix S values) =
      complexMatrix S * Matrix.diagonal (fun k => (values k : ℂ)) * complexMatrix S⁻¹ := by
  rw [diagonalizableMatrix, complexMatrix_mul, complexMatrix_mul,
    complexMatrix_diagonal]

private theorem complex_shift_factorization {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (values : Fin n → ℝ) (z : ℂ)
    (hS : IsUnit S.det) :
    z • (1 : Matrix (Fin n) (Fin n) ℂ) -
        complexMatrix (diagonalizableMatrix S values) =
      complexMatrix S *
        (z • 1 - Matrix.diagonal (fun k => (values k : ℂ))) * complexMatrix S⁻¹ := by
  rw [complexMatrix_diagonalizableMatrix, mul_sub, sub_mul]
  congr 1
  rw [mul_smul_comm, mul_one, smul_mul_assoc, complexMatrix_mul_inv S hS]

private noncomputable def complexResolvent {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (values : Fin n → ℝ) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  complexMatrix S * Matrix.diagonal (fun k => (z - (values k : ℂ))⁻¹) *
    complexMatrix S⁻¹

private theorem complexMatrix_coordinateProjector_apply {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (k a b : Fin n) :
    complexMatrix (coordinateProjector S k) a b = ((S a k * S⁻¹ k b : ℝ) : ℂ) := by
  classical
  simp [complexMatrix, coordinateProjector, Matrix.mul_apply, Matrix.diagonal_apply]

private theorem complexResolvent_apply {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (values : Fin n → ℝ) (z : ℂ) (a b : Fin n) :
    complexResolvent S values z a b =
      ∑ k, (z - (values k : ℂ))⁻¹ * ((S a k * S⁻¹ k b : ℝ) : ℂ) := by
  classical
  simp [complexResolvent, complexMatrix, Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem complexResolvent_eq_sum {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (values : Fin n → ℝ) (z : ℂ) :
    complexResolvent S values z =
      ∑ k, (z - (values k : ℂ))⁻¹ • complexMatrix (coordinateProjector S k) := by
  classical
  ext a b
  rw [complexResolvent_apply, Matrix.sum_apply a b Finset.univ]
  apply Finset.sum_congr rfl
  intro k _
  change (z - (values k : ℂ))⁻¹ * ((S a k * S⁻¹ k b : ℝ) : ℂ) =
    (z - (values k : ℂ))⁻¹ * complexMatrix (coordinateProjector S k) a b
  rw [complexMatrix_coordinateProjector_apply]

private theorem complexResolvent_circleIntegrable {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (values : Fin n → ℝ) (c : ℂ) {R : ℝ}
    (hR : 0 ≤ R) (hne : ∀ k, (values k : ℂ) ∉ Metric.sphere c R) :
    CircleIntegrable (fun z => complexResolvent S values z) c R := by
  classical
  rw [show (fun z => complexResolvent S values z) =
      fun z => ∑ k, (z - (values k : ℂ))⁻¹ •
        complexMatrix (coordinateProjector S k) by
      funext z; exact complexResolvent_eq_sum S values z]
  apply CircleIntegrable.fun_sum Finset.univ
  intro k _
  apply ContinuousOn.circleIntegrable'
  rw [abs_of_nonneg hR]
  have hf : ContinuousOn (fun z => (z - (values k : ℂ))⁻¹)
      (Metric.sphere c R) := by
    apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro z hz
    change z - (values k : ℂ) ≠ 0
    intro hzero
    apply hne k
    have hzk : z = (values k : ℂ) := sub_eq_zero.mp hzero
    exact hzk ▸ hz
  change ContinuousOn
    ((fun z => (z - (values k : ℂ))⁻¹) •
      (fun _ => complexMatrix (coordinateProjector S k))) (Metric.sphere c R)
  exact hf.smul continuousOn_const

private theorem circleIntegral_sub_inv_of_not_mem_closedBall {c w : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hw : w ∉ Metric.closedBall c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hR Set.countable_empty
  · apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro z hz
    change z - w ≠ 0
    exact sub_ne_zero.mpr fun hzw => hw (hzw ▸ hz)
  · intro z hz
    apply DifferentiableAt.inv
    · fun_prop
    · exact sub_ne_zero.mpr fun hzw =>
        hw (hzw ▸ Metric.ball_subset_closedBall hz.1)

private theorem complexResolvent_integral_eq_projector {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (values : Fin n → ℝ) (j : Fin n)
    (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hin : ‖(values j : ℂ) - c‖ < R)
    (hout : ∀ k, k ≠ j → R < ‖(values k : ℂ) - c‖) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ z in C(c, R), complexResolvent S values z) =
      complexMatrix (coordinateProjector S j) := by
  classical
  have hne (k : Fin n) : (values k : ℂ) ∉ Metric.sphere c R := by
    intro hk
    have heq : ‖(values k : ℂ) - c‖ = R := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp hk
    by_cases hkj : k = j
    · subst k
      linarith
    · exact (ne_of_lt (hout k hkj)) heq.symm
  have hint (k : Fin n) :
      CircleIntegrable
        (fun z => (z - (values k : ℂ))⁻¹ •
          complexMatrix (coordinateProjector S k)) c R := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_pos hR]
    have hf : ContinuousOn (fun z => (z - (values k : ℂ))⁻¹)
        (Metric.sphere c R) := by
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro z hz
      change z - (values k : ℂ) ≠ 0
      intro hzero
      apply hne k
      have hzk : z = (values k : ℂ) := sub_eq_zero.mp hzero
      exact hzk ▸ hz
    change ContinuousOn
      ((fun z => (z - (values k : ℂ))⁻¹) •
        (fun _ => complexMatrix (coordinateProjector S k))) (Metric.sphere c R)
    exact hf.smul continuousOn_const
  rw [show (fun z => complexResolvent S values z) =
      fun z => ∑ k, (z - (values k : ℂ))⁻¹ •
        complexMatrix (coordinateProjector S k) by
      funext z; exact complexResolvent_eq_sum S values z]
  rw [circleIntegral.integral_fun_sum (fun k _ => hint k)]
  have hscalar (k : Fin n) :
      (∮ z in C(c, R), (z - (values k : ℂ))⁻¹) =
        if k = j then 2 * Real.pi * Complex.I else 0 := by
    split
    · subst k
      exact circleIntegral.integral_sub_inv_of_mem_ball
        (by rw [Metric.mem_ball, dist_eq_norm]; exact hin)
    · apply circleIntegral_sub_inv_of_not_mem_closedBall hR.le
      intro hk
      have hle : ‖(values k : ℂ) - c‖ ≤ R := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp hk
      exact (not_lt_of_ge hle) (hout k ‹k ≠ j›)
  rw [Finset.smul_sum]
  simp_rw [circleIntegral.integral_smul_const, hscalar]
  simp only [ite_smul, zero_smul, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j]
  have htwo : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [if_pos (Finset.mem_univ j)]
  exact inv_smul_smul₀ htwo (complexMatrix (coordinateProjector S j))

private theorem complexResolvent_norm_le {n : ℕ} [NeZero n]
    (S : Matrix (Fin n) (Fin n) ℝ) (values : Fin n → ℝ) (z : ℂ)
    {sigma chi : ℝ} (hsigma : 0 < sigma)
    (hcondition : squareOperatorNorm S * squareOperatorNorm S⁻¹ ≤ chi)
    (hdist : ∀ k, sigma / 3 ≤ ‖z - (values k : ℂ)‖) :
    ‖complexResolvent S values z‖ ≤ 3 * chi / sigma := by
  letI : Nonempty (Fin n) := inferInstance
  have hdiag :
      ‖Matrix.diagonal (fun k : Fin n => (z - (values k : ℂ))⁻¹)‖ ≤ 3 / sigma := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonempty _).2
    intro k
    rw [norm_inv]
    calc
      ‖z - (values k : ℂ)‖⁻¹ ≤ (sigma / 3)⁻¹ :=
        inv_anti₀ (by positivity) (hdist k)
      _ = 3 / sigma := by field_simp
  have hcond : ‖complexMatrix S‖ * ‖complexMatrix S⁻¹‖ ≤ chi := by
    rw [complexMatrix_norm_eq, complexMatrix_norm_eq]
    simpa only [squareOperatorNorm, Matrix.l2_opNorm_toEuclideanCLM] using hcondition
  have hchi : 0 ≤ chi :=
    (mul_nonneg (norm_nonneg (complexMatrix S))
      (norm_nonneg (complexMatrix S⁻¹))).trans hcond
  calc
    ‖complexResolvent S values z‖
        ≤ ‖complexMatrix S * Matrix.diagonal
            (fun k => (z - (values k : ℂ))⁻¹)‖ * ‖complexMatrix S⁻¹‖ := by
          exact Matrix.l2_opNorm_mul _ _
    _ ≤ (‖complexMatrix S‖ * ‖Matrix.diagonal
          (fun k => (z - (values k : ℂ))⁻¹)‖) * ‖complexMatrix S⁻¹‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
    _ = (‖complexMatrix S‖ * ‖complexMatrix S⁻¹‖) *
          ‖Matrix.diagonal (fun k => (z - (values k : ℂ))⁻¹)‖ := by ring
    _ ≤ chi * (3 / sigma) := mul_le_mul hcond hdiag (norm_nonneg _) hchi
    _ = 3 * chi / sigma := by ring

private theorem diagonal_resolvent_mul_shift {n : ℕ} (values : Fin n → ℝ) (z : ℂ)
    (hz : ∀ k, z ≠ (values k : ℂ)) :
    Matrix.diagonal (fun k => (z - (values k : ℂ))⁻¹) *
        (z • 1 - Matrix.diagonal (fun k => (values k : ℂ))) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hz a))
  · simp [Matrix.mul_apply, Matrix.diagonal_apply, hab]

private theorem diagonal_shift_mul_resolvent {n : ℕ} (values : Fin n → ℝ) (z : ℂ)
    (hz : ∀ k, z ≠ (values k : ℂ)) :
    (z • 1 - Matrix.diagonal (fun k => (values k : ℂ))) *
        Matrix.diagonal (fun k => (z - (values k : ℂ))⁻¹) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (hz a))
  · simp [Matrix.mul_apply, Matrix.diagonal_apply, hab]

private theorem complexResolvent_mul_shift {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (values : Fin n → ℝ) (z : ℂ)
    (hS : IsUnit S.det) (hz : ∀ k, z ≠ (values k : ℂ)) :
    complexResolvent S values z *
        (z • 1 - complexMatrix (diagonalizableMatrix S values)) = 1 := by
  rw [complex_shift_factorization S values z hS]
  simp only [complexResolvent, mul_assoc]
  rw [← mul_assoc (complexMatrix S⁻¹) (complexMatrix S),
    complexMatrix_inv_mul S hS, one_mul,
    ← mul_assoc (Matrix.diagonal (fun k => (z - (values k : ℂ))⁻¹)),
    diagonal_resolvent_mul_shift values z hz, one_mul,
    complexMatrix_mul_inv S hS]

private theorem complex_shift_mul_resolvent {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (values : Fin n → ℝ) (z : ℂ)
    (hS : IsUnit S.det) (hz : ∀ k, z ≠ (values k : ℂ)) :
    (z • 1 - complexMatrix (diagonalizableMatrix S values)) *
        complexResolvent S values z = 1 := by
  rw [complex_shift_factorization S values z hS]
  simp only [complexResolvent, mul_assoc]
  rw [← mul_assoc (complexMatrix S⁻¹) (complexMatrix S),
    complexMatrix_inv_mul S hS, one_mul,
    ← mul_assoc (z • 1 - Matrix.diagonal (fun k => (values k : ℂ))),
    diagonal_shift_mul_resolvent values z hz, one_mul,
    complexMatrix_mul_inv S hS]

private theorem complex_resolvent_identity {n : ℕ}
    (S S' : Matrix (Fin n) (Fin n) ℝ) (values values' : Fin n → ℝ) (z : ℂ)
    (hS : IsUnit S.det) (hS' : IsUnit S'.det)
    (hz : ∀ k, z ≠ (values k : ℂ)) (hz' : ∀ k, z ≠ (values' k : ℂ)) :
    complexResolvent S' values' z - complexResolvent S values z =
      complexResolvent S' values' z *
        complexMatrix (diagonalizableMatrix S' values' - diagonalizableMatrix S values) *
          complexResolvent S values z := by
  rw [complexMatrix_sub]
  have href := complex_shift_mul_resolvent S values z hS hz
  have hprime := complexResolvent_mul_shift S' values' z hS' hz'
  calc
    complexResolvent S' values' z - complexResolvent S values z =
        complexResolvent S' values' z * 1 - 1 * complexResolvent S values z := by simp
    _ = complexResolvent S' values' z *
          ((z • 1 - complexMatrix (diagonalizableMatrix S values)) *
            complexResolvent S values z) -
        (complexResolvent S' values' z *
          (z • 1 - complexMatrix (diagonalizableMatrix S' values'))) *
            complexResolvent S values z := by rw [href, hprime]
    _ = complexResolvent S' values' z *
          ((z • 1 - complexMatrix (diagonalizableMatrix S values)) -
            (z • 1 - complexMatrix (diagonalizableMatrix S' values'))) *
          complexResolvent S values z := by noncomm_ring
    _ = _ := by congr 2 <;> module

/-- Matched simple eigenvalues of two nearby diagonalizable matrices have close coordinate
projectors, and the perturbed projector remains controlled by twice the reference condition
envelope. Under [the listed assumptions](hyp:hS,hS',hsigma,hchi,hdelta,hgap,hgap',hcondition,hclose,hmatch,hsmall), [the stated conclusion follows](goal). -/
-- Proof route: complexify and use the circle of radius `sigma / 3` about `values j`.
-- Bauer--Fike localization and `hsmall` keep the Neumann resolvent along that circle invertible;
-- the resolvent identity bounds the contour-integral difference.  Algebraic identification of
-- those Riesz integrals with the two coordinate projectors gives the three stated estimates.
theorem coordinateProjector_perturbation_of_matched_eigenvalue {n : ℕ} [NeZero n]
    (S S' : Matrix (Fin n) (Fin n) ℝ) (values values' : Fin n → ℝ)
    (j j' : Fin n) {sigma chi delta : ℝ}
    (hS : IsUnit S.det) (hS' : IsUnit S'.det)
    (hsigma : 0 < sigma) (hchi : 0 < chi) (hdelta : 0 ≤ delta)
    (hgap : PairwiseGap values sigma) (hgap' : PairwiseGap values' sigma)
    (hcondition : squareOperatorNorm S * squareOperatorNorm S⁻¹ ≤ chi)
    (hclose : squareOperatorNorm
      (diagonalizableMatrix S' values' - diagonalizableMatrix S values) ≤ delta)
    (hmatch : |values' j' - values j| ≤ chi * delta)
    (hsmall : 6 * chi * delta < sigma) :
    squareOperatorNorm (coordinateProjector S' j' - coordinateProjector S j) ≤
        6 * chi ^ 2 * delta / sigma ∧
      squareOperatorNorm (coordinateProjector S j) ≤ chi ∧
      squareOperatorNorm (coordinateProjector S' j') ≤ 2 * chi := by
  let c : ℂ := (values j : ℂ)
  let R : ℝ := sigma / 3
  let E := diagonalizableMatrix S' values' - diagonalizableMatrix S values
  have hR : 0 < R := by dsimp [R]; positivity
  have hchidelta : chi * delta < sigma / 6 := by linarith
  have hcircle_norm {z : ℂ} (hz : z ∈ Metric.sphere c R) : ‖z - c‖ = R := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hz
  have href_dist {z : ℂ} (hz : z ∈ Metric.sphere c R) :
      ∀ k, sigma / 3 ≤ ‖z - (values k : ℂ)‖ := by
    intro k
    by_cases hkj : k = j
    · subst k
      simpa [c, R] using (hcircle_norm hz).ge
    · have hgapkj : sigma ≤ ‖(values k : ℂ) - c‖ := by
        calc
          sigma ≤ |values k - values j| := by simpa [abs_sub_comm] using hgap k j hkj
          _ = ‖((values k - values j : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]
          _ = ‖(values k : ℂ) - (values j : ℂ)‖ := by norm_cast
          _ = ‖(values k : ℂ) - c‖ := by rw [show c = (values j : ℂ) by rfl]
      have htri := norm_sub_le_norm_sub_add_norm_sub (values k : ℂ) z c
      have hzc := hcircle_norm hz
      rw [norm_sub_rev (values k : ℂ) z] at htri
      dsimp [R] at hzc
      linarith
  have hprime_in : ‖(values' j' : ℂ) - c‖ < R := by
    have hm : ‖(values' j' : ℂ) - c‖ ≤ chi * delta := by
      calc
        _ = ‖((values' j' - values j : ℝ) : ℂ)‖ := by
          rw [show c = (values j : ℂ) by rfl]
          norm_cast
        _ = |values' j' - values j| := by rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ _ := hmatch
    dsimp [R]
    linarith
  have hprime_out : ∀ k, k ≠ j' → R < ‖(values' k : ℂ) - c‖ := by
    intro k hkj'
    have hgapkj : sigma ≤ ‖(values' k : ℂ) - (values' j' : ℂ)‖ := by
      calc
        sigma ≤ |values' k - values' j'| := by
          simpa [abs_sub_comm] using hgap' k j' hkj'
        _ = ‖((values' k - values' j' : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        _ = _ := by norm_cast
    have htri := norm_sub_le_norm_sub_add_norm_sub (values' k : ℂ) c (values' j' : ℂ)
    have hm : ‖c - (values' j' : ℂ)‖ ≤ chi * delta := by
      rw [norm_sub_rev]
      calc
        _ = ‖((values' j' - values j : ℝ) : ℂ)‖ := by
          rw [show c = (values j : ℂ) by rfl]
          norm_cast
        _ = |values' j' - values j| := by rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ _ := hmatch
    dsimp [R]
    linarith
  have href_out : ∀ k, k ≠ j → R < ‖(values k : ℂ) - c‖ := by
    intro k hkj
    have hg : sigma ≤ ‖(values k : ℂ) - c‖ := by
      calc
        sigma ≤ |values k - values j| := by simpa [abs_sub_comm] using hgap k j hkj
        _ = ‖((values k - values j : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        _ = ‖(values k : ℂ) - (values j : ℂ)‖ := by norm_cast
        _ = _ := by rw [show c = (values j : ℂ) by rfl]
    dsimp [R]
    linarith
  have href_ne {z : ℂ} (hz : z ∈ Metric.sphere c R) :
      ∀ k, z ≠ (values k : ℂ) := by
    intro k hzk
    subst z
    have := href_dist hz k
    simp only [sub_self, norm_zero] at this
    linarith
  have hprime_ne {z : ℂ} (hz : z ∈ Metric.sphere c R) :
      ∀ k, z ≠ (values' k : ℂ) := by
    intro k hzk
    subst z
    by_cases hkj : k = j'
    · subst k
      have heq := hcircle_norm hz
      linarith
    · have hout := hprime_out k hkj
      have heq := hcircle_norm hz
      linarith
  have hE : ‖complexMatrix E‖ ≤ delta := by
    rw [complexMatrix_norm_eq]
    simpa only [E, squareOperatorNorm, Matrix.l2_opNorm_toEuclideanCLM] using hclose
  let r : ℝ := 3 * chi / sigma
  have hrpos : 0 < r := by dsimp [r]; positivity
  have href_norm {z : ℂ} (hz : z ∈ Metric.sphere c R) :
      ‖complexResolvent S values z‖ ≤ r := by
    dsimp [r]
    exact complexResolvent_norm_le S values z hsigma hcondition (href_dist hz)
  have hdelta_r : delta * r < 1 / 2 := by
    dsimp [r]
    rw [show delta * (3 * chi / sigma) = (3 * chi * delta) / sigma by ring]
    apply (div_lt_iff₀ hsigma).2
    nlinarith [hsmall]
  have hprime_norm {z : ℂ} (hz : z ∈ Metric.sphere c R) :
      ‖complexResolvent S' values' z‖ ≤ 2 * r := by
    have hid := complex_resolvent_identity S S' values values' z hS hS'
      (href_ne hz) (hprime_ne hz)
    have hdiff :
        ‖complexResolvent S' values' z - complexResolvent S values z‖ ≤
          (‖complexResolvent S' values' z‖ * delta) * r := by
      rw [hid]
      calc
        ‖complexResolvent S' values' z * complexMatrix E * complexResolvent S values z‖
            ≤ ‖complexResolvent S' values' z * complexMatrix E‖ *
                ‖complexResolvent S values z‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ (‖complexResolvent S' values' z‖ * ‖complexMatrix E‖) *
              ‖complexResolvent S values z‖ := by
            gcongr
            exact Matrix.l2_opNorm_mul _ _
        _ ≤ (‖complexResolvent S' values' z‖ * delta) *
              ‖complexResolvent S values z‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hE (norm_nonneg _)) (norm_nonneg _)
        _ ≤ (‖complexResolvent S' values' z‖ * delta) * r := by
            exact mul_le_mul_of_nonneg_left (href_norm hz)
              (mul_nonneg (norm_nonneg _) hdelta)
    have hsum : ‖complexResolvent S' values' z‖ ≤
        ‖complexResolvent S' values' z - complexResolvent S values z‖ +
          ‖complexResolvent S values z‖ := by
      calc
        ‖complexResolvent S' values' z‖ =
            ‖(complexResolvent S' values' z - complexResolvent S values z) +
              complexResolvent S values z‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    nlinarith [href_norm hz, norm_nonneg (complexResolvent S' values' z)]
  have hint_bound {z : ℂ} (hz : z ∈ Metric.sphere c R) :
      ‖complexResolvent S' values' z - complexResolvent S values z‖ ≤
        18 * chi ^ 2 * delta / sigma ^ 2 := by
    rw [complex_resolvent_identity S S' values values' z hS hS'
      (href_ne hz) (hprime_ne hz)]
    calc
      ‖complexResolvent S' values' z * complexMatrix E * complexResolvent S values z‖
          ≤ ‖complexResolvent S' values' z * complexMatrix E‖ *
              ‖complexResolvent S values z‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖complexResolvent S' values' z‖ * ‖complexMatrix E‖) *
            ‖complexResolvent S values z‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ (‖complexResolvent S' values' z‖ * delta) *
            ‖complexResolvent S values z‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hE (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ((2 * r) * delta) * ‖complexResolvent S values z‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hprime_norm hz) hdelta) (norm_nonneg _)
      _ ≤ ((2 * r) * delta) * r := by
          exact mul_le_mul_of_nonneg_left (href_norm hz)
            (mul_nonneg (mul_nonneg (by positivity) hrpos.le) hdelta)
      _ = 18 * chi ^ 2 * delta / sigma ^ 2 := by
        dsimp [r]
        field_simp
        ring
  have hcontour :
      ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C(c, R),
            (complexResolvent S' values' z - complexResolvent S values z))‖ ≤
        6 * chi ^ 2 * delta / sigma := by
    calc
      _ ≤ R * (18 * chi ^ 2 * delta / sigma ^ 2) :=
        circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
          hR.le (fun z hz => hint_bound hz)
      _ = 6 * chi ^ 2 * delta / sigma := by
        dsimp [R]
        field_simp
        ring
  have href_int := complexResolvent_integral_eq_projector S values j c hR
    (by simp [c, R, hR]) href_out
  have hprime_int := complexResolvent_integral_eq_projector S' values' j' c hR
    hprime_in hprime_out
  have hintS : CircleIntegrable (fun z => complexResolvent S values z) c R := by
    apply complexResolvent_circleIntegrable S values c hR.le
    intro k hk
    exact href_ne hk k rfl
  have hintS' : CircleIntegrable (fun z => complexResolvent S' values' z) c R := by
    apply complexResolvent_circleIntegrable S' values' c hR.le
    intro k hk
    exact hprime_ne hk k rfl
  have hprojector_diff :
      complexMatrix (coordinateProjector S' j' - coordinateProjector S j) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C(c, R),
            (complexResolvent S' values' z - complexResolvent S values z)) := by
    rw [complexMatrix_sub, circleIntegral.integral_sub hintS' hintS,
      smul_sub, hprime_int, href_int]
  have hdiff_real :
      squareOperatorNorm (coordinateProjector S' j' - coordinateProjector S j) ≤
        6 * chi ^ 2 * delta / sigma := by
    rw [squareOperatorNorm]
    rw [Matrix.l2_opNorm_toEuclideanCLM
      (coordinateProjector S' j' - coordinateProjector S j)]
    rw [← complexMatrix_norm_eq]
    rw [hprojector_diff]
    exact hcontour
  have hP := coordinateProjector_operatorNorm_le S j hS hcondition
  have hP' : squareOperatorNorm (coordinateProjector S' j') ≤ 2 * chi := by
    calc
      squareOperatorNorm (coordinateProjector S' j') =
          squareOperatorNorm
            ((coordinateProjector S' j' - coordinateProjector S j) +
              coordinateProjector S j) := by congr 2; abel
      _ ≤ squareOperatorNorm (coordinateProjector S' j' - coordinateProjector S j) +
          squareOperatorNorm (coordinateProjector S j) := by
        unfold squareOperatorNorm
        rw [map_add]
        exact norm_add_le _ _
      _ ≤ 6 * chi ^ 2 * delta / sigma + chi := add_le_add hdiff_real hP
      _ ≤ 2 * chi := by
        have herr_lt : 6 * chi ^ 2 * delta / sigma < chi := by
          apply (div_lt_iff₀ hsigma).2
          nlinarith [hsmall]
        linarith
  exact ⟨hdiff_real, hP, hP'⟩

/-- Given two diagonalizers, their simple spectra,
invertibility, positive separation, conditioning, and error margins,
separation of both spectra, a diagonalizer condition bound,
a pencil perturbation bound, and the required small-error condition,
one permutation matches the simple spectral projectors with explicit eigenvalue and operator-norm
bounds. Under [the listed assumptions](hyp:hS,hS',hsigma,hchi,hdelta,hgap,hgap',hcondition,hclose,hsmall), [the stated conclusion follows](goal). -/
-- Proof route: apply `diagonalizableMatrix_eigenvalue_localization`, turn the resulting
-- one-sided localization into a permutation with `exists_permutation_matching_of_localization`,
-- and apply `coordinateProjector_perturbation_of_matched_eigenvalue` along that permutation.
theorem exists_permutation_projector_matching {n : ℕ} [NeZero n]
    (S S' : Matrix (Fin n) (Fin n) ℝ) (values values' : Fin n → ℝ)
    {sigma chi delta : ℝ}
    (hS : IsUnit S.det) (hS' : IsUnit S'.det)
    (hsigma : 0 < sigma) (hchi : 0 < chi) (hdelta : 0 ≤ delta)
    (hgap : PairwiseGap values sigma) (hgap' : PairwiseGap values' sigma)
    (hcondition : squareOperatorNorm S * squareOperatorNorm S⁻¹ ≤ chi)
    (hclose : squareOperatorNorm
      (diagonalizableMatrix S' values' - diagonalizableMatrix S values) ≤ delta)
    (hsmall : 6 * chi * delta < sigma) :
    ∃ pi : Equiv.Perm (Fin n), ∀ j,
      |values' (pi j) - values j| < sigma / 3 ∧
      squareOperatorNorm (coordinateProjector S' (pi j) - coordinateProjector S j) ≤
        6 * chi ^ 2 * delta / sigma ∧
      squareOperatorNorm (coordinateProjector S j) ≤ chi ∧
      squareOperatorNorm (coordinateProjector S' (pi j)) ≤ 2 * chi := by
  have hlocal := diagonalizableMatrix_eigenvalue_localization S S' values values'
    hS hS' hcondition hclose
  have hradius : 0 ≤ chi * delta := mul_nonneg hchi.le hdelta
  have htwosmall : 2 * (chi * delta) < sigma := by linarith
  obtain ⟨pi, hpi⟩ := exists_permutation_matching_of_localization values values'
    hradius hgap' hlocal htwosmall
  refine ⟨pi, fun j => ?_⟩
  have hmatch := hpi j
  have hthird : |values' (pi j) - values j| < sigma / 3 := by linarith
  exact ⟨hthird,
    coordinateProjector_perturbation_of_matched_eigenvalue S S' values values' j (pi j)
      hS hS' hsigma hchi hdelta hgap hgap' hcondition hclose hmatch hsmall⟩

end Causalean.Mathlib.Analysis.SymmetricTensorPencil
