module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Explicit one-sided interpolation

The factorial-scaled Vandermonde grid in the bias roadmap is nonsingular.
Its declared inverse norm bounds recovered Taylor jets from grid responses.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: interpolationMatrix
noncomputable def interpolationMatrix (ell : ℕ) :
    Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ :=
  fun r j => (((r.val : ℝ) / (2 * ell)) ^ j.val) / Nat.factorial j.val

-- @node: interpolationInverseNorm
noncomputable def interpolationInverseNorm (ell : ℕ) : ℝ :=
  ∑ r : Fin (ell + 1), ∑ j : Fin (ell + 1),
    |((interpolationMatrix ell)⁻¹) r j|

/-- The paper's grid matrix is a Vandermonde matrix with factorial-scaled columns. -/
-- @node: interpolationMatrix_eq_vandermonde_mul_diagonal
lemma interpolationMatrix_eq_vandermonde_mul_diagonal (ell : ℕ) :
    interpolationMatrix ell =
      Matrix.vandermonde (fun r : Fin (ell + 1) => (r.val : ℝ) / (2 * ell)) *
        Matrix.diagonal (fun j : Fin (ell + 1) => (Nat.factorial j.val : ℝ)⁻¹) := by
  ext r j
  simp [interpolationMatrix, Matrix.mul_diagonal, Matrix.vandermonde, div_eq_mul_inv]

/-- Distinct equally spaced grid points give an invertible interpolation matrix. -/
-- @node: interpolationMatrix_det_ne_zero
lemma interpolationMatrix_det_ne_zero (ell : ℕ) (hell : 0 < ell) :
    (interpolationMatrix ell).det ≠ 0 := by
  rw [interpolationMatrix_eq_vandermonde_mul_diagonal, Matrix.det_mul,
    Matrix.det_diagonal]
  apply mul_ne_zero
  · apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro r s hrs
    have hd : (2 * (ell : ℝ)) ≠ 0 := by positivity
    have hv : (r.val : ℝ) = s.val := (div_left_inj' hd).mp hrs
    apply Fin.ext
    exact_mod_cast hv
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j.val)

/-- The finite inverse solve recovers every jet from its grid response. -/
-- @node: interpolationMatrix_recover
lemma interpolationMatrix_recover (ell : ℕ) (hell : 0 < ell)
    (v : Fin (ell + 1) → ℝ) :
    (interpolationMatrix ell)⁻¹.mulVec ((interpolationMatrix ell).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (interpolationMatrix_det_ne_zero ell hell)),
    Matrix.one_mulVec]

/-- A uniform bound on the grid response bounds each recovered coefficient
by the declared finite inverse norm, without an unspecified interpolation constant. -/
-- @node: interpolationMatrix_jet_bound
lemma interpolationMatrix_jet_bound (ell : ℕ) (hell : 0 < ell)
    (v : Fin (ell + 1) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hresponse : ∀ r, |(interpolationMatrix ell).mulVec v r| ≤ B)
    (j : Fin (ell + 1)) :
    |v j| ≤ interpolationInverseNorm ell * B := by
  have hrecover := congrFun (interpolationMatrix_recover ell hell v) j
  rw [← hrecover, Matrix.mulVec, dotProduct]
  calc
    _ ≤ ∑ r : Fin (ell + 1),
        |(interpolationMatrix ell)⁻¹ j r * (interpolationMatrix ell).mulVec v r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin (ell + 1), |(interpolationMatrix ell)⁻¹ j r| * B := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hresponse r) (abs_nonneg _)
    _ = (∑ r : Fin (ell + 1), |(interpolationMatrix ell)⁻¹ j r|) * B := by
      rw [Finset.sum_mul]
    _ ≤ interpolationInverseNorm ell * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      unfold interpolationInverseNorm
      exact Finset.single_le_sum
        (f := fun r => ∑ s : Fin (ell + 1), |(interpolationMatrix ell)⁻¹ r s|)
        (fun r _ => Finset.sum_nonneg (fun s _ => abs_nonneg _)) (Finset.mem_univ j)

/-- The grid values of a bounded function, with a controlled Taylor remainder,
give the exact inverse-norm jet envelope used in the bias roadmap. -/
-- @node: interpolationMatrix_jet_bound_of_remainder
lemma interpolationMatrix_jet_bound_of_remainder (ell : ℕ) (hell : 0 < ell)
    (v y : Fin (ell + 1) → ℝ) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hy : ∀ r, |y r| ≤ M)
    (hrem : ∀ r, |y r - (interpolationMatrix ell).mulVec v r| ≤ R)
    (j : Fin (ell + 1)) :
    |v j| ≤ interpolationInverseNorm ell * (M + R) := by
  apply interpolationMatrix_jet_bound ell hell v (add_nonneg hM hR)
  intro r
  calc
    |(interpolationMatrix ell).mulVec v r| =
        |y r - (y r - (interpolationMatrix ell).mulVec v r)| := by congr 1; ring
    _ ≤ |y r| + |y r - (interpolationMatrix ell).mulVec v r| := abs_sub _ _
    _ ≤ M + R := add_le_add (hy r) (hrem r)

/-- Backward interpolation has the same coefficient envelope: reversing the
grid direction changes only signs of the Taylor columns. -/
-- @node: interpolationMatrix_backward_jet_bound_of_remainder
lemma interpolationMatrix_backward_jet_bound_of_remainder (ell : ℕ) (hell : 0 < ell)
    (v y : Fin (ell + 1) → ℝ) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hy : ∀ r, |y r| ≤ M)
    (hrem : ∀ r, |y r - (interpolationMatrix ell).mulVec
      (fun j => (-1 : ℝ) ^ j.val * v j) r| ≤ R)
    (j : Fin (ell + 1)) :
    |v j| ≤ interpolationInverseNorm ell * (M + R) := by
  have h := interpolationMatrix_jet_bound_of_remainder ell hell
    (fun j => (-1 : ℝ) ^ j.val * v j) y hM hR hy hrem j
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using h

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
