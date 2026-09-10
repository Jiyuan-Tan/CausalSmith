/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Quantitative.Quantitative
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pairwise-affine simultaneous-congruence stability: definitions

This module defines pair-dependent affine-minor separation, off-diagonal approximate
simultaneous congruence, the entrywise Euclidean matrix norm used for aggregation, and
the explicit constants and scale envelopes used by the local stability theorem.

Unlike `AffineMinorSeparated`, the separation predicate here does not select one common
base and a full-dimensional minor.  Its three witnessing environments may depend on the
coordinate pair.
-/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine

open Causalean.Discovery.LinearDisentanglement.Quantitative

/-- For [a dimension](hyp:p), [an environment collection](hyp:E), [a diagonal shift vector for
each environment](hyp:s), [two selected coordinates](hyp:i,j), and [three environments](hyp:e₀,e₁,e₂),
[the pairwise affine determinant](goal) is the signed area determinant of the three corresponding
two-coordinate shift points. -/
def pairAffineDet {p : ℕ} {E : Type*} (s : E → Fin p → ℝ)
    (i j : Fin p) (e₀ e₁ e₂ : E) : ℝ :=
  (s e₁ i - s e₀ i) * (s e₂ j - s e₀ j) -
    (s e₂ i - s e₀ i) * (s e₁ j - s e₀ j)

/-- For [a dimension](hyp:p), [a finite environment collection](hyp:E), [a diagonal shift
vector for each environment](hyp:s), and [a real margin](hyp:δ), [pairwise affine separation](goal)
holds exactly when every two distinct coordinates admit three, possibly pair-specific,
environments whose affine determinant has absolute value at least the margin. -/
def PairwiseAffineSeparated {p : ℕ} {E : Type*} [Fintype E]
    (s : E → Fin p → ℝ) (δ : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ e₀ e₁ e₂ : E, δ ≤ |pairAffineDet s i j e₀ e₁ e₂|

/-- For [a dimension](hyp:p), [a finite environment collection](hyp:E), [an observed matrix
for each environment](hyp:A), [a candidate matrix](hyp:B), and [a real tolerance](hyp:ε),
[off-diagonal approximate congruence](goal) holds exactly when every off-diagonal entry of every
transformed matrix has absolute value at most the tolerance.

Its diagonal output is deliberately left unrestricted. -/
def OffDiagonalApproximateCongruence {p : ℕ} {E : Type*} [Fintype E]
    (A : E → SqMatrix p) (B : SqMatrix p) (ε : ℝ) : Prop :=
  ∀ e i j, i ≠ j → |(B * A e * B.transpose) i j| ≤ ε

/-- For [a dimension](hyp:p) and [a reference and candidate matrix](hyp:B₀,B), [the transition
error](goal) is the transition matrix minus the identity matrix. -/
def transitionError {p : ℕ} (B₀ B : SqMatrix p) : SqMatrix p :=
  transition B₀ B - 1

/-- For [a dimension](hyp:p) and [a square matrix](hyp:R), [its entrywise Euclidean size](goal)
is the square root of the sum of squared absolute values of all its entries. -/
def entryL2 {p : ℕ} (R : SqMatrix p) : ℝ :=
  Real.sqrt (∑ i, ∑ j, |R i j| ^ 2)

/-- For [a matrix scale](hyp:M) and [a pairwise affine-separation margin](hyp:δ), [the pairwise
solve factor](goal) is $6M/\delta$.

The factor six leaves room for centering and triangle inequalities while retaining the requested
specialization. -/
def pairwiseSolveFactor (M δ : ℝ) : ℝ :=
  6 * M / δ

/-- For [a dimension](hyp:p), [a matrix scale](hyp:M), [a pairwise affine-separation margin](hyp:δ),
and [a shift scale](hyp:L), [the pairwise aggregate factor](goal) is the pairwise solve factor
times the square root of $p(p-1)(1+L^2)$. -/
def pairwiseAggregateFactor (p : ℕ) (M δ L : ℝ) : ℝ :=
  pairwiseSolveFactor M δ *
    Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2))

/-- For [a dimension](hyp:p), [a matrix scale](hyp:M), [a pairwise affine-separation margin](hyp:δ),
and [a shift scale](hyp:L), [the pairwise stability constant](goal) is sixteen times the
pairwise aggregate factor times $L^3$. -/
def pairwiseStabilityConstant (p : ℕ) (M δ L : ℝ) : ℝ :=
  16 * pairwiseAggregateFactor p M δ L * L ^ 3

/-- For [a dimension](hyp:p), [a matrix scale](hyp:M), [a pairwise affine-separation margin](hyp:δ),
and [a shift scale](hyp:L), [the pairwise residual radius](goal) is the reciprocal of thirty-two
times the squared maximum of one and the pairwise aggregate factor, times the matrix scale.

Its use of $\max(1,\cdot)$ also covers the one-dimensional case, where the ordered-pair aggregate
vanishes. -/
def pairwiseResidualRadius (p : ℕ) (M δ L : ℝ) : ℝ :=
  1 / (32 * (max 1 (pairwiseAggregateFactor p M δ L)) ^ 2 * M)

/-- For [a dimension](hyp:p), [a matrix scale](hyp:M), [a pairwise affine-separation margin](hyp:δ),
[a shift scale](hyp:L), and [an inverse-norm envelope](hyp:J), [the pairwise local radius](goal)
is the stated minimum-based reference-neighborhood radius divided by the dimension and the
inverse-norm envelope.

The inverse-norm envelope is an upper bound for the reference inverse's Euclidean operator norm. -/
def pairwiseLocalRadius (p : ℕ) (M δ L J : ℝ) : ℝ :=
  min 1 (3 / (8 * max 1 (pairwiseAggregateFactor p M δ L) * M)) /
    ((p : ℝ) * J)

/-- For [a dimension](hyp:p) and [a condition-number envelope](hyp:κ), [the condition root](goal)
is $((p!)\kappa^{p-1})^{1/p}$. -/
def conditionRoot (p : ℕ) (κ : ℝ) : ℝ :=
  ((Nat.factorial p : ℝ) * κ ^ (p - 1)) ^ (1 / (p : ℝ))

/-- For [a dimension](hyp:p), [a real scale bound](hyp:L), and [a reference and candidate
matrix](hyp:B₀,B), [the pair matrix-norm bound](goal) holds exactly when both Euclidean operator
norms are at most the scale bound: [the reference matrix's norm is at most the bound](step:1) and
[the candidate matrix's norm is at most the bound](step:2). -/
def PairMatrixNormBound {p : ℕ} (L : ℝ) (B₀ B : SqMatrix p) : Prop :=
  ‖B₀‖ ≤ L ∧ ‖B‖ ≤ L

/-- For [a dimension](hyp:p), [a real neighborhood radius](hyp:ρ), and [a reference and candidate
matrix](hyp:B₀,B), [membership in the reference neighborhood](goal) holds exactly when their
entrywise Euclidean distance is at most the radius. -/
def InReferenceNeighborhood {p : ℕ} (ρ : ℝ) (B₀ B : SqMatrix p) : Prop :=
  entryL2 (B - B₀) ≤ ρ

/-- For [a dimension](hyp:p), [a condition-number envelope](hyp:κ), and [a square matrix](hyp:B),
[the determinant-condition envelope](goal) holds exactly when [the matrix is nonsingular](step:1),
[its determinant has absolute value at most $p!$](step:2), and [its Euclidean operator-norm
condition number is at most the envelope](step:3). -/
def DetConditionEnvelope {p : ℕ} (κ : ℝ) (B : SqMatrix p) : Prop :=
  IsUnit B.det ∧ |B.det| ≤ (Nat.factorial p : ℝ) ∧
    operatorConditionNumber B ≤ κ

/-- For [a dimension](hyp:p), [a condition-number envelope](hyp:κ), and [a reference and candidate
matrix](hyp:B₀,B), [the pair determinant-condition envelope](goal) holds exactly when [the
reference matrix satisfies that determinant-condition envelope](step:1) and [the candidate matrix
satisfies that determinant-condition envelope](step:2). -/
def PairDetConditionEnvelope {p : ℕ} (κ : ℝ) (B₀ B : SqMatrix p) : Prop :=
  DetConditionEnvelope κ B₀ ∧ DetConditionEnvelope κ B

/-- For [a dimension](hyp:p), [a matrix scale](hyp:M), [a pairwise affine-separation margin](hyp:δ),
[a shift scale](hyp:L), and [a reference and candidate matrix](hyp:B₀,B), [membership in the
identity branch](goal) holds exactly when [the transition error has entrywise Euclidean size at
most one](step:1) and [twice the pairwise aggregate factor times the matrix scale times that size
is at most one half](step:2). -/
def InIdentityBranch {p : ℕ} (M δ L : ℝ) (B₀ B : SqMatrix p) : Prop :=
  entryL2 (transitionError B₀ B) ≤ 1 ∧
    2 * pairwiseAggregateFactor p M δ L * M *
      entryL2 (transitionError B₀ B) ≤ 1 / 2

/-- For [positive shift scale and pairwise margin](hyp:hM,hδ) and [a matrix scale at
least one](hyp:hL), [the explicit residual threshold is strictly positive](goal). -/
theorem pairwiseResidualRadius_pos {p : ℕ} {M δ L : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hL : 1 ≤ L) :
    0 < pairwiseResidualRadius p M δ L := by
  unfold pairwiseResidualRadius
  positivity

/-- For [positive dimension, shift scale, pairwise margin, and inverse envelope](hyp:hp,hM,hδ,hJ) and [a matrix scale at least one](hyp:hL), [the explicit local
reference-neighborhood radius is strictly positive](goal). -/
theorem pairwiseLocalRadius_pos {p : ℕ} {M δ L J : ℝ}
    (hp : 0 < p) (hM : 0 < M) (hδ : 0 < δ) (hL : 1 ≤ L) (hJ : 0 < J) :
    0 < pairwiseLocalRadius p M δ L J := by
  unfold pairwiseLocalRadius
  positivity

private theorem exists_eigenvalue_eq_opNorm_sq {p : ℕ} (hp : 0 < p)
    (B : Matrix (Fin p) (Fin p) ℝ) :
    ∃ i : Fin p,
      (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues i = ‖B‖ ^ 2 := by
  letI : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  let hH := Matrix.isHermitian_conjTranspose_mul_self B
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ hH.eigenvalues Finset.univ_nonempty
  have hnonneg (j : Fin p) : 0 ≤ hH.eigenvalues j :=
    Matrix.eigenvalues_conjTranspose_mul_self_nonneg B j
  have heigNorm : ‖hH.eigenvalues‖ = hH.eigenvalues i := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (hnonneg i)]
      intro j
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg j)]
      exact hi j (Finset.mem_univ j)
    · have hj := norm_le_pi_norm hH.eigenvalues i
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg i)] at hj
      exact hj
  refine ⟨i, ?_⟩
  have hspectral := hH.spectral_theorem
  have hnorm : ‖B.transpose * B‖ = ‖hH.eigenvalues‖ := by
    calc
      ‖B.transpose * B‖ =
          ‖(Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
            (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues))‖ :=
        congrArg norm hspectral
      _ = ‖hH.eigenvalues‖ := by
        rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
          CStarRing.norm_mul_coe_unitary,
          CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
        simp
  rw [← heigNorm, ← hnorm]
  simpa [pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self B

private theorem opNorm_sq_le_condition_sq_mul_eigenvalue {p : ℕ} (hp : 0 < p)
    (B : Matrix (Fin p) (Fin p) ℝ)
    (hunit : IsUnit B.det) (j : Fin p) :
    ‖B‖ ^ 2 ≤ (‖B‖ * ‖B⁻¹‖) ^ 2 *
      (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues j := by
  letI : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  let hH := Matrix.isHermitian_conjTranspose_mul_self B
  let v : EuclideanSpace ℝ (Fin p) := hH.eigenvectorBasis j
  let w : EuclideanSpace ℝ (Fin p) :=
    (EuclideanSpace.equiv (Fin p) ℝ).symm (B *ᵥ WithLp.ofLp v)
  have hv : ‖v‖ = 1 := hH.eigenvectorBasis.orthonormal.norm_eq_one j
  have hleft :
      (EuclideanSpace.equiv (Fin p) ℝ).symm
          (B⁻¹ *ᵥ WithLp.ofLp w) = v := by
    ext i
    simp [w, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hunit]
  have hinv : 1 ≤ ‖B⁻¹‖ * ‖w‖ := by
    calc
      1 = ‖v‖ := hv.symm
      _ = ‖(EuclideanSpace.equiv (Fin p) ℝ).symm
          (B⁻¹ *ᵥ WithLp.ofLp w)‖ := congrArg norm hleft.symm
      _ ≤ ‖B⁻¹‖ * ‖w‖ := Matrix.l2_opNorm_mulVec B⁻¹ w
  have hw_sq : ‖w‖ ^ 2 = hH.eigenvalues j := by
    rw [hH.eigenvalues_eq]
    dsimp [w]
    rw [← Matrix.mulVec_mulVec]
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    dsimp [v]
    simp only [EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv,
      WithLp.ofLp_toLp]
    rw [Matrix.dotProduct_mulVec]
    simp only [star_trivial]
    rw [Matrix.vecMul_conjTranspose]
    simp [dotProduct, pow_two]
  have hsq : 1 ≤ ‖B⁻¹‖ ^ 2 * hH.eigenvalues j := by
    nlinarith [sq_nonneg (‖B⁻¹‖ * ‖w‖ - 1)]
  nlinarith [mul_nonneg (norm_nonneg B) (norm_nonneg B⁻¹)]

private theorem pow_le_of_prod_sq {p : ℕ} (hp : 0 < p)
    (s : Fin p → ℝ) (i : Fin p) {n c d : ℝ}
    (hn : 0 ≤ n) (hc : 0 ≤ c)
    (hi : s i = n ^ 2) (hprod : ∏ j, s j = d ^ 2)
    (hbound : ∀ j, n ^ 2 ≤ c ^ 2 * s j) :
    n ^ p ≤ |d| * c ^ (p - 1) := by
  have herase :
      ∏ _j ∈ (Finset.univ.erase i), n ^ 2 ≤
        ∏ j ∈ (Finset.univ.erase i), c ^ 2 * s j := by
    exact Finset.prod_le_prod (fun _ _ => sq_nonneg n) (fun j _ => hbound j)
  have hcard : (Finset.univ.erase i).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  rw [Finset.prod_const, hcard, Finset.prod_mul_distrib,
    Finset.prod_const, hcard] at herase
  have hfull : n ^ 2 * ∏ j ∈ (Finset.univ.erase i), s j = d ^ 2 := by
    rw [← hi, mul_comm, Finset.prod_erase_mul _ _ (Finset.mem_univ i), hprod]
  have hsq : (n ^ p) ^ 2 ≤ (|d| * c ^ (p - 1)) ^ 2 := by
    rw [mul_pow, sq_abs]
    calc
      (n ^ p) ^ 2 = n ^ 2 * (n ^ 2) ^ (p - 1) := by
        rw [← pow_mul, ← pow_succ']
        rw [Nat.sub_add_cancel hp]
        rw [Nat.mul_comm p 2, pow_mul]
      _ ≤ n ^ 2 * ((c ^ 2) ^ (p - 1) *
          ∏ j ∈ (Finset.univ.erase i), s j) := by
        gcongr
      _ = (c ^ 2) ^ (p - 1) * d ^ 2 := by rw [← hfull]; ring
      _ = d ^ 2 * (c ^ (p - 1)) ^ 2 := by
        rw [mul_comm, ← pow_mul, ← pow_mul]
        rw [Nat.mul_comm]
  exact (sq_le_sq₀ (pow_nonneg hn _)
    (mul_nonneg (abs_nonneg d) (pow_nonneg hc _))).mp hsq

private theorem opNorm_pow_le_det_mul_condition_pow {p : ℕ} (hp : 0 < p)
    (B : Matrix (Fin p) (Fin p) ℝ)
    (hunit : IsUnit B.det) :
    ‖B‖ ^ p ≤ |B.det| * operatorConditionNumber B ^ (p - 1) := by
  letI : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  let hH := Matrix.isHermitian_conjTranspose_mul_self B
  obtain ⟨i, hi⟩ := exists_eigenvalue_eq_opNorm_sq hp B
  apply pow_le_of_prod_sq hp hH.eigenvalues i (norm_nonneg B)
      (mul_nonneg (norm_nonneg B) (norm_nonneg B⁻¹))
  · exact hi
  · have hdet : (B.transpose * B).det = ∏ j, hH.eigenvalues j := by
      simpa using hH.det_eq_prod_eigenvalues
    rw [← hdet]
    simp [Matrix.det_mul, Matrix.det_transpose, pow_two]
  · intro j
    exact opNorm_sq_le_condition_sq_mul_eigenvalue hp B hunit j

/-- For [positive dimension](hyp:hp) and [a condition envelope at least one](hyp:hκ),
[the determinant/condition root is at least one](goal). -/
theorem one_le_conditionRoot {p : ℕ} {κ : ℝ} (hp : 0 < p) (hκ : 1 ≤ κ) :
    1 ≤ conditionRoot p κ := by
  unfold conditionRoot
  apply Real.one_le_rpow
  · have hf : (1 : ℝ) ≤ Nat.factorial p := by
      exact_mod_cast Nat.factorial_pos p
    have hk : (1 : ℝ) ≤ κ ^ (p - 1) := one_le_pow₀ hκ
    nlinarith
  · positivity

/-- For [positive dimension](hyp:hp), [condition envelope at least one](hyp:hκ), [a
unit-diagonal matrix](hyp:hdiag), and [its determinant/condition envelope](hyp:henv),
[the matrix operator norm is bounded by the determinant/condition root](goal). -/
-- Proof route: a unit diagonal entry gives `1 ≤ ‖B‖`.  Order the singular values;
-- `cond(B) ≤ κ` bounds every lower singular value below by `‖B‖/κ`, while their
-- product is `|det B| ≤ p!`.  Take the positive `p`-th root.
theorem opNorm_le_conditionRoot {p : ℕ} {κ : ℝ} (B : SqMatrix p)
    (hp : 0 < p) (hκ : 1 ≤ κ) (hdiag : UnitDiagonal B)
    (henv : DetConditionEnvelope κ B) :
    ‖B‖ ≤ conditionRoot p κ := by
  have hcond_nonneg : 0 ≤ operatorConditionNumber B :=
    mul_nonneg (norm_nonneg B) (norm_nonneg B⁻¹)
  have hpow : ‖B‖ ^ p ≤ (Nat.factorial p : ℝ) * κ ^ (p - 1) := by
    calc
      ‖B‖ ^ p ≤ |B.det| * operatorConditionNumber B ^ (p - 1) :=
        opNorm_pow_le_det_mul_condition_pow hp B henv.1
      _ ≤ (Nat.factorial p : ℝ) * κ ^ (p - 1) := by
        exact mul_le_mul henv.2.1
          (pow_le_pow_left₀ hcond_nonneg henv.2.2 _)
          (pow_nonneg hcond_nonneg _) (by positivity)
  unfold conditionRoot
  have hrpow := Real.rpow_le_rpow (pow_nonneg (norm_nonneg B) _) hpow
    (show 0 ≤ 1 / (p : ℝ) by positivity)
  calc
    ‖B‖ = (‖B‖ ^ p) ^ (1 / (p : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (norm_nonneg B)]
      have hpR : (p : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel₀ 1 hpR, Real.rpow_one]
    _ ≤ ((Nat.factorial p : ℝ) * κ ^ (p - 1)) ^ (1 / (p : ℝ)) := hrpow

/-- For [positive dimension](hyp:hp), [condition envelope at least one](hyp:hκ),
[unit diagonals](hyp:hdiag₀,hdiag), and [a common determinant/condition envelope](hyp:henv),
[both matrix norms obey the common `conditionRoot` bound](goal). -/
theorem pairMatrixNormBound_conditionRoot {p : ℕ} {κ : ℝ} (B₀ B : SqMatrix p)
    (hp : 0 < p) (hκ : 1 ≤ κ) (hdiag₀ : UnitDiagonal B₀)
    (hdiag : UnitDiagonal B) (henv : PairDetConditionEnvelope κ B₀ B) :
    PairMatrixNormBound (conditionRoot p κ) B₀ B := by
  exact ⟨opNorm_le_conditionRoot B₀ hp hκ hdiag₀ henv.1,
    opNorm_le_conditionRoot B hp hκ hdiag henv.2⟩

end Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine
