/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Quantitative.Quantitative
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pairwise-affine simultaneous-congruence stability: definitions

This module defines pair-dependent affine-minor separation, off-diagonal approximate
simultaneous congruence, the entrywise Euclidean matrix norm used for aggregation, and
the explicit constants and scale envelopes used by the local stability theorem.

Unlike `AffineMinorSeparated`, the separation predicate here does not select one common
base and a full-dimensional minor.  Its three witnessing environments may depend on the
coordinate pair.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence

open Causalean.Discovery.LinearDisentanglement.Quantitative

/-- [The pairwise affine determinant](goal) measures whether three environmental shifts span area
in [coordinates `i,j`](hyp:i,j), using [shift family `s`](hyp:s) and [environments
`e₀,e₁,e₂`](hyp:e₀,e₁,e₂) from [collection `E`](hyp:E) in [dimension `p`](hyp:p). -/
def pairAffineDet {p : ℕ} {E : Type*} (s : E → Fin p → ℝ)
    (i j : Fin p) (e₀ e₁ e₂ : E) : ℝ :=
  (s e₁ i - s e₀ i) * (s e₂ j - s e₀ j) -
    (s e₂ i - s e₀ i) * (s e₁ j - s e₀ j)

/-- [Pairwise affine separation](goal) ensures every coordinate pair receives enough independent
environmental movement to be distinguished: [shift family `s`](hyp:s) over [finite environments
`E`](hyp:E) has a three-environment area of at least [margin `δ`](hyp:δ) for every pair in
[dimension `p`](hyp:p). -/
def PairwiseAffineSeparated {p : ℕ} {E : Type*} [Fintype E]
    (s : E → Fin p → ℝ) (δ : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ e₀ e₁ e₂ : E, δ ≤ |pairAffineDet s i j e₀ e₁ e₂|

/-- [Off-diagonal approximate congruence](goal) accepts [candidate coordinates `B`](hyp:B) when all
cross-coordinate terms of [observed matrices `A`](hyp:A) stay below [tolerance `ε`](hyp:ε), over
[finite environments `E`](hyp:E) in [dimension `p`](hyp:p).

Its diagonal output is deliberately left unrestricted. -/
def OffDiagonalApproximateCongruence {p : ℕ} {E : Type*} [Fintype E]
    (A : E → SqMatrix p) (B : SqMatrix p) (ε : ℝ) : Prop :=
  ∀ e i j, i ≠ j → |(B * A e * B.transpose) i j| ≤ ε

/-- [The transition error](goal) directly measures departure from exact recovery by comparing
[candidate coordinates with reference coordinates](hyp:B₀,B) in [dimension `p`](hyp:p). -/
def transitionError {p : ℕ} (B₀ B : SqMatrix p) : SqMatrix p :=
  transition B₀ B - 1

/-- [The entrywise Euclidean size](goal) aggregates all coordinate errors of [matrix `R`](hyp:R) in
[dimension `p`](hyp:p), using its Frobenius norm.

This is a named abbreviation for Mathlib's Frobenius norm (`Matrix.frobeniusNormedAddCommGroup`),
not a separate notion.  It is kept as a function because these files use the Euclidean operator
norm as the ambient matrix norm `‖·‖`, and several statements compare the two norms. -/
def entryL2 {p : ℕ} (R : SqMatrix p) : ℝ :=
  @norm (SqMatrix p) Matrix.frobeniusNormedAddCommGroup.toNorm R

/-- [The entrywise Euclidean size is exactly the Frobenius norm](goal) for [matrix `R`](hyp:R) in
[dimension `p`](hyp:p), allowing standard matrix-norm results to apply directly. -/
theorem entryL2_eq_frobenius_norm {p : ℕ} (R : SqMatrix p) :
    entryL2 R = @norm (SqMatrix p) Matrix.frobeniusNormedAddCommGroup.toNorm R := rfl

/-- [Entrywise Euclidean size is the root-sum-of-squares of all entries](goal) for [matrix
`R`](hyp:R) in [dimension `p`](hyp:p). -/
theorem entryL2_eq_sqrt {p : ℕ} (R : SqMatrix p) :
    entryL2 R = Real.sqrt (∑ i, ∑ j, |R i j| ^ 2) := by
  rw [entryL2, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs]

/-- [Entrywise Euclidean size cannot be negative](goal) for [matrix `R`](hyp:R) in [dimension
`p`](hyp:p), as required for radius and error bounds. -/
theorem entryL2_nonneg {p : ℕ} (R : SqMatrix p) : 0 ≤ entryL2 R := by
  rw [entryL2_eq_sqrt]
  exact Real.sqrt_nonneg _

/-- [The pairwise solve factor](goal) converts off-diagonal residuals into coordinate-pair error;
it grows with [shift scale `M`](hyp:M) and shrinks with [separation margin `δ`](hyp:δ).

The factor six leaves room for centering and triangle inequalities while retaining the requested
specialization. -/
def pairwiseSolveFactor (M δ : ℝ) : ℝ :=
  6 * M / δ

/-- [The pairwise aggregate factor](goal) combines all ordered coordinate-pair errors under
[dimension `p`](hyp:p), [shift scale `M`](hyp:M), [separation margin `δ`](hyp:δ), and [matrix
scale `L`](hyp:L). -/
def pairwiseAggregateFactor (p : ℕ) (M δ L : ℝ) : ℝ :=
  pairwiseSolveFactor M δ *
    Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2))

/-- [The pairwise stability constant](goal) turns residual size into diagonalizer error under
[dimension `p`](hyp:p), [shift scale `M`](hyp:M), [separation margin `δ`](hyp:δ), and [matrix
scale `L`](hyp:L). -/
def pairwiseStabilityConstant (p : ℕ) (M δ L : ℝ) : ℝ :=
  16 * pairwiseAggregateFactor p M δ L * L ^ 3

/-- [The pairwise residual radius](goal) sets the noise threshold used to enter
the identity branch, determined by [dimension `p`](hyp:p), [shift scale `M`](hyp:M), [separation
margin `δ`](hyp:δ), and [matrix scale `L`](hyp:L).

Its use of $\max(1,\cdot)$ also covers the one-dimensional case, where the ordered-pair aggregate
vanishes. -/
def pairwiseResidualRadius (p : ℕ) (M δ L : ℝ) : ℝ :=
  1 / (32 * (max 1 (pairwiseAggregateFactor p M δ L)) ^ 2 * M)

/-- [The pairwise local radius](goal) sets the reference-neighborhood size used to force a candidate
onto the identity branch, determined by [dimension `p`](hyp:p), [shift scale `M`](hyp:M),
[separation margin `δ`](hyp:δ), [matrix scale `L`](hyp:L), and [inverse-norm envelope
`J`](hyp:J).

The inverse-norm envelope is an upper bound for the reference inverse's Euclidean operator norm. -/
def pairwiseLocalRadius (p : ℕ) (M δ L J : ℝ) : ℝ :=
  min 1 (3 / (8 * max 1 (pairwiseAggregateFactor p M δ L) * M)) /
    ((p : ℝ) * J)

/-- [The condition root](goal) is the scale used to convert determinant and condition information
operator-norm bound in [dimension `p`](hyp:p) under [condition envelope `κ`](hyp:κ). At dimension
zero the exponent conventions make the value one. -/
def conditionRoot (p : ℕ) (κ : ℝ) : ℝ :=
  ((Nat.factorial p : ℝ) * κ ^ (p - 1)) ^ (1 / (p : ℝ))

/-- [The pair matrix-norm bound](goal) keeps [reference and candidate matrices](hyp:B₀,B) within
[scale `L`](hyp:L) in [dimension `p`](hyp:p); it is [the canonical pair matrix-scale
condition](step:1) under a compatibility name. -/
abbrev PairMatrixNormBound {p : ℕ} (L : ℝ) (B₀ B : SqMatrix p) : Prop :=
  PairMatrixScaleBound L B₀ B

/-- [Membership in the reference neighborhood](goal) requires [candidate and reference
matrices](hyp:B₀,B) to differ by at most [entrywise radius `ρ`](hyp:ρ) in [dimension
`p`](hyp:p). -/
def InReferenceNeighborhood {p : ℕ} (ρ : ℝ) (B₀ B : SqMatrix p) : Prop :=
  entryL2 (B - B₀) ≤ ρ

/-- [The determinant-condition envelope](goal) rules out unstable [matrices `B`](hyp:B) in
[dimension `p`](hyp:p) by requiring (1) [nonsingularity](step:1), (2) [a factorial determinant
cap](step:2), and (3) [condition number at most envelope `κ`](step:3) for [that
envelope](hyp:κ). -/
def DetConditionEnvelope {p : ℕ} (κ : ℝ) (B : SqMatrix p) : Prop :=
  IsUnit B.det ∧ |B.det| ≤ (Nat.factorial p : ℝ) ∧
    operatorConditionNumber B ≤ κ

/-- [The pair determinant-condition envelope](goal) places [reference and candidate
matrices](hyp:B₀,B) in the same stable class in [dimension `p`](hyp:p): (1) [the reference meets
the envelope](step:1) and (2) [the candidate meets it](step:2), for [condition limit
`κ`](hyp:κ). -/
def PairDetConditionEnvelope {p : ℕ} (κ : ℝ) (B₀ B : SqMatrix p) : Prop :=
  DetConditionEnvelope κ B₀ ∧ DetConditionEnvelope κ B

/-- [Membership in the identity branch](goal) rules out large relabeling or sign ambiguities for
[reference and candidate matrices](hyp:B₀,B) in [dimension `p`](hyp:p), under [shift scale,
separation, and matrix scale](hyp:M,δ,L): (1) [transition error is at most one](step:1), and (2)
[its amplified pairwise error is at most one half](step:2). -/
def InIdentityBranch {p : ℕ} (M δ L : ℝ) (B₀ B : SqMatrix p) : Prop :=
  entryL2 (transitionError B₀ B) ≤ 1 ∧
    2 * pairwiseAggregateFactor p M δ L * M *
      entryL2 (transitionError B₀ B) ≤ 1 / 2

/-- [The explicit pairwise residual threshold is strictly positive](goal) when [shift scale `M`
and separation margin `δ`](hyp:M,δ) are [positive](hyp:hM,hδ), [matrix scale `L`](hyp:L) is [at
least one](hyp:hL), and the model has [dimension `p`](hyp:p). -/
theorem pairwiseResidualRadius_pos {p : ℕ} {M δ L : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hL : 1 ≤ L) :
    0 < pairwiseResidualRadius p M δ L := by
  unfold pairwiseResidualRadius
  positivity

/-- [The explicit local reference-neighborhood radius is strictly positive](goal) when [dimension
`p`, shift scale `M`, separation margin `δ`, and inverse envelope `J`](hyp:p,M,δ,J) are
[positive](hyp:hp,hM,hδ,hJ) and [matrix scale `L`](hyp:L) is [at least one](hyp:hL). -/
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

/-- [The determinant-condition root is at least one](goal) in [dimension `p`](hyp:p) under
[condition envelope `κ`](hyp:κ), provided [the dimension is positive](hyp:hp) and [the envelope
is at least one](hyp:hκ). -/
theorem one_le_conditionRoot {p : ℕ} {κ : ℝ} (hp : 0 < p) (hκ : 1 ≤ κ) :
    1 ≤ conditionRoot p κ := by
  unfold conditionRoot
  apply Real.one_le_rpow
  · have hf : (1 : ℝ) ≤ Nat.factorial p := by
      exact_mod_cast Nat.factorial_pos p
    have hk : (1 : ℝ) ≤ κ ^ (p - 1) := one_le_pow₀ hκ
    nlinarith
  · positivity

/-- [The determinant-condition root bounds the matrix operator norm](goal), turning [matrix
`B`](hyp:B)'s [determinant-condition certificate](hyp:henv) into a scale bound in [dimension
`p`](hyp:p) for [condition envelope `κ`](hyp:κ), when [the dimension is positive](hyp:hp) and
[the envelope is at least one](hyp:hκ). -/
-- Proof route: order the singular values;
-- `cond(B) ≤ κ` bounds every lower singular value below by `‖B‖/κ`, while their
-- product is `|det B| ≤ p!`.  Take the positive `p`-th root.
theorem opNorm_le_conditionRoot {p : ℕ} {κ : ℝ} (B : SqMatrix p)
    (hp : 0 < p) (hκ : 1 ≤ κ)
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

/-- [One determinant-condition certificate yields a common operator-norm bound for both
matrices](goal), for [reference and candidate `B₀,B`](hyp:B₀,B) in [dimension `p`](hyp:p) under
[condition envelope `κ`](hyp:κ), assuming [positive dimension](hyp:hp), [envelope at least
one](hyp:hκ), and [the shared certificate](hyp:henv). -/
theorem pairMatrixNormBound_conditionRoot {p : ℕ} {κ : ℝ} (B₀ B : SqMatrix p)
    (hp : 0 < p) (hκ : 1 ≤ κ) (henv : PairDetConditionEnvelope κ B₀ B) :
    PairMatrixNormBound (conditionRoot p κ) B₀ B := by
  exact ⟨opNorm_le_conditionRoot B₀ hp hκ henv.1,
    opNorm_le_conditionRoot B hp hκ henv.2⟩

end Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence
