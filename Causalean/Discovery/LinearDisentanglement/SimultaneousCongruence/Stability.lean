/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.LocalBranch

/-!
# Local operator-norm stability from pairwise affine separation

This module aggregates the pair-dependent two-coordinate estimates, uses an explicit
small-residual threshold and ordinary local neighborhood to select the identity branch,
converts entrywise L² control to Euclidean operator norm, and specializes the result to a
determinant/condition-number envelope.
-/

public section

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence

open Causalean.Discovery.LinearDisentanglement.Quantitative

open scoped Matrix.Norms.Frobenius in
private theorem l2CLM_norm_le_frobenius {p : ℕ} (R : SqMatrix p) :
    ‖(Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)) R‖ ≤ ‖R‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R) fun x => ?_
  have hmul := Matrix.frobenius_norm_mul R
    (Matrix.replicateCol Unit (WithLp.ofLp x))
  have heq :
      R * Matrix.replicateCol Unit (WithLp.ofLp x) =
        Matrix.replicateCol Unit (R *ᵥ WithLp.ofLp x) := by
    ext i u
    simp [Matrix.mul_apply, Matrix.mulVec, Matrix.replicateCol, dotProduct]
  rw [heq, Matrix.frobenius_norm_replicateCol] at hmul
  rw [← Matrix.toEuclideanCLM_toLp R (WithLp.ofLp x), WithLp.toLp_ofLp] at hmul
  simpa using hmul

/-- [Operator norm is bounded by entrywise Euclidean size](goal), allowing aggregate control of
[matrix error `R`](hyp:R) in [dimension `p`](hyp:p) to imply worst-direction control. -/
theorem opNorm_le_entryL2 {p : ℕ} (R : SqMatrix p) :
    ‖R‖ ≤ entryL2 R := by
  rw [Matrix.cstar_norm_def]
  calc
    ‖(Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)) R‖ ≤
        @norm (SqMatrix p) Matrix.frobeniusNormedAddCommGroup.toNorm R :=
      l2CLM_norm_le_frobenius R
    _ = entryL2 R := rfl

/-- [Candidate-reference error factors through transition error](goal), converting relative error
back to the original scale for [reference and candidate matrices](hyp:B₀,B) in [dimension
`p`](hyp:p) when [the reference is invertible](hyp:hunit). -/
theorem sub_eq_transitionError_mul {p : ℕ} (B₀ B : SqMatrix p)
    (hunit : IsUnit B₀.det) :
    B - B₀ = transitionError B₀ B * B₀ := by
  rw [transitionError, Matrix.sub_mul, Matrix.one_mul, transition]
  rw [Matrix.nonsing_inv_mul_cancel_right B₀ B hunit]

/-- **Local pairwise-affine simultaneous-congruence stability.** For [positive dimension,
shift scale, and affine margin](hyp:hp,hM,hδ), [a matrix scale at least one](hyp:hL),
[bounded pairwise-separated shifts](hyp:hscale,hsep), [an exact invertible unit-diagonal reference](hyp:hunit,hexact,hdiag₀),
[a unit-diagonal candidate](hyp:hdiag), [a reference operator norm at most the matrix
scale](hyp:hB₀), [nonnegative
off-diagonal residual tolerance](hyp:hε), [off-diagonal approximate feasibility](hyp:happrox),
and [the explicit local identity-branch condition](hyp:hbranch), [the candidate-reference
Euclidean operator distance is linear in the residual](goal). -/
-- Proof route: `pairwise_offDiagonal_control` and `entryL2_transitionError_le` give
-- `u ≤ K (2 M u² + 2ε)`.  The second identity-branch inequality absorbs the quadratic
-- term, yielding `u ≤ 4Kε`.  Factor `B-B₀ = R B₀`, use
-- `‖R‖op ≤ entryL2 R`, and weaken `4KL` to the displayed `16KL³` using `1 ≤ L`.
theorem opNorm_sub_le_of_pairwise_affine_in_identity_branch {p : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix p) (s : E → Fin p → ℝ) (B₀ B : SqMatrix p)
    {M δ L ε : ℝ}
    (hp : 0 < p) (hM : 0 < M) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hscale : ShiftScaleBound s M) (hsep : PairwiseAffineSeparated s δ)
    (hunit : IsUnit B₀.det) (hexact : ExactCongruence A s B₀)
    (hdiag₀ : UnitDiagonal B₀) (hdiag : UnitDiagonal B)
    (hB₀ : ‖B₀‖ ≤ L)
    (hε : 0 ≤ ε) (happrox : OffDiagonalApproximateCongruence A B ε)
    (hbranch : InIdentityBranch M δ L B₀ B) :
    ‖B - B₀‖ ≤ pairwiseStabilityConstant p M δ L * ε := by
  let R := transitionError B₀ B
  let K := pairwiseAggregateFactor p M δ L
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hK0 : 0 ≤ K := by
    dsimp [K, pairwiseAggregateFactor, pairwiseSolveFactor]
    positivity
  have hu0 : 0 ≤ entryL2 R := entryL2_nonneg R
  have hc0 : 0 ≤ pairwiseSolveFactor M δ *
      (2 * M * entryL2 R ^ 2 + 2 * ε) := by
    unfold pairwiseSolveFactor
    positivity
  have hoff : ∀ i j, i ≠ j →
      |R i j| ≤ pairwiseSolveFactor M δ *
        (2 * M * entryL2 R ^ 2 + 2 * ε) := by
    simpa [R] using pairwise_offDiagonal_control A s B₀ B hM.le hδ hε
      hscale hsep hunit hexact happrox
  have hu := entryL2_transitionError_le B₀ B hp hL0 hc0 hunit hdiag₀ hdiag
    hB₀ hoff
  have huK : entryL2 R ≤ K * (2 * M * entryL2 R ^ 2 + 2 * ε) := by
    change entryL2 R ≤ pairwiseSolveFactor M δ *
      (2 * M * entryL2 R ^ 2 + 2 * ε) *
        Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2)) at hu
    calc
      entryL2 R ≤ pairwiseSolveFactor M δ *
          (2 * M * entryL2 R ^ 2 + 2 * ε) *
            Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2)) := hu
      _ = K * (2 * M * entryL2 R ^ 2 + 2 * ε) := by
        dsimp [K, pairwiseAggregateFactor]
        ring
  have hbranch' : 2 * K * M * entryL2 R ≤ 1 / 2 := by
    simpa [R, K, InIdentityBranch] using hbranch.2
  have hquad : K * (2 * M * entryL2 R ^ 2) ≤ entryL2 R / 2 := by
    nlinarith [mul_nonneg hu0
      (sub_nonneg.mpr hbranch')]
  have huLinear : entryL2 R ≤ 4 * K * ε := by
    nlinarith
  rw [sub_eq_transitionError_mul B₀ B hunit]
  calc
    ‖transitionError B₀ B * B₀‖ ≤ ‖transitionError B₀ B‖ * ‖B₀‖ := norm_mul_le _ _
    _ ≤ entryL2 R * L := by
      exact mul_le_mul (by simpa [R] using opNorm_le_entryL2 R) hB₀
        (norm_nonneg _) hu0
    _ ≤ (4 * K * ε) * L := by gcongr
    _ ≤ pairwiseStabilityConstant p M δ L * ε := by
      unfold pairwiseStabilityConstant
      dsimp [K]
      have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
      have hcoef : 4 * L ≤ 16 * L ^ 3 := by nlinarith
      calc
        (4 * pairwiseAggregateFactor p M δ L * ε) * L =
            (pairwiseAggregateFactor p M δ L * ε) * (4 * L) := by ring
        _ ≤ (pairwiseAggregateFactor p M δ L * ε) * (16 * L ^ 3) :=
          mul_le_mul_of_nonneg_left hcoef (mul_nonneg hK0 hε)
        _ = 16 * pairwiseAggregateFactor p M δ L * L ^ 3 * ε := by ring

/-- **Small-residual local pairwise-affine simultaneous-congruence stability.** For
[positive dimension, shift scale, affine margin, matrix scale, and inverse envelope](hyp:hp,hM,hδ,hL,hJ), [bounded pairwise-separated shifts](hyp:hscale,hsep), [an exact
invertible unit-diagonal reference](hyp:hunit,hexact,hdiag₀), [a unit-diagonal
candidate](hyp:hdiag), [a reference operator norm at most the matrix scale](hyp:hB₀), [a reference inverse bound](hyp:hinv), [nonnegative
off-diagonal residual below the explicit threshold](hyp:hε,hsmall), [approximate
feasibility](hyp:happrox), and [membership in the explicit entrywise-L² neighborhood of
the reference](hyp:hlocal), [the candidate-reference Euclidean operator distance is linear
in the residual](goal). -/
theorem opNorm_sub_le_of_pairwise_affine {p : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix p) (s : E → Fin p → ℝ) (B₀ B : SqMatrix p)
    {M δ L J ε : ℝ}
    (hp : 0 < p) (hM : 0 < M) (hδ : 0 < δ) (hL : 1 ≤ L) (hJ : 0 < J)
    (hscale : ShiftScaleBound s M) (hsep : PairwiseAffineSeparated s δ)
    (hunit : IsUnit B₀.det) (hexact : ExactCongruence A s B₀)
    (hdiag₀ : UnitDiagonal B₀) (hdiag : UnitDiagonal B)
    (hB₀ : ‖B₀‖ ≤ L) (hinv : ‖B₀⁻¹‖ ≤ J)
    (hε : 0 ≤ ε) (hsmall : ε ≤ pairwiseResidualRadius p M δ L)
    (happrox : OffDiagonalApproximateCongruence A B ε)
    (hlocal : InReferenceNeighborhood (pairwiseLocalRadius p M δ L J) B₀ B) :
    ‖B - B₀‖ ≤ pairwiseStabilityConstant p M δ L * ε := by
  have hbranch := inIdentityBranch_of_small_residual A s B₀ B hp hM hδ hL hJ
    hscale hsep hunit hexact hdiag₀ hdiag hB₀ hinv hε hsmall happrox hlocal
  exact opNorm_sub_le_of_pairwise_affine_in_identity_branch A s B₀ B hp hM hδ hL
    hscale hsep hunit hexact hdiag₀ hdiag hB₀ hε happrox hbranch

/-- [The determinant-condition envelope yields the advertised local operator-norm stability
rate](goal), replacing an abstract matrix scale by its explicit condition root. For [matrix
family, shifts, reference, and candidate](hyp:A,s,B₀,B) over [environments `E`](hyp:E) in
[dimension `p`](hyp:p), with [scale, margin, condition, and residual parameters](hyp:M,γ,κ,ε),
this uses [positive dimension, scale, and margin with condition at least one](hyp:hp,hM,hγ,hκ),
[bounded separated shifts](hyp:hscale,hsep), [normalized matrices and a conditioned
reference](hyp:hdiag₀,hdiag,hcond), [exact and approximate feasibility](hyp:hexact,happrox),
[nonnegative residual](hyp:hε), and [the small-residual and local-neighborhood
conditions](hyp:hsmall,hlocal). -/
theorem opNorm_sub_le_condition_specialization {p : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix p) (s : E → Fin p → ℝ) (B₀ B : SqMatrix p)
    {M γ κ ε : ℝ}
    (hp : 0 < p) (hM : 0 < M) (hγ : 0 < γ) (hκ : 1 ≤ κ)
    (hscale : ShiftScaleBound s M) (hsep : PairwiseAffineSeparated s γ)
    (hdiag₀ : UnitDiagonal B₀) (hdiag : UnitDiagonal B)
    (hcond : DetConditionEnvelope κ B₀)
    (hexact : ExactCongruence A s B₀)
    (hε : 0 ≤ ε) (happrox : OffDiagonalApproximateCongruence A B ε)
    (hsmall : ε ≤ pairwiseResidualRadius p M γ (conditionRoot p κ))
    (hlocal : InReferenceNeighborhood
      (pairwiseLocalRadius p M γ (conditionRoot p κ) κ) B₀ B) :
    ‖B - B₀‖ ≤
      16 * (6 * M / γ) *
        Real.sqrt ((p : ℝ) * (p - 1 : ℕ) *
          (1 + conditionRoot p κ ^ 2)) *
        conditionRoot p κ ^ 3 * ε := by
  have hL : 1 ≤ conditionRoot p κ := one_le_conditionRoot hp hκ
  have hB₀ : ‖B₀‖ ≤ conditionRoot p κ :=
    opNorm_le_conditionRoot B₀ hp hκ hcond
  have hinv : ‖B₀⁻¹‖ ≤ κ :=
    invOpNorm_le_conditionEnvelope B₀ hp hdiag₀ hcond
  have hJ : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have h := opNorm_sub_le_of_pairwise_affine (J := κ) A s B₀ B hp hM hγ hL hJ
    hscale hsep hcond.1 hexact hdiag₀ hdiag hB₀ hinv hε hsmall happrox hlocal
  calc
    ‖B - B₀‖ ≤ pairwiseStabilityConstant p M γ (conditionRoot p κ) * ε := h
    _ = 16 * (6 * M / γ) *
        Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + conditionRoot p κ ^ 2)) *
        conditionRoot p κ ^ 3 * ε := by
      unfold pairwiseStabilityConstant pairwiseAggregateFactor pairwiseSolveFactor
      ring

end Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence
