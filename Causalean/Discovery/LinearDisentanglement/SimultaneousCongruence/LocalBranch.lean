/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence.PairwiseControl

/-!
# Local branch selection for pairwise-affine congruence stability

This module converts an ordinary entrywise-L² neighborhood of the reference into control
of the transition error.  It then combines that control with an explicit small-residual
threshold and the pairwise quadratic estimate to select the identity branch.  Thus the
stability API does not ask callers to assume the desired transition-error bound directly.
-/

public section

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence

open Causalean.Discovery.LinearDisentanglement.Quantitative

/-- [Entrywise Euclidean size is submultiplicative](goal), so errors do not amplify beyond the
product of the sizes of [matrices `X` and `Y`](hyp:X,Y) in [dimension `p`](hyp:p). -/
theorem entryL2_mul_le {p : ℕ} (X Y : SqMatrix p) :
    entryL2 (X * Y) ≤ entryL2 X * entryL2 Y := by
  exact Matrix.frobenius_norm_mul X Y

/-- [Entrywise Euclidean size is at most dimension times operator norm](goal) for [matrix
`X`](hyp:X) in [dimension `p`](hyp:p), provided [the dimension is positive](hyp:hp). -/
theorem entryL2_le_dimension_mul_opNorm {p : ℕ} (X : SqMatrix p) (hp : 0 < p) :
    entryL2 X ≤ (p : ℝ) * ‖X‖ := by
  rw [entryL2_eq_sqrt, Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      ∑ i, ∑ j, |X i j| ^ 2 ≤ ∑ _i : Fin p, ∑ _j : Fin p, ‖X‖ ^ 2 := by
        gcongr with i j
        exact abs_entry_le_opNorm X i j
      _ = ((p : ℝ) * ‖X‖) ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring

/-- [Transition error is the candidate-reference discrepancy expressed in reference
coordinates](goal), for [reference and candidate matrices](hyp:B₀,B) in [dimension `p`](hyp:p)
when [the reference is invertible](hyp:hunit). -/
theorem transitionError_eq_sub_mul_inv {p : ℕ} (B₀ B : SqMatrix p)
    (hunit : IsUnit B₀.det) :
    transitionError B₀ B = (B - B₀) * B₀⁻¹ := by
  unfold transitionError transition
  rw [Matrix.sub_mul, Matrix.mul_nonsing_inv B₀ hunit]

/-- [A local candidate neighborhood yields a quantitative transition-error bound](goal) for
[reference and candidate matrices](hyp:B₀,B) in [dimension `p`](hyp:p), with [inverse envelope
`J` and radius `ρ`](hyp:J,ρ), [positive dimension and nonnegative envelope](hyp:hp,hJ), [invertible
reference](hyp:hunit), [bounded reference inverse](hyp:hinv), and [local proximity](hyp:hlocal). -/
theorem transitionError_entryL2_le_of_neighborhood {p : ℕ} (B₀ B : SqMatrix p)
    {J ρ : ℝ} (hp : 0 < p) (hJ : 0 ≤ J)
    (hunit : IsUnit B₀.det) (hinv : ‖B₀⁻¹‖ ≤ J)
    (hlocal : InReferenceNeighborhood ρ B₀ B) :
    entryL2 (transitionError B₀ B) ≤ (p : ℝ) * J * ρ := by
  rw [transitionError_eq_sub_mul_inv B₀ B hunit]
  calc
    entryL2 ((B - B₀) * B₀⁻¹) ≤ entryL2 (B - B₀) * entryL2 B₀⁻¹ :=
      entryL2_mul_le _ _
    _ ≤ ρ * ((p : ℝ) * J) := by
      have hρ : 0 ≤ ρ := (entryL2_nonneg _).trans hlocal
      apply mul_le_mul hlocal
      · exact (entryL2_le_dimension_mul_opNorm B₀⁻¹ hp).trans
          (mul_le_mul_of_nonneg_left hinv (by positivity))
      · exact entryL2_nonneg _
      · exact hρ
    _ = (p : ℝ) * J * ρ := by ring

/-- [A unit-diagonal determinant-condition certificate bounds the inverse operator norm](goal) for
[matrix `B`](hyp:B) in [dimension `p`](hyp:p) under [condition envelope `κ`](hyp:κ), assuming
[positive dimension](hyp:hp), [unit diagonal](hyp:hdiag), and [the certificate](hyp:henv). -/
theorem invOpNorm_le_conditionEnvelope {p : ℕ} {κ : ℝ} (B : SqMatrix p)
    (hp : 0 < p) (hdiag : UnitDiagonal B) (henv : DetConditionEnvelope κ B) :
    ‖B⁻¹‖ ≤ κ := by
  letI : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  let i : Fin p := Classical.choice (inferInstance : Nonempty (Fin p))
  have hB : 1 ≤ ‖B‖ := by
    simpa [hdiag i] using abs_entry_le_opNorm B i i
  calc
    ‖B⁻¹‖ ≤ ‖B‖ * ‖B⁻¹‖ := by
      nlinarith [norm_nonneg B⁻¹]
    _ = operatorConditionNumber B := rfl
    _ ≤ κ := henv.2.2

/-- **Small-residual local identity-branch selection.** For [positive dimension, shift
scale, affine margin, matrix scale, and inverse envelope](hyp:hp,hM,hδ,hL,hJ),
[bounded pairwise-separated shifts](hyp:hscale,hsep), [an exact invertible unit-diagonal
reference](hyp:hunit,hexact,hdiag₀), [a unit-diagonal candidate](hyp:hdiag), [a reference operator norm at most the matrix
scale](hyp:hB₀), [an inverse bound](hyp:hinv), [nonnegative approximate residual](hyp:hε,happrox), [the explicit residual smallness condition](hyp:hsmall), and [membership
in the explicit ordinary reference neighborhood](hyp:hlocal), [the transition lies on the
identity branch needed by the linear stability estimate](goal). -/
-- Proof route: the neighborhood and inverse envelope give `u ≤ min 1 (3/(8 max(1,K)M))`
-- for `u = entryL2 R`.  Pairwise control gives `u ≤ 2 K M u² + 2 K ε`; the coarse
-- local bound absorbs three quarters of `u`, and the residual radius improves this to
-- `2 K M u ≤ 1/2`.  This derives, rather than assumes, `InIdentityBranch`.
theorem inIdentityBranch_of_small_residual {p : ℕ} {E : Type*}
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
    InIdentityBranch M δ L B₀ B := by
  let R := transitionError B₀ B
  let u := entryL2 R
  let K := pairwiseAggregateFactor p M δ L
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hK0 : 0 ≤ K := by
    dsimp [K, pairwiseAggregateFactor, pairwiseSolveFactor]
    positivity
  have hmax : 0 < max 1 K := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hKmax : K ≤ max 1 K := le_max_right _ _
  have hu0 : 0 ≤ u := by
    exact entryL2_nonneg R
  have huLocal : u ≤ min 1 (3 / (8 * max 1 K * M)) := by
    have h := transitionError_entryL2_le_of_neighborhood B₀ B hp hJ.le
      hunit hinv hlocal
    change u ≤ (p : ℝ) * J * pairwiseLocalRadius p M δ L J at h
    calc
      u ≤ (p : ℝ) * J * pairwiseLocalRadius p M δ L J := h
      _ = min 1 (3 / (8 * max 1 K * M)) := by
        dsimp [pairwiseLocalRadius, K]
        field_simp
  have hu1 : u ≤ 1 := huLocal.trans (min_le_left _ _)
  have huCoarse : u ≤ 3 / (8 * max 1 K * M) :=
    huLocal.trans (min_le_right _ _)
  have hc0 : 0 ≤ pairwiseSolveFactor M δ *
      (2 * M * u ^ 2 + 2 * ε) := by
    unfold pairwiseSolveFactor
    positivity
  have hoff : ∀ i j, i ≠ j →
      |R i j| ≤ pairwiseSolveFactor M δ * (2 * M * u ^ 2 + 2 * ε) := by
    simpa [R, u] using pairwise_offDiagonal_control A s B₀ B hM.le hδ hε
      hscale hsep hunit hexact happrox
  have huAgg := entryL2_transitionError_le B₀ B hp hL0 hc0 hunit hdiag₀ hdiag
    hB₀ hoff
  have huK : u ≤ K * (2 * M * u ^ 2 + 2 * ε) := by
    change u ≤ pairwiseSolveFactor M δ * (2 * M * u ^ 2 + 2 * ε) *
      Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2)) at huAgg
    calc
      u ≤ pairwiseSolveFactor M δ * (2 * M * u ^ 2 + 2 * ε) *
          Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2)) := huAgg
      _ = K * (2 * M * u ^ 2 + 2 * ε) := by
        dsimp [K, pairwiseAggregateFactor]
        ring
  have hcoefficient : 2 * K * M * u ≤ 3 / 4 := by
    calc
      2 * K * M * u ≤ 2 * (max 1 K) * M * u := by gcongr
      _ ≤ 2 * (max 1 K) * M * (3 / (8 * max 1 K * M)) := by gcongr
      _ = 3 / 4 := by field_simp; ring
  have huLinear : u ≤ 8 * K * ε := by
    have hquad : 2 * K * M * u ^ 2 ≤ (3 / 4) * u := by
      nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hcoefficient)]
    nlinarith
  have hsmall' : ε ≤ 1 / (32 * (max 1 K) ^ 2 * M) := by
    simpa [pairwiseResidualRadius, K] using hsmall
  have hbranch : 2 * K * M * u ≤ 1 / 2 := by
    calc
      2 * K * M * u ≤ 2 * K * M * (8 * K * ε) := by gcongr
      _ = 16 * K ^ 2 * M * ε := by ring
      _ ≤ 16 * (max 1 K) ^ 2 * M * ε := by
        gcongr
      _ ≤ 16 * (max 1 K) ^ 2 * M *
          (1 / (32 * (max 1 K) ^ 2 * M)) := by gcongr
      _ = 1 / 2 := by field_simp; ring
  exact ⟨by simpa [u, R] using hu1, by simpa [u, R, K] using hbranch⟩

end Causalean.Discovery.LinearDisentanglement.SimultaneousCongruence
