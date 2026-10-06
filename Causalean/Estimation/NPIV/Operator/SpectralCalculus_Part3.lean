/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Operator.Adjoint
public import Causalean.Estimation.NPIV.Operator.Complexification
public import Causalean.Estimation.NPIV.Operator.SpectralCalculus_Part1
public import Causalean.Estimation.NPIV.Operator.SpectralCalculus_Part2
public import Causalean.Estimation.NPIV.Operator.Tikhonov
public import Causalean.Estimation.NPIV.SourceCondition
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Packaging spectral bias for the primal rate theorem

This final spectral part converts a `SpectralSourceCondition` and a
`TikhonovPullback` into the uniform `TikhonovBiasBound` consumed by the primal
rate theorem.  The pullback represents the ambient minimizer by a candidate
function; it does not turn the ambient construction into candidate-subspace
minimization.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
/-- For [an NPIV operator system](hyp:S), [a real source exponent](hyp:β), [a spectral
source condition](hyp:sc), and [a simultaneous pullback of the population minimisers to
candidate functions](hyp:pb), [the construction returns one Tikhonov bias certificate whose
constant is uniform over every positive regularization level](goal).

**Discharge of the Tikhonov bias bound from the spectral source
condition.**

Given a `SpectralSourceCondition` and a `TikhonovPullback` to the
function-level minimiser, packages the spectral `strong_bias` and
`weak_bias` theorems plus `tikhonovMinimiserL2_strong_convexity` into
a full `TikhonovBiasBound`.

The packaged constant is `C := sc.biasConst · ‖w₀‖_{L²}`, so the
`TikhonovBiasBound` statement `LHS² ≤ C · ‖w₀‖ · λ^…` follows from the
spectral statement `LHS² ≤ biasConst · ‖w₀‖² · λ^…`. -/
noncomputable def tikhonov_bias_from_spectral
    (S : OperatorSystem Ω μ) (β : ℝ)
    (sc : SpectralSourceCondition S β)
    (pb : TikhonovPullback S β sc) :
    TikhonovBiasBound S β sc.toSourceCondition := by
  refine
    { h_lambda_star_fun := pb.h_lambda_star_fun
      h_lambda_star_mem := pb.h_lambda_star_mem
      C := sc.biasConst * ‖S.hL2 sc.w₀_mem‖
      C_nonneg := mul_nonneg sc.biasConst_nonneg (norm_nonneg _)
      strong_bias := ?_
      weak_bias := ?_
      strong_convexity := ?_ }
  · intro lambda lambda_pos
    have hb := sc.strong_bias lambda_pos
    have hpull := pb.h_lambda_star_pullback lambda_pos
    have hC :
        sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 *
              lambda ^ (min β 2)
          = sc.biasConst * ‖S.hL2 sc.w₀_mem‖ * S.strongNorm (S.hL2 sc.w₀_mem)
              * lambda ^ (min β 2) := by
      rw [S.primalTrimEquiv.norm_map, OperatorSystem.strongNorm, sq]
      ring
    rw [OperatorSystem.strongNorm, hpull]
    calc
      ‖S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem‖ ^ 2 =
          ‖S.primalTrimEquiv
            (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem)‖ ^ 2 := by
              rw [S.primalTrimEquiv.norm_map]
      _ = ‖S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) -
              S.primalTrimEquiv (S.hL2 S.h₀_mem)‖ ^ 2 := by
            rw [map_sub]
      _ ≤ sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 *
              lambda ^ (min β 2) := hb
      _ = sc.biasConst * ‖S.hL2 sc.w₀_mem‖ *
              S.strongNorm (S.hL2 sc.w₀_mem) * lambda ^ (min β 2) := hC
  · intro lambda lambda_pos
    have hb := sc.weak_bias lambda_pos
    have hpull := pb.h_lambda_star_pullback lambda_pos
    have hC :
        sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 *
              lambda ^ (min (β + 1) 2)
          = sc.biasConst * ‖S.hL2 sc.w₀_mem‖ * S.strongNorm (S.hL2 sc.w₀_mem)
              * lambda ^ (min (β + 1) 2) := by
      rw [S.primalTrimEquiv.norm_map, OperatorSystem.strongNorm, sq]
      ring
    rw [OperatorSystem.weakNorm, OperatorSystem.strongNorm, hpull]
    change ‖S.Tlin (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem)‖ ^ 2 ≤ _
    calc
      ‖S.Tlin (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem)‖ ^ 2 =
          ‖S.TlinTrim (S.primalTrimEquiv
            (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem))‖ ^ 2 := by
              simp [OperatorSystem.TlinTrim]
      _ = ‖S.TlinTrim (S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) -
              S.primalTrimEquiv (S.hL2 S.h₀_mem))‖ ^ 2 := by
            rw [map_sub]
      _ ≤ sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 *
              lambda ^ (min (β + 1) 2) := hb
      _ = sc.biasConst * ‖S.hL2 sc.w₀_mem‖ *
              ‖S.hL2 sc.w₀_mem‖ * lambda ^ (min (β + 1) 2) := hC
  · intro lambda lambda_pos h hh
    have hconv :=
      S.tikhonovMinimiserL2_strong_convexity (lambda_pos := lambda_pos)
        (h := S.hL2 hh)
    change lambda * ‖S.hL2 hh - S.hL2 (pb.h_lambda_star_mem lambda_pos)‖ ^ 2 +
        ‖S.Tlin (S.hL2 hh - S.hL2 (pb.h_lambda_star_mem lambda_pos))‖ ^ 2 ≤
      ‖S.Tlin (S.hL2 hh - S.hL2 S.h₀_mem)‖ ^ 2 -
        ‖S.Tlin (S.hL2 (pb.h_lambda_star_mem lambda_pos) - S.hL2 S.h₀_mem)‖ ^ 2 +
          lambda * (‖S.hL2 hh‖ ^ 2 -
            ‖S.hL2 (pb.h_lambda_star_mem lambda_pos)‖ ^ 2)
    rw [pb.h_lambda_star_pullback lambda_pos]
    exact hconv

end NPIV
end Estimation
end Causalean
