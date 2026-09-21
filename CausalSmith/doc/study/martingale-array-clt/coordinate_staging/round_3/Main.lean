/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.CharacteristicFunction
import Causalean.Stat.CLT.MartingaleArray.Lyapunov

/-! # Scalar martingale triangular-array central limit theorem

This module proves the reusable scalar CLT for finite-row, square-integrable
martingale-difference arrays.  It also supplies Lyapunov corollaries based on
conditional or unconditional fourth-moment sums and a deterministic
predictable-variance specialization.  No independence hypothesis is used.
-/

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Topology

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

/-- For [a square-integrable real martingale-difference triangular array](hyp:A), if [the
sum of conditional variances in each row converges in probability to one](hyp:hVariance)
and [the conditional Lindeberg sum converges in probability to zero at every positive
threshold](hyp:hLindeberg), then [the row sums converge in distribution to the standard
normal law](goal).  Row lengths may vary with the row index, and no independence between
increments is assumed. -/
theorem martingaleArrayCLT
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ)
    (hVariance : TendstoInProbability μ A.predictableQuadraticVariation 1)
    (hLindeberg : ∀ ε : ℝ, 0 < ε →
      TendstoInProbability μ (A.conditionalLindeberg ε) 0) :
    TendstoInDistribution μ A.rowSum (gaussianReal 0 1) A.rowSum_aemeasurable := by
  unfold TendstoInDistribution
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr fun t => ?_
  simpa [ProbabilityMeasure.coe_mk] using
    martingaleArrayCharFun_tendsto A hVariance hLindeberg t

/-- For [a square-integrable martingale-difference array](hyp:A) whose [predictable
quadratic variations converge in probability to one](hyp:hVariance), if [all increments
have finite fourth moments](hyp:hFourth) and [the conditional fourth-moment row sums vanish
in probability](hyp:hFourthConditional), then [the row sums converge in distribution to
the standard normal law](goal). -/
theorem martingaleArrayCLT_of_conditionalFourthMoment
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ)
    (hVariance : TendstoInProbability μ A.predictableQuadraticVariation 1)
    (hFourth : ∀ n k, k < A.rowLength n → MemLp (A.increment n k) 4 (μ n))
    (hFourthConditional :
      TendstoInProbability μ A.conditionalFourthMoment 0) :
    TendstoInDistribution μ A.rowSum (gaussianReal 0 1) A.rowSum_aemeasurable := by
  apply martingaleArrayCLT A hVariance
  exact conditionalLindeberg_of_conditionalFourthMoment A hFourth hFourthConditional

/-- For [a square-integrable martingale-difference array](hyp:A) whose [predictable
quadratic variations converge in probability to one](hyp:hVariance), if [all increments
have finite fourth moments](hyp:hFourth) and [the deterministic sum of their unconditional
fourth moments vanishes](hyp:hFourthSum), then [the row sums converge in distribution to
the standard normal law](goal). -/
theorem martingaleArrayCLT_of_fourthMomentSum
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ)
    (hVariance : TendstoInProbability μ A.predictableQuadraticVariation 1)
    (hFourth : ∀ n k, k < A.rowLength n → MemLp (A.increment n k) 4 (μ n))
    (hFourthSum : Tendsto A.fourthMomentSum atTop (𝓝 0)) :
    TendstoInDistribution μ A.rowSum (gaussianReal 0 1) A.rowSum_aemeasurable := by
  apply martingaleArrayCLT A hVariance
  exact conditionalLindeberg_of_fourthMomentSum A hFourth hFourthSum

/-- For [a square-integrable martingale-difference array](hyp:A), suppose [its predictable
quadratic variation equals a deterministic row variance](hyp:hVarianceEq), [those variances
converge to one](hyp:hVariance), [all increments have finite fourth moments](hyp:hFourth),
and [the deterministic fourth-moment row sums vanish](hyp:hFourthSum).  Then [the row sums
converge in distribution to the standard normal law](goal). -/
theorem martingaleArrayCLT_of_deterministicVariance_fourthMomentSum
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (v : ℕ → ℝ)
    (hVarianceEq : ∀ n, A.predictableQuadraticVariation n =ᵐ[μ n] fun _ => v n)
    (hVariance : Tendsto v atTop (𝓝 1))
    (hFourth : ∀ n k, k < A.rowLength n → MemLp (A.increment n k) 4 (μ n))
    (hFourthSum : Tendsto A.fourthMomentSum atTop (𝓝 0)) :
    TendstoInDistribution μ A.rowSum (gaussianReal 0 1) A.rowSum_aemeasurable := by
  apply martingaleArrayCLT_of_fourthMomentSum A
    (predictableQuadraticVariation_tendstoInProbability_of_ae_eq
      A v hVarianceEq hVariance)
    hFourth hFourthSum

end Causalean.Stat
