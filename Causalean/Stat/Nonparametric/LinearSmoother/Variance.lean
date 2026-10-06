/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.GaussMarkov.Variance

/-!
# Variance of a fixed-weight linear smoother under heteroskedastic errors

Variance bounds for fixed-weight linear smoothers under uncorrelated heteroskedastic errors.

A linear smoother `∑ᵢ Sᵢ Yᵢ` with deterministic weights `Sᵢ` (the local-polynomial /
series equivalent-kernel weights, conditional on the design) applied to an uncorrelated
random family `Y` whose cell variances are bounded by `σ̄²` has variance

`Var[∑ᵢ Sᵢ Yᵢ] ≤ σ̄² · ∑ᵢ Sᵢ²`.

This is the generic (design-agnostic) variance half of the interior nonparametric estimator
analysis: it reduces the target stochastic-error bound `O((Nh)^{−1/2})` to a leverage bound
`∑ᵢ Sᵢ² = O(1/(Nh))`. It is a direct corollary of the Gauss–Markov covariance–quadratic-form
identity (`Causalean.Stat.GaussMarkov`). Both the local-polynomial and the series/sieve estimators
consume it; the local-polynomial-specific corollary lives in
`Causalean.Stat.Nonparametric.LocalPoly.SmootherVariance`.
-/

@[expose] public section

namespace Causalean.Stat.Nonparametric

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

/-- For [a finite family of real random variables](hyp:Y), [a probability measure](hyp:μ), and
[a variance scale](hyp:σbar), the [uncorrelated bounded-variance condition](goal) requires (1)
[every coordinate variance to be at most `σbar²`](step:1) and (2) [every two distinct
coordinates to have covariance zero](step:2). -/
def UncorrelatedVarianceFamily {Ω : Type*} {N : ℕ} [MeasurableSpace Ω]
    (Y : Fin N → Ω → ℝ) (μ : Measure Ω) (σbar : ℝ) : Prop :=
  (∀ i, Var[Y i; μ] ≤ σbar ^ 2) ∧
    (∀ i j, i ≠ j → cov[Y i, Y j; μ] = 0)

/-- **Stochastic-error bound for a fixed-weight linear smoother.** If [each response `Yᵢ`
is square-integrable](hyp:hY), [distinct responses are uncorrelated and every response variance
is bounded by `σbar²`](hyp:hnoise), and [the
sum of squared smoother weights, `∑ᵢ Sᵢ²`, is bounded by `V`](hyp:hlev), then [the
variance of the linear smoother `∑ᵢ Sᵢ Yᵢ` is at most `σbar² V`](goal).

Taking `V = O(1/(Nh))` gives the interior `O((Nh)^{−1/2})` stochastic-error rate. -/
theorem linearSmoother_variance_le {Ω : Type*} {N : ℕ} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Fin N → Ω → ℝ} {S : Fin N → ℝ}
    {σbar V : ℝ}
    (hY : ∀ i, MemLp (Y i) 2 μ)
    (hnoise : UncorrelatedVarianceFamily Y μ σbar)
    (hlev : (∑ i, S i ^ 2) ≤ V) :
    Var[fun ω => ∑ i, S i * Y i ω; μ] ≤ σbar ^ 2 * V := by
  rw [Causalean.Stat.GaussMarkov.variance_linearCombination Y hY S]
  have hquad : Causalean.Stat.GaussMarkov.quadVar (Causalean.Stat.GaussMarkov.covMatrix Y μ) S
      ≤ σbar ^ 2 * ∑ i, S i ^ 2 := by
    simp only [Causalean.Stat.GaussMarkov.quadVar, dotProduct, mulVec]
    calc
      ∑ i, S i * ∑ j, Causalean.Stat.GaussMarkov.covMatrix Y μ i j * S j
          = ∑ i, S i * (Var[Y i; μ] * S i) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              congr 1
              rw [Finset.sum_eq_single i]
              · rw [Causalean.Stat.GaussMarkov.covMatrix,
                    covariance_self (hY i).aemeasurable]
              · intro j _ hji
                rw [Causalean.Stat.GaussMarkov.covMatrix,
                  hnoise.2 i j (Ne.symm hji), zero_mul]
              · simp
      _ ≤ ∑ i, σbar ^ 2 * S i ^ 2 := by
              refine Finset.sum_le_sum (fun i _ => ?_)
              nlinarith [hnoise.1 i, sq_nonneg (S i)]
      _ = σbar ^ 2 * ∑ i, S i ^ 2 := by rw [Finset.mul_sum]
  exact hquad.trans (mul_le_mul_of_nonneg_left hlev (sq_nonneg σbar))

end Causalean.Stat.Nonparametric
