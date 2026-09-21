/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.GaussianWeightedSum

/-! # Gaussian multiplier bootstrap: exact law for fixed data

The Gaussian multiplier (wild) bootstrap does not resample.  It keeps the observed data
`x₁, …, xₙ` fixed, multiplies the recentred values `xᵢ − x̄` by independent standard
Gaussian weights `ξᵢ`, and uses the law of `n^{-1/2} Σᵢ (xᵢ − x̄) ξᵢ` over the weights as
the bootstrap distribution.

`multiplierBootstrap_law` computes that distribution exactly: for every fixed data vector
it is the centred Gaussian with variance equal to the sample variance
`n⁻¹ Σᵢ (xᵢ − x̄)²`.  This file does not prove bootstrap consistency, i.e. that this law
approximates the sampling law of `√n (x̄ − E X)`; the data here are a deterministic
vector, not a random sample. -/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Exact law of the √n-scaled multiplier-bootstrap mean.** Fix a sample size `n`, data
`x : Fin n → ℝ`, and a multiplier family `ξ`. If [`ξ` is independent across
coordinates](hyp:hindep), [each `ξ i` is measurable](hyp:hmeas), and [each `ξ i` has the
standard Gaussian law](hyp:hlaw), then [the scaled multiplier-bootstrap statistic
$n^{-1/2}\sum_i (x_i-\bar x)\,\xi_i$ has exactly the centered Gaussian law with variance equal
to the sample variance $n^{-1}\sum_i(x_i-\bar x)^2$](goal).

    Immediate from `Causalean.Mathlib.map_weighted_sum_gaussian` with weights
`aᵢ = n^{-1/2} (xᵢ − x̄)`, using `∑ aᵢ² = n⁻¹ ∑ (xᵢ − x̄)² = sₙ²`. -/
theorem multiplierBootstrap_law {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (hindep : iIndepFun ξ μ) (hmeas : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = gaussianReal 0 1) (x : Fin n → ℝ) :
    μ.map (fun ω =>
        (Real.sqrt n)⁻¹ * ∑ i, (x i - (n : ℝ)⁻¹ * ∑ j, x j) * ξ i ω)
      = gaussianReal 0
          ⟨(n : ℝ)⁻¹ * ∑ i, (x i - (n : ℝ)⁻¹ * ∑ j, x j) ^ 2,
            by positivity⟩ := by
  set xbar : ℝ := (n : ℝ)⁻¹ * ∑ j, x j with hxbar
  set a : Fin n → ℝ := fun i => (Real.sqrt n)⁻¹ * (x i - xbar) with ha
  -- Rewrite the statistic as `∑ i, a i * ξ i`.
  have hstat : (fun ω => (Real.sqrt n)⁻¹ * ∑ i, (x i - xbar) * ξ i ω)
      = (fun ω => ∑ i, a i * ξ i ω) := by
    funext ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ha]; ring
  rw [hstat, Causalean.Mathlib.map_weighted_sum_gaussian ξ hindep hmeas hlaw a]
  -- Match the variance: `∑ aᵢ² = n⁻¹ ∑ (xᵢ − x̄)²`.
  congr 1
  ext
  show (∑ i, ((Real.sqrt n)⁻¹ * (x i - xbar)) ^ 2)
      = (n : ℝ)⁻¹ * ∑ i, (x i - xbar) ^ 2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (le_of_lt hnpos)]
    have hpt : ∀ i, ((Real.sqrt n)⁻¹ * (x i - xbar)) ^ 2
        = (n : ℝ)⁻¹ * (x i - xbar) ^ 2 := by
      intro i; rw [mul_pow, hsq]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), ← Finset.mul_sum]

end Causalean.Stat
