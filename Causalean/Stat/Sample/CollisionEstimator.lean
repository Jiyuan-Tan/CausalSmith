/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Collision and cross-sample estimators

This module defines an ordered-pair collision estimator for inverse-frequency
functionals, together with cell-weighted moments and cross-sample averages for
observations equipped with an explicit projection to their cell labels.
-/

namespace Causalean.Stat

open scoped BigOperators

/-- Given [a finite or infinite cell-label space](hyp:𝒳), [a real-valued cell-mass function](hyp:q),
and [two cell labels](hyp:x,y), the [collision kernel](goal) equals the reciprocal mass of the
first label when the labels coincide and equals zero otherwise. -/
noncomputable def collisionKernel {𝒳 : Type*} (q : 𝒳 → ℝ) (x y : 𝒳) : ℝ :=
  by
    classical
    exact if x = y then 1 / q x else 0

/-- Given [a cell-label space](hyp:𝒳), [a real-valued cell-mass function](hyp:q), [a nonnegative
integer target-sample size](hyp:N), and [a target sample of that size](hyp:target), the [collision
scale](goal) is the average collision-kernel value over all ordered pairs of distinct target
indices, with the displayed reciprocal convention also applying at sample sizes zero and one. -/
noncomputable def collisionScale {𝒳 : Type*} (q : 𝒳 → ℝ) {N : ℕ}
    (target : Fin N → 𝒳) : ℝ :=
  ((N : ℝ) * (N - 1 : ℕ))⁻¹ *
    ∑ j, ∑ l, if j ≠ l then collisionKernel q (target j) (target l) else 0

/-- Given [a cell-label space and an observation space](hyp:𝒳,Ω), [a real-valued cell-mass
function](hyp:q), [a map assigning each observation to a cell](hyp:proj), [a nonnegative integer
source-sample size](hyp:n), [a source sample](hyp:sample), [a real-valued observation
statistic](hyp:G), and [a cell label](hyp:x), the [cell moment](goal) is the inverse source-sample
size and inverse cell mass times the sum of the statistic over source observations projected to
that cell. -/
noncomputable def cellMoment {𝒳 Ω : Type*} (q : 𝒳 → ℝ) (proj : Ω → 𝒳)
    {n : ℕ} (sample : Fin n → Ω) (G : Ω → ℝ) (x : 𝒳) : ℝ :=
  by
    classical
    exact (n : ℝ)⁻¹ / q x *
      ∑ i, if proj (sample i) = x then G (sample i) else 0

/-- Given [a cell-label space and an observation space](hyp:𝒳,Ω), [a real-valued cell-mass
function](hyp:q), [an observation-to-cell map](hyp:proj), [nonnegative integer source and target
sample sizes](hyp:n,N), [a source sample](hyp:source), [a target sample of cell labels](hyp:target),
and [a real-valued observation statistic](hyp:G), the [cross-sample average](goal) is the average,
over target observations, of the corresponding source-sample cell moments. -/
noncomputable def crossAverage {𝒳 Ω : Type*} (q : 𝒳 → ℝ) (proj : Ω → 𝒳)
    {n N : ℕ} (source : Fin n → Ω) (target : Fin N → 𝒳)
    (G : Ω → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j, cellMoment q proj source G (target j)

end Causalean.Stat
