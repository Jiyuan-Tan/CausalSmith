module
public import Causalean.Stat.Limit.Convergence

/-!
# Generic `o_p` transfer helper

This module provides `isLittleOp_of_eventuallyEq`, which transfers a
little-o-in-probability rate across eventual pointwise equality of stochastic
sequences. The fixed-order U-statistic decomposition and central limit
theorems are defined in `OrderM.Hajek`, `OrderM.CLT`, and `OrderM.OrderTwo`.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Transfer of `o_p` along eventual equality.** For sequences of random variables
`f, g : ℕ → Ω → ℝ` and a rate `r : ℕ → ℝ`, if [`g` is `o_p(r)` under `μ`](hyp:hg) and
[`f n = g n` for all sufficiently large `n`](hyp:hfg), then [`f` is also `o_p(r)` under
`μ`](goal). -/
theorem isLittleOp_of_eventuallyEq {f g : ℕ → Ω → ℝ} {r : ℕ → ℝ}
    (hg : IsLittleOp g r μ) (hfg : ∀ᶠ n in atTop, f n = g n) :
    IsLittleOp f r μ := by
  intro ε hε
  refine (hg ε hε).congr' ?_
  filter_upwards [hfg] with n hn
  rw [hn]

end Causalean.Stat
