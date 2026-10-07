/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.Poisson.Poincare.L2Closure
public import Causalean.Mathlib.Probability.Poisson.Poincare.Series

/-!
# Building blocks for the Poisson Poincaré inequality

Three ingredients of the proof that a function f of a Poisson(λ) variable N satisfies
Var f(N) ≤ λ·E[(f(N + 1) − f(N))²]. First, for any probability law the variance of a
square-integrable function equals half the expected squared difference between two independent
draws. Second, the Poisson weights satisfy the size-bias shift (n + 1)·p(n + 1) = λ·p(n), and a
difference over a range of integers is controlled by the sum of squared one-step increments via
Cauchy–Schwarz. Third, truncating a sequence to finite support approximates it in L² together
with its add-one increment, so the inequality extends from finitely supported sequences.

## Contents

* `Poincare.Series` — `poissonWeight`, `poissonWeight_shift`, the upper-triangle reindexings and
  `sq_sub_le_nat_sub_mul_sum_sq_step`.
* `Poincare.L2Closure` — the increment `addOne`, `variance_eq_half_integral_prod_sq_sub`, the
  truncation `supportTruncation` and its L² convergence.

This file only gathers the modules above.
-/

public section
