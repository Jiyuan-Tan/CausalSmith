/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LinearDisentanglement.Quantitative.CompactExclusion
public import Causalean.Discovery.LinearDisentanglement.Quantitative.Definitions
public import Causalean.Discovery.LinearDisentanglement.Quantitative.Quantitative

/-!
# Quantitative stability of simultaneous congruence

Perturbation bound for simultaneous diagonalization by congruence. Given real square matrices Aₑ
indexed by finitely many environments e and prescribed diagonal vectors sₑ, a matrix B has
residual maxₑ ‖B·Aₑ·Bᵀ − diag(sₑ)‖ in the Euclidean operator norm. Suppose an invertible
unit-diagonal B₀ has residual zero, the sₑ are bounded, and d of the differences sₑ − s_base form a
matrix with determinant at least δ > 0 in absolute value. Then every unit-diagonal B within the
stated norm bound and with residual ε below an explicit threshold satisfies ‖B − B₀‖ ≤ C·ε for an
explicit constant C depending only on the dimension, the shift bound, δ and the norm bound. A
compactness argument gives the complementary non-local fact: on a compact candidate set where
only B₀ has zero residual, the residual has a positive minimum outside any open neighbourhood of
B₀.

## Contents

* `Definitions` — `simultaneousCongruenceResidual`, `ExactCongruence`, `ApproximateCongruence`,
  the separation condition `AffineMinorSeparated`, and the constants `stabilityConstant` and
  `admissibleRadius`.
* `Quantitative` — `opNorm_sub_le_of_approximate_simultaneous_congruence`, the bound
  ‖B − B₀‖ ≤ C·ε.
* `CompactExclusion` — `continuous_simultaneousCongruenceResidual` and
  `exists_simultaneousCongruence_exclusionRadius`, the positive residual gap away from B₀.
-/
