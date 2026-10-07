/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.HigherOrderInfluence.ProjectedKernelTrace
public import Causalean.Stat.Nonparametric.HigherOrderInfluence.ProjectionRisk

/-!
# Projection-kernel identities for higher-order influence function calculations

Two ingredients of the risk analysis of second-order U-statistic corrections built from a
`J`-dimensional projection. For a feature map `c` with invertible second-moment matrix
`Σ = E[c cᵀ]`, the projection kernel `g(x, y) = ⟨c(x), Σ⁻¹ c(y)⟩` has squared L²(P⊗P) norm exactly
`J` (the trace identity `tr(Σ Σ⁻¹ Σ Σ⁻¹) = J`), and integrates to zero in one argument when the
features are centred. A second result is pure algebra: it combines assumed bounds on the
first-order variance, the projection bias, the kernel energy and the remainder into one risk bound.

## Main results

* `projKernel_L2_eq_dim` (`HigherOrderInfluence/ProjectedKernelTrace`) — `∬ g² dP dP = J`, for
  `projKernel` with the inverse of the Gram matrix `gram`.
* `projKernel_degen` — `∫ g(x, ·) dP = 0` for centred features.
* `projectionKernel_risk_bound` (`HigherOrderInfluence/ProjectionRisk`) — the conditional risk
  algebra; the risk decomposition and all four component bounds are hypotheses.

No influence function or estimator is defined here, and no risk decomposition is derived.
-/
