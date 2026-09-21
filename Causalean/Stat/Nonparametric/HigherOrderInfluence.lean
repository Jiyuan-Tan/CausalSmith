/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Nonparametric.HigherOrderInfluence.ProjectedKernelTrace
public import Causalean.Stat.Nonparametric.HigherOrderInfluence.ProjectionRisk

/-!
# Higher-order influence function (HOIF) building blocks

Building blocks for projection-kernel risk algebra: projected-kernel trace identities and
algebraic assembly of assumed component bounds.

This barrel collects independently useful projection-kernel and risk-algebra results.
It does not define an influence function or an estimator:

* `HigherOrderInfluence/ProjectedKernelTrace.lean` — the projected degenerate kernel
  `g(x,y) = ⟨c(x), Σ⁻¹ c(y)⟩` has L²-energy `ζ = ∬ g² dP dP = J`
  (`projKernel_L2_eq_dim`), the trace identity `tr(Σ Σ⁻¹ Σ Σ⁻¹) = J`; the file also proves
  its degeneracy (`projKernel_degen`).
* `HigherOrderInfluence/ProjectionRisk.lean` — risk algebra assembling supplied component bounds
  into a single projection-kernel risk bound (`projectionKernel_risk_bound`).
-/
