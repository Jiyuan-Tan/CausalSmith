/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.Do.Rule2Kernel.WitnessBridge.Cutset
public import Causalean.SCM.Do.Rule2Kernel.WitnessBridge.ObsSide
public import Causalean.SCM.Do.Rule2Kernel.WitnessBridge.DoSide

/-! # Cross-model conditional-kernel identity for Rule 2 with general treatments

The analytic core of Rule 2 of the do-calculus for treatments with arbitrary (possibly
continuous) values. In a structural causal model with outcome nodes Y, treatment names Z and
conditioning nodes W, both the observational conditional law of Y given (Z, W) and the
post-intervention conditional law of Y given W are shown to equal one common kernel: the
posterior law of the latent cut-set of Y given W, pushed through the structural map that sends a
cut-set value and a value (z, w) to Y. Equating the two gives the bridge
`obsCondKernel_fixSet_M1_eq_ae_product`: for almost every (z, w) under the product of a treatment
marginal and the W-marginal, the conditional of Y given W under do(Z = z) equals the
observational conditional of Y given (Z = z, W = w). It assumes that W contains no descendant of
the treatment, that Y is d-separated from the random treatment copies given W and the fixed
nodes in the intervened graph, a positivity (absolute-continuity) condition, and standard Borel
value spaces.

## Contents

* `WitnessBridge.Cutset` — the outcome factors through the cut-set and the conditioning values
  (`cutset_factor_pointwise`); the cut-set is conditionally independent of the treatment given
  W (`cutset_condIndep_condDistrib`).
* `WitnessBridge.ObsSide` — the observational conditional equals the witness kernel
  (`obsSide_eq_witness`, `obsCondKernel_union_eq_witness`).
* `WitnessBridge.DoSide` — the post-intervention conditional equals the same kernel
  (`doSide_eq_witness`), and the assembled bridge.
-/
