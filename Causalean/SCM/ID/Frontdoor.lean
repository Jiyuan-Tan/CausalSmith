/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.Frontdoor.Completeness

/-! # Frontdoor adjustment

Pearl's frontdoor adjustment for a structural causal model with treatment X, mediator W and
outcome Y, stated for general (standard Borel) value spaces at the level of Markov kernels.
Under the frontdoor criterion — W intercepts every directed path from X to Y, there is no
unblocked back-door path from X to W, and X blocks every back-door path from W to Y — the law of
Y under do(X = x) equals the frontdoor functional

    ∫ P(dw | x) ∫ P(dy | x', w) P(dx'),

for almost every treatment value x under the observational treatment marginal. The result is
conditional on three absolute-continuity premises, of which only the treatment–mediator overlap
condition is substantive.

## Main definitions

* `frontdoorCriterion` — the graphical criterion, as d-separation and back-door conditions.
* `frontdoorKernelY` — the frontdoor functional as a kernel from treatment values to outcomes.

## Main results

* `frontdoor_legA_mediator`, `frontdoor_legB_outcome` — the mediator law under do(X) and the
  outcome law under do(W) are given by back-door adjustment (empty set, respectively X).
* `frontdoor_fd1_interception_compProd` — the interception step linking do(X, W) to do(X).
* `frontdoor_completeness_ae_compProd`, `frontdoor_adjustment_ae` — the frontdoor identity, as
  an equality of joint laws with the treatment marginal and as an almost-everywhere equality.
-/
