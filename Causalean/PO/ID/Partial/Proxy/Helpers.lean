/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.PO.ID.Partial.Proxy.Helpers.BridgeW
public import Causalean.PO.ID.Partial.Proxy.Helpers.BridgeWZ
public import Causalean.PO.ID.Partial.Proxy.Helpers.CondExpQ

/-! # Bridge-substitution identities for proximal partial identification

The identities that move an unobservable off-arm counterfactual integral onto observable
quantities in the proximal bounds. With treatment A, covariates X, latent confounder U,
outcome proxy W, treatment proxy Z, outcome bridge h and treatment bridge q:

* `condIntYofA_eq_h_arm` (W-only assumptions): ∫ over {A ≠ a} of Y(a) equals ∫ over {A ≠ a} of
  h(a, W, X), by latent exchangeability, consistency, the bridge equation and W ⊥ A | (U, X).
* `condIntYofA_eq_hq_armSwap_twoProxy` (two-proxy assumptions): ∫ over {A ≠ a} of Y(a) equals
  ∫ over {A = a} of h(a, W, X) · q(Z, a, X).
* `condExp_q_eq_stratumOddsRatio_arm_AX` (two-proxy assumptions): on {A = a}, the conditional
  expectation of q(Z, a, X) given (A, X) equals the stratum odds ratio P(A ≠ a | X) / P(A = a | X)
  almost surely, which removes the latent treatment bridge from the final bound.

## Contents

* `Helpers.Common` — stratum decomposition of the marginal mean, pull-out of measurable factors
  from set integrals, and transfer of almost-sure bounds from the observed outcome to a
  potential outcome (`ae_le_YofA_of_ae_le_Y`, `ae_le_YofA_of_ae_le_Y_below`).
* `Helpers.BridgeW` — the W-only identity.
* `Helpers.BridgeWZ` — the two-proxy identity.
* `Helpers.CondExpQ` — the treatment-bridge collapse to the stratum odds ratio.
-/
