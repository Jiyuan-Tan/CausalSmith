/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.PO.ID.Partial.Proxy.IntervalForm
/-! # Proximal partial-identification bounds

Bounds on counterfactual means in the proximal causal inference setting when completeness fails
and the bridge functions are not identified, following Ghassami, Shpitser and Tchetgen Tchetgen
(arXiv:2304.04374). With binary treatment A, covariates X, latent confounder U, an
outcome-side proxy W and a treatment-side proxy Z, the target is the off-arm mean
E[Y(a) | A ≠ a] and, from it, the marginal mean E[Y(a)]. Each theorem takes lower and upper
envelope functions satisfying stated integral comparisons as hypotheses, and concludes that the
target lies between the corresponding observable integrals; no envelope is constructed and no
sharpness is claimed.

## Main results

* `condMeanYofA_W_bounds`, `meanYofA_W_bounds` — outcome-proxy (W only) bounds: under
  consistency, latent exchangeability, W ⊥ A | (U, X) and an outcome bridge h, the target lies
  between integrals over {A = a} of stratum odds ratio × envelope × E[Y | A, X], clamped by the
  outcome's essential bounds.
* `condMeanYofA_Z_bounds`, `meanYofA_Z_bounds` — treatment-proxy (Z only) bounds via a treatment
  bridge q: the target lies between the off-arm integrals of the envelopes.
* `condMeanYofA_WZ_bounds` — two conditionally independent invalid proxies: a bound of the same
  observable form as the W-only one, with both latent bridges eliminated.
* `condMeanYofA_W_mem_Icc`, `meanYofA_W_mem_Icc`, `condMeanYofA_Z_mem_Icc`,
  `meanYofA_Z_mem_Icc`, `condMeanYofA_WZ_mem_Icc` — the five bounds as closed-interval
  membership.

Integrability of the envelope-weighted quantities and positive mass of {A ≠ a} are hypotheses.
-/
