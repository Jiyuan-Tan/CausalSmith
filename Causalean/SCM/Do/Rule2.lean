/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.SCM.Do.Rule2Kernel.RectIdentity
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.Do.Overlap

/-! # Ingredients for Rule 2 of the do-calculus

Rule 2 of the do-calculus (action/observation exchange) says that, when the outcome Y is
d-separated from the treatment Z given W in the graph where Z has been intervened on, the
conditional law of Y given W under do(Z = z) equals the observational conditional law of Y given
(Z = z, W). This module collects the three ingredients of the kernel-level, almost-everywhere
proof of that rule; the rule itself is `do_rule2_kernel_of_nondescendant_product_ae` in `SCM.Do.Rule2AE`.

## Contents

* `SCM.Do.Rule2Kernel.RectIdentity` — two almost-everywhere identities of conditional kernels:
  `obsCondKernel_dSep_collapse_ae` (under the d-separation above, the post-intervention
  conditional of Y given the random treatment copies and W depends only on W) and
  `obsCondKernel_cross_SCM_ae_eq_on_fillZrW` (the pre- and post-intervention conditionals agree
  at conditioning points whose treatment coordinates match the intervened value).
* `SCM.Do.ObsMarkov` — the global Markov property for the observed variables: d-separation in
  the full graph, latent nodes included, implies conditional independence under the
  observational law (`globalMarkov`, `globalMarkov_with_fixed`, `obs_condIndep_of_full`).
* `SCM.Do.Overlap` — `Rule2JointOverlap`: the post-intervention marginal of the treatment and
  W is absolutely continuous with respect to the observational one; an explicit assumption of
  the backdoor and frontdoor identification results.

This file itself declares nothing.
-/

public section

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

end SCM

end Causalean
