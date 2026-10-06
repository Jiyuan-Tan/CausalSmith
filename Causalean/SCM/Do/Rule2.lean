/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 of do-calculus — kernel-level plumbing aggregator

The kernel-native Rule 2 *statement* itself is the witness-route a.e.
theorem `obsCondKernel_fixSet_eq_ae_witness` in `Rule2AE.lean` (surfaced as
`do_rule2_kernel_of_nondescendant_product_ae` in `DoCalculus.lean`).  The earlier pointwise/`fillZrW`
form `obsCondKernel_fixSet_eq` was retired: it pinned `obsCondKernel` on the
`μ_C`-null `{Z.random = ζ_s}` slice, which is ill-posed for continuous
treatment.

This module re-exports value-space and global-Markov plumbing used by the Rule 2
a.e. proof, plus the separate `ID.Overlap` predicate used by downstream
identification arguments.

## References

* Basic Concepts.tex, Proposition (do-Calculus), Rule 2.
-/

module
public import Causalean.SCM.Do.Rule2Kernel.RectIdentity
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.Do.Overlap

/-! # Rule 2 kernel-level plumbing aggregator

This module re-exports value-space and global-Markov helpers used by the
kernel-native Rule 2 a.e. statement (`Rule2AE.lean`). It also re-exports the
separate overlap predicate used by downstream backdoor / frontdoor
identification arguments. The Rule 2 statement itself lives in `Rule2AE.lean`. -/

public section

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

end SCM

end Causalean
