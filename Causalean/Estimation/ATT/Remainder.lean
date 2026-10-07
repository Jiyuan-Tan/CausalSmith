/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW second-order remainder bound (ATT) — umbrella module

This file is the public entry point for the ATT AIPW remainder package.  The
population remainder identity sits in `Remainder/Identity.lean`, and the
quantitative L²-product bound plus its `o_p(n^{-1/2})` corollary sit in
`Remainder/Bound.lean`.  Mirrors `Estimation/ATE/Remainder.lean`.
-/

module
public import Causalean.Estimation.ATT.Remainder.Bound

/-!
# The second-order remainder of the AIPW moment for the treated

How far the population ATT moment moves when the nuisance functions are wrong. For a candidate
control regression μ̂₀ and propensity ê in the overlap class, the population AIPW moment at the
true ATT equals exactly the single cross-product

    ∫ (ê(x) − e(x))/(1 − ê(x)) · (μ̂₀(x) − μ₀(x)) dP_X(x),

so its absolute value is at most (1/ε)·‖μ̂₀ − μ₀‖₂·‖ê − e‖₂ in L²(P_X), and a sequence of
nuisance estimators whose error product is o_p(n^{-1/2}) has remainder o_p(n^{-1/2}). The
statements assume one-sided overlap e ≤ 1 − ε of the true propensity, the one-sided back-door
ATT assumptions, a positive treatment probability, finite second moments of the outcome and of
the untreated potential outcome, and integrability of the candidate's odds-weighted correction.

## Main results

* `aipw_remainder_identity_ATT` — the exact cross-product identity (`Remainder/Identity`).
* `aipw_remainder_bound_ATT` — the L² product bound (`Remainder/Bound`).
* `aipw_remainder_op_ATT` — the o_p(n^{-1/2}) remainder under the product-rate condition.
-/

public section

namespace Causalean
namespace Estimation
namespace ATT

namespace TreatedEstimationSystem

-- Re-export module layout for convenience.

end TreatedEstimationSystem

end ATT
end Estimation
end Causalean
