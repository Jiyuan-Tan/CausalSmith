/- 
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW second-order remainder bound

This file is the public entry point for the AIPW remainder package.  The
population remainder identity sits in `Remainder/Identity.lean`, and the
rate/big-O corollary sits in `Remainder/Bound.lean`.
-/

module
public import Causalean.Estimation.ATE.Remainder.Bound

/-!
# The second-order remainder of the AIPW moment for the average treatment effect

How far the population AIPW moment moves when the nuisance functions are wrong. For a candidate
pair (μ̂, ê) in the overlap class, evaluated at the true effect θ₀, the population moment equals
exactly

    ∫ (ê(x) − e(x)) · [ (μ̂(1,x) − μ(1,x))/ê(x) + (μ̂(0,x) − μ(0,x))/(1 − ê(x)) ] dP_X(x),

a product of propensity and outcome-regression errors with no first-order term. By
Cauchy–Schwarz its absolute value is at most an overlap-dependent constant times the sum over
arms of ‖μ̂(a,·) − μ(a,·)‖₂·‖ê − e‖₂ in L²(P_X), so a sequence of nuisance estimators whose error
product is o_p(n^{-1/2}) in each arm has remainder o_p(n^{-1/2}). All three statements assume
strict overlap of the true propensity, the back-door identification assumptions, and finite
second moments of the observed and potential outcomes.

## Main results

* `aipw_remainder_identity` — the exact product-of-errors identity (`Remainder/Identity`).
* `aipw_remainder_bound` — the L² product bound (`Remainder/Bound`).
* `aipw_remainder_op` — the o_p(n^{-1/2}) remainder under the product-rate condition.
* `plugin_bias_le_eLpNorm` — the integrated error of an outcome regression is at most its
  L²(P_X) norm.
-/

public section

namespace Causalean
namespace Estimation
namespace ATE

namespace BackdoorEstimationSystem

-- Re-export module layout for convenience.

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
