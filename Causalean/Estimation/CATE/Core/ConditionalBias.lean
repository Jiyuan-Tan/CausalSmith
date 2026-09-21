/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional bias of the DR pseudo-outcome — `prop:est-cate-dr-bias-identity`

The σ(X)-conditional bias identity used in the proof of Kennedy (2023),
Theorem 2:

    μ[ φ_η(Z) − φ_0(Z) | σ(X) ]
      =ᵐ  ∑_{a ∈ {true, false}}
            ((η.e_fn − η₀.e_fn) (η.μ_fn a − η₀.μ_fn a) /
              (a · η.e_fn + (1 − a) · (1 − η.e_fn)))(X)

equivalently in value space (`P_X`-a.e.) — the closed-form cross-product
remainder driving the double-robustness corollary
`rem:est-cate-double-robust`.

This file provides:
* `condBias η η₀ x`                — the closed-form value-space bias.
* `measurable_condBias`            — measurability of `condBias`.
* `cond_exp_residual_at_h`         — generalized residual-conditional-expectation
                                     helper (parameterised over an arbitrary
                                     measurable `h : γ → ℝ`).
* `phi_eta_minus_phi₀_cond_exp`    — the σ(X)-conditional bias identity (Ω-form).
* `phi_eta_minus_phi₀_at_x`        — lightweight value-space bridge used by
                                     downstream packaging.
* `condBias_zero_of_propensity_match` — DR corollary (correct propensity).
* `condBias_zero_of_outcome_match`     — DR corollary (correct outcomes).
* `cond_exp_phi_eta_dir_deriv_at_truth_zero` — differentiated orthogonality
                                     statement at the truth.
-/

module
public import Causalean.Estimation.CATE.Core.ConditionalBias_Part2
/-!
Conditional-bias tools for conditional average treatment-effect estimators. They separate pointwise target bias from nuisance and approximation errors.
-/
