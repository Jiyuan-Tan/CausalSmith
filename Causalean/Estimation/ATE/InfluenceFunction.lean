/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW influence function for the back-door ATE — umbrella

Re-exports the influence-function submodules into a single import target consumed by
`PlugIn.lean` and the DML development:

* `Setup.lean`          — `BackdoorEstimationSystem`, `P_X`, `factualZ`, `P_Z`,
                          `θ₀`, `θ₀_eq_ATE`, `StrictOverlap`.
* `Score/AIPWMoment.lean`     — `aipwMoment`, `ψ_AIPW`, `NuisanceVec` + algebraic
                          instances, `H_ε_aeL2`, `aipwMomentFunctional`.
* `Score/MeanZero.lean`       — `lem:est-aipw-mean-zero` and helpers
                          (`cond_exp_residual_zero`, `theta_zero_factualX_integral`,
                          `aipw_mean_zero`).
* `Score/ScorePullout.lean`    — shared pull-out and residual lemmas
                          (`e_val_label`, `weighted_residual_integral_zero`,
                          `indicator_to_propScore_integral`).
* `Score/FiniteVar.lean`      — `lem:est-aipw-finite-var` (proved).

The active DML proof uses the per-nuisance bilinear remainder identity and
bound exported by `Remainder/Identity.lean` and `Remainder/Bound.lean`.

References (NL doc):
* `def:est-ate-nuisance`         — value-space `(μ, e)`.
* `def:est-aipw-moment`          — `m_AIPW`.
* `def:est-aipw-nuisance-space`  — a.e.-overlap and L² nuisance set
                                    `H_ε_aeL2`.
* `lem:est-aipw-mean-zero`       — `E[ψ_AIPW] = 0`.
* `lem:est-aipw-finite-var`      — `E[ψ_AIPW²] < ∞`.
-/

module
public import Causalean.Estimation.ATE.Score.MeanZero
public import Causalean.Estimation.ATE.Score.ScorePullout
public import Causalean.Estimation.ATE.Score.FiniteVar

/-!
# The AIPW influence function for the average treatment effect

Population properties of the augmented inverse-probability-weighted (AIPW) score for the average
treatment effect under back-door adjustment,

    ψ(X, D, Y) = μ(1,X) − μ(0,X) + D·(Y − μ(1,X))/e(X) − (1 − D)·(Y − μ(0,X))/(1 − e(X)) − θ₀,

evaluated at the true outcome regressions μ, propensity score e and effect θ₀. Under the
back-door identification assumptions the score has mean zero under the law of the observed
triple, provided the two inverse-propensity-weighted residual terms are integrable; under strict
overlap, a finite second moment of the outcome and square-integrable outcome regressions it is
square-integrable. These are the two facts that plug-in and double-machine-learning arguments
need from the score.

## Main results

* `aipw_mean_zero` — the AIPW score has mean zero (`Score/MeanZero`; the estimation system,
  observed-data law, moment `aipwMoment` and score `ψ_AIPW` come from `Score/AIPWMoment`).
* `aipw_finite_var` — the AIPW score is square-integrable (`Score/FiniteVar`);
  `aipw_finite_var_of_counterfactual_sq` derives the same from potential-outcome second moments.
* `weighted_residual_integral_zero`, `indicator_to_propScore_integral` — the conditioning
  identities that remove propensity-weighted residuals (`Score/ScorePullout`).
-/

public section
