/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATT.ATTInstance
public import Causalean.Estimation.ATT.DML
public import Causalean.Estimation.ATT.DML.AsymptoticNormality
public import Causalean.Estimation.ATT.DML.Feasible
public import Causalean.Estimation.ATT.InfluenceFunction
public import Causalean.Estimation.ATT.Remainder
public import Causalean.Estimation.ATT.Remainder.Bound
public import Causalean.Estimation.ATT.Remainder.Identity
public import Causalean.Estimation.ATT.Score.AIPWMoment
public import Causalean.Estimation.ATT.Score.AIPWScoreL2
public import Causalean.Estimation.ATT.Score.FiniteVar
public import Causalean.Estimation.ATT.Score.MeanZero
public import Causalean.Estimation.ATT.Score.ScorePullout
public import Causalean.Estimation.ATT.Setup

/-!
# Estimation of the average treatment effect on the treated

Double machine learning for the average treatment effect on the treated (ATT) under back-door
adjustment, using the score A·(Y − μ₀(X)) − (1 − A)·e(X)/(1 − e(X))·(Y − μ₀(X)) − A·θ, which
involves only the control regression μ₀ and the propensity score e. At the truth the score has
mean zero and finite variance, and at a wrong nuisance pair its population mean is the single
cross-product ∫ (ê − e)/(1 − ê)·(μ̂₀ − μ₀) dP_X, bounded by (1/ε)·‖μ̂₀ − μ₀‖₂·‖ê − e‖₂ under
one-sided overlap e ≤ 1 − ε. The sample-split estimator that divides by the sample treated share
is asymptotically linear with influence function equal to the score at the truth divided by the
treated probability, and after scaling by the true standard deviation it converges to N(0,1).
The asymptotic results take as hypotheses nuisance estimators fitted on the other fold whose
errors are o_p(1) and whose error product is o_p(n^{-1/2}), together with the listed
measurability and integrability conditions.

## Contents

* `Setup` — `TreatedEstimationSystem`, `OneSidedOverlap`, the target `θ₀` and `θ₀_eq_ATT`.
* `Score/` — `aipwMomentATT`, `ψ_ATT`, `aipw_mean_zero_ATT`, `aipw_finite_var_ATT`, and L²
  continuity of the score in the nuisances.
* `Remainder/` — `aipw_remainder_identity_ATT`, `aipw_remainder_bound_ATT`,
  `aipw_remainder_op_ATT`.
* `DML`, `ATTInstance` — the oracle estimator with known treated probability and its asymptotic
  linearity.
* `DML/Feasible`, `DML/AsymptoticNormality` — `dml_ATT_isAsymLinear` and
  `dml_ATT_tendstoStandardNormal` for the feasible estimator.
-/

public section
