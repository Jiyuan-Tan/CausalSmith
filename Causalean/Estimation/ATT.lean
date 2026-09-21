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

/-! # Estimation of the average treatment effect on the treated

This barrel exports the ATT identification-compatible AIPW score, remainder
analysis, oracle comparison, feasible sample-share DML estimator, asymptotic
linearity theorem, and standardized Gaussian limit.
-/

public section
