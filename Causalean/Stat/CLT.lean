/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.CLT.AsymptoticLinearityVec
public import Causalean.Stat.CLT.ChiSquared
public import Causalean.Stat.CLT.ChiSquaredProjection
public import Causalean.Stat.CLT.FiniteDesignConditioning
public import Causalean.Stat.CLT.FunctionalDelta
public import Causalean.Stat.CLT.GaussianCharFunBridge
public import Causalean.Stat.CLT.GaussianLimit
public import Causalean.Stat.CLT.GaussianTail
public import Causalean.Stat.CLT.HadamardDeriv
public import Causalean.Stat.CLT.Lindeberg

public import Causalean.Stat.CLT.Martingale
public import Causalean.Stat.CLT.Martingale.Basic
public import Causalean.Stat.CLT.Martingale.CharacteristicFunction
public import Causalean.Stat.CLT.Martingale.CompensatedStep
public import Causalean.Stat.CLT.Martingale.CompensatedTelescoping
public import Causalean.Stat.CLT.Martingale.ConditionalTaylor
public import Causalean.Stat.CLT.Martingale.ConditionalTelescoping
public import Causalean.Stat.CLT.Martingale.ExponentialBounds
public import Causalean.Stat.CLT.Martingale.GaussianBounds
public import Causalean.Stat.CLT.Martingale.Lyapunov
public import Causalean.Stat.CLT.Martingale.Main
public import Causalean.Stat.CLT.Martingale.PredictableVarianceBounds
public import Causalean.Stat.CLT.Martingale.ProbabilityBounds
public import Causalean.Stat.CLT.Martingale.RemainderBudget
public import Causalean.Stat.CLT.Martingale.StoppedArray
public import Causalean.Stat.CLT.Martingale.StoppedBudget
public import Causalean.Stat.CLT.MultivariateCLT
public import Causalean.Stat.CLT.SecondMomentOperator
public import Causalean.Stat.CLT.VectorWLLN

/-!
Central limit theory, including martingale extensions. Use these results to justify Gaussian approximations for normalized estimators.
-/
