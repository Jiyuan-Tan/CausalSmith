/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.FiniteRaoBlackwell.Core
public import Causalean.Stat.FiniteRaoBlackwell.DesignPushforward
public import Causalean.Stat.FiniteRaoBlackwell.KernelBridge
public import Causalean.Stat.FiniteRaoBlackwell.Poisson
public import Causalean.Stat.FiniteRaoBlackwell.Posterior
public import Causalean.Stat.FiniteRaoBlackwell.RaoBlackwell
public import Causalean.Stat.FiniteRaoBlackwell.Sufficiency
public import Causalean.Stat.FiniteRaoBlackwell.Core
public import Causalean.Stat.FiniteRaoBlackwell.DesignPushforward
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix
public import Causalean.Stat.FiniteRaoBlackwell.KernelBridge
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram
public import Causalean.Stat.FiniteRaoBlackwell.Posterior
public import Causalean.Stat.FiniteRaoBlackwell.RaoBlackwell
public import Causalean.Stat.FiniteRaoBlackwell.Sufficiency

/-!
Rao–Blackwell results for finite sampling designs, including Poisson designs. Use them to improve estimators by conditioning on informative statistics.
-/
