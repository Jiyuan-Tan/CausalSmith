/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.SuperPopulation.Network.MeanAsymptotics.AsymptoticNormality
public import Causalean.Experimentation.SuperPopulation.Network.MeanAsymptotics.Field
public import Causalean.Experimentation.SuperPopulation.Network.MeanAsymptotics.Hypotheses

/-!
# Standardized asymptotic normality of the network sample mean

This roll-up imports the construction of centered, variance-normalized network fields, the
hypotheses that make those fields mean-zero and unit-variance, and the final CLT turning the
abstract m-dependent network-sum theorem into asymptotic normality for network sample means.
-/
