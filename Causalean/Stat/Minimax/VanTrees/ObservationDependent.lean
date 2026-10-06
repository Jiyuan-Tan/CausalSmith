/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Basic
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.GuardedInformation
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.IntegrationByParts
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Main
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.WeightedL2

/-!
Observation-dependent versions of the van Trees information inequality. They bound estimation precision when information or priors vary with the observed design.
-/

public section
