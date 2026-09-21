/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.Density.FiniteDAG.LocalMarkov.Coordinates
public import Causalean.Graph.Density.FiniteDAG.LocalMarkov.Local
public import Causalean.Graph.Density.FiniteDAG.LocalMarkov.Main

/-!
Local Markov properties for finite directed acyclic graphs. They connect each variable's conditional law to its parents and non-descendants.
-/

public section
