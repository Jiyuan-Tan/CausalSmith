/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.MarkovEquiv.CoveredReversal.FlipEdge
public import Causalean.Graph.MarkovEquiv.CoveredReversal.ActivePathTransport
public import Causalean.Graph.MarkovEquiv.CoveredReversal.PathSurgery
public import Causalean.Graph.MarkovEquiv.CoveredReversal.MarkovEquivalence

/-!
# Covered-edge reversal

Reversing a covered edge of a directed acyclic graph does not change its d-separations. An edge
a → b is covered when every other vertex is a parent of a exactly when it is a parent of b.
Reversing such an edge gives another directed acyclic graph with the same skeleton and the same
v-structures, and the two graphs are Markov equivalent: every d-separation statement holds in one
exactly when it holds in the other. This is the single-step invariance behind the converse
direction of the Verma–Pearl theorem; `Causalean.Graph.MarkovEquiv.Decompose` chains such steps
to connect any two graphs with the same skeleton and v-structures.

## Contents

* `FlipEdge` — `DAG.IsCoveredEdge`, the reversed graph `DAG.flipEdge` (shown acyclic),
  `flipEdge_sameSkeleton` and `flipEdge_sameImmoralities`.
* `ActivePathTransport`, `PathSurgery` — d-connection as existence of an active walk, and the
  walk operations that carry an active walk across the reversal.
* `MarkovEquivalence` — `markovEquiv_flipEdge`: the graph and its covered-edge reversal are
  Markov equivalent.
-/
