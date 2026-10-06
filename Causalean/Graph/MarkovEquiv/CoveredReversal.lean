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

/-! # Covered-edge reversal

This barrel collects the covered-edge route used in the hard direction of the Verma–Pearl
characterization. `FlipEdge` constructs the reversal and proves that it preserves the skeleton
and immoralities. `ActivePathTransport` and `PathSurgery` develop the active-walk transport
machinery. `MarkovEquivalence` proves that one covered-edge reversal preserves every
d-separation statement. `Causalean.Graph.MarkovEquiv.Decompose` assembles these single-edge
steps into the full hard direction.
-/
