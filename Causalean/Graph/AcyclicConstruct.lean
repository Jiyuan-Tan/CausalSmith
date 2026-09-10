/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.DAG

/-! # Constructing a DAG from a raw acyclic edge relation

Since `DAG` stores acyclicity directly (`acyclic : ∀ v, ¬ Relation.TransGen edge v v`),
building one only requires exhibiting the edge relation, its decidability, and a
proof that it has no directed cycle. This file provides:

* `DAG.ofAcyclic e hac` — from an edge relation `e` whose transitive closure is
  irreflexive (`hac`). Materialises the graph directly. (Used e.g. for the
  Verma–Pearl covered-edge reversal, where acyclicity of the modified relation is
  known before any topological numbering.)

For constructions that already carry a topological numbering, build the `DAG`
structure directly and discharge its `acyclic` field with
`DAG.acyclic_of_topoOrder` (in `Causalean.Graph.DAG`), which keeps the edge
relation definitionally transparent.
-/

namespace Causalean

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Given [an edge relation on a finite vertex set](hyp:e) for which [no vertex can return to itself by a nonempty directed path](hyp:hac), the [directed acyclic graph constructed from that relation](goal) has precisely that edge relation.

    The graph materializes the supplied relation directly. -/
noncomputable def ofAcyclic (e : V → V → Prop)
    (hac : ∀ v, ¬ Relation.TransGen e v v) : DAG V where
  edge := e
  decEdge := Classical.decRel e
  acyclic := hac

/-- The directed acyclic graph `ofAcyclic e hac`, built from an edge relation `e` together with
[a proof that `e` has no directed cycle](hyp:hac), [has exactly `e` as its edge
relation](goal). -/
@[simp] theorem ofAcyclic_edge (e : V → V → Prop)
    (hac : ∀ v, ¬ Relation.TransGen e v v) :
    (ofAcyclic e hac).edge = e := rfl

end DAG

end Causalean
