/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.DSep.Separation

/-! # Markov equivalence of DAGs — basic definitions

This file introduces the combinatorial vocabulary for the Verma–Pearl characterization of
Markov equivalence. Two directed acyclic graphs on the same vertices are **Markov
equivalent** when they encode exactly the same d-separation statements, i.e. the same
conditional-independence constraints. The Verma–Pearl theorem (proved in the umbrella
file) says this happens precisely when the graphs share a *skeleton* and the same
*v-structures* (immoralities).

The definitions here are:

* `DAG.IsImmorality G a b c` — there is a v-structure (immorality) `a → b ← c` whose two
  parents `a, c` are non-adjacent and distinct;
* `SameSkeleton G₁ G₂` — the two graphs have the same undirected adjacency;
* `SameImmoralities G₁ G₂` — the two graphs have the same v-structures;
* `MarkovEquiv G₁ G₂` — the two graphs declare the same d-separations.

All of these are decidable on a finite vertex type. The underlying undirected adjacency is
the existing `DAG.UAdj` (`a` and `b` joined by an edge in either direction) and a collider
`a → b ← c` is `DAG.IsCollider`.
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [three ordered vertices](hyp:a,b,c), [the v-structure, or immorality, condition](goal) holds exactly when the first and third vertices are distinct, each has a directed edge into the second, and no directed edge joins the first and third in either direction.

Immoralities are the colliders whose parents are non-adjacent; they are exactly the part of the collider structure that is visible to conditional independence. -/
def IsImmorality (a b c : V) : Prop :=
  G.edge a b ∧ G.edge c b ∧ ¬ G.UAdj a c ∧ a ≠ c

/-- For [a finite vertex population with decidable equality](hyp:V), [a directed acyclic graph on that population](hyp:G), and [three ordered vertices](hyp:a,b,c), the [decision procedure for the v-structure condition](goal) determines whether the first and third vertices are distinct non-adjacent parents of the second. -/
instance (a b c : V) : Decidable (G.IsImmorality a b c) := by
  unfold IsImmorality; infer_instance

end DAG

/-- For [a finite vertex population](hyp:V) and [two directed acyclic graphs on it](hyp:G₁,G₂), [the same-skeleton condition](goal) holds exactly when, for every pair of vertices, a directed edge joins the pair in either direction in the first graph if and only if one does in the second graph. -/
def SameSkeleton (G₁ G₂ : DAG V) : Prop := ∀ a b, G₁.UAdj a b ↔ G₂.UAdj a b

/-- For [a finite vertex population](hyp:V) and [two directed acyclic graphs on it](hyp:G₁,G₂), [the same-immoralities condition](goal) holds exactly when, for every ordered triple of vertices, it is an immorality in the first graph if and only if it is an immorality in the second graph. -/
def SameImmoralities (G₁ G₂ : DAG V) : Prop :=
  ∀ a b c, G₁.IsImmorality a b c ↔ G₂.IsImmorality a b c

/-- For [a finite vertex population](hyp:V) and [two directed acyclic graphs on it](hyp:G₁,G₂), [Markov equivalence](goal) holds exactly when, for every three finite vertex sets, the first and second sets are d-separated by the third in the first graph if and only if they are d-separated in the second graph.

Equivalently, via the global Markov property, the two graphs impose the same conditional-independence constraints on every distribution. Pairwise disjointness is already part of d-separation, so it need not be repeated here. -/
def MarkovEquiv (G₁ G₂ : DAG V) : Prop :=
  ∀ X Y Z : Finset V, G₁.dSep X Y Z ↔ G₂.dSep X Y Z

/-- For [a finite vertex population with decidable equality](hyp:V) and [two directed acyclic graphs on that population](hyp:G₁,G₂), the [decision procedure for the same-skeleton condition](goal) determines whether the graphs have identical undirected adjacencies for every pair of vertices. -/
instance (G₁ G₂ : DAG V) : Decidable (SameSkeleton G₁ G₂) := by
  unfold SameSkeleton; infer_instance

/-- For [a finite vertex population with decidable equality](hyp:V) and [two directed acyclic graphs on that population](hyp:G₁,G₂), the [decision procedure for the same-immoralities condition](goal) determines whether the graphs have identical v-structures for every ordered triple of vertices. -/
instance (G₁ G₂ : DAG V) : Decidable (SameImmoralities G₁ G₂) := by
  unfold SameImmoralities; infer_instance

/-- For [any DAG `G`](hyp:G), [`G` is Markov equivalent to itself](goal). -/
@[refl] theorem MarkovEquiv.refl (G : DAG V) : MarkovEquiv G G :=
  fun _ _ _ => Iff.rfl

/-- Markov equivalence is symmetric. -/
theorem MarkovEquiv.symm {G₁ G₂ : DAG V} (h : MarkovEquiv G₁ G₂) : MarkovEquiv G₂ G₁ :=
  fun X Y Z => (h X Y Z).symm

/-- Markov equivalence is transitive. -/
theorem MarkovEquiv.trans {G₁ G₂ G₃ : DAG V}
    (h₁ : MarkovEquiv G₁ G₂) (h₂ : MarkovEquiv G₂ G₃) : MarkovEquiv G₁ G₃ :=
  fun X Y Z => (h₁ X Y Z).trans (h₂ X Y Z)

end Causalean
