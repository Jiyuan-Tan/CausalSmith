/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation

/-! # Directed Acyclic Graphs

This file provides finite directed acyclic graphs. A `DAG` is represented by a
decidable edge relation together with the standard acyclicity condition: no
vertex reaches itself along a directed path (`∀ v, ¬ Relation.TransGen edge v v`).
This is the textbook definition, and it is the entire data of the structure — a
`DAG` is determined by its edge relation.

A topological numbering is **not** part of the definition; it is *derived*. The
strict ancestors of a vertex are computed by a finite backward-reachability
fixpoint (`ancClosure`), which yields both a decidable ancestor relation
(`decIsAncestor`, order-free and computable) and a canonical strict-ancestor count
(`ancestorRank`, computable). The topological order
`topoOrder v = rank v * |V| + enum v` is built on the rank; it satisfies
injectivity (`topoOrder_injective`) and edge-consistency (`topoOrder_lt`), so
downstream constructions that need a topological order use it exactly as before.
`topoOrder` is `noncomputable` because the tie-breaking enumeration of a bare
finite type needs a choice of ordering; it is used purely for its ordering
properties, never reduced on concrete values (decidable ancestry goes through
`ancClosure`).

This file also defines immediate neighborhoods (`parents`, `children`), strict
reachability (`isAncestor`, `isDescendant`), finite ancestor/descendant sets,
set-level ancestry operations (`ancestralSet`, `descendantsSet`), non-descendants,
and roots.

## References

* Basic Concepts.tex, Definition 1 (Directed Acyclic Graph)
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A Directed Acyclic Graph on a finite vertex type: [a decidable edge
relation](hyp:edge,decEdge) together with the condition that [no vertex is connected to itself by
a directed path](hyp:acyclic) — the transitive closure of the edge relation is irreflexive.
Irreflexivity of the transitive closure is exactly the statement that the graph
has no directed cycle.

The acyclicity condition is the whole content of the structure, so a DAG is
determined by its edge relation. A topological order is not stored; it is derived
(see `DAG.topoOrder`). -/
structure DAG (V : Type*) [DecidableEq V] [Fintype V] where
  /-- The edge relation: `edge u v` means there is a directed edge from `u` to `v`. -/
  edge : V → V → Prop
  /-- Decidability of the edge relation. -/
  decEdge : DecidableRel edge
  /-- **Acyclicity.** No vertex reaches itself along a directed path: the
      transitive closure of `edge` is irreflexive. Equivalently, the graph has no
      directed cycle. This is the defining property of a DAG. -/
  acyclic : ∀ v, ¬ Relation.TransGen edge v v

attribute [instance] DAG.decEdge

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : DAG V)

-- ============================================================
-- Parents, Children
-- ============================================================

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a vertex](hyp:v), [the parent set](goal) is the finite set of all vertices having a directed edge into that vertex. -/
def parents (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.edge u v)

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a vertex](hyp:v), [the child set](goal) is the finite set of all vertices to which that vertex has a directed edge. -/
def children (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.edge v w)

/-- Membership characterization for `parents`: `u ∈ G.parents v ↔ G.edge u v`. -/
theorem mem_parents {v u : V} : u ∈ G.parents v ↔ G.edge u v := by
  simp [parents]

/-- Membership characterization for `children`: `w ∈ G.children v ↔ G.edge v w`. -/
theorem mem_children {v w : V} : w ∈ G.children v ↔ G.edge v w := by
  simp [children]

-- ============================================================
-- Ancestors, Descendants (via transitive closure)
-- ============================================================

/-- For [a finite vertex population with decidable equality](hyp:V) and [a directed acyclic graph on that population](hyp:G), the [ancestor relation](goal) holds from one vertex to another exactly when there is a directed path from the former to the latter. It is established either by [a directed edge from the former vertex to the latter](hyp:edge) or by [an existing ancestor path followed by a directed edge](hyp:trans). -/
inductive isAncestor : V → V → Prop
  | edge {u v : V} : G.edge u v → isAncestor u v
  | trans {u w v : V} : isAncestor u w → G.edge w v → isAncestor u v

/-- The inductive ancestor relation coincides with `Relation.TransGen` of the edge
relation: both are the transitive closure of the edge relation. -/
theorem isAncestor_iff_transGen {u v : V} :
    G.isAncestor u v ↔ Relation.TransGen G.edge u v := by
  constructor
  · intro h
    induction h with
    | edge he => exact Relation.TransGen.single he
    | trans _ he ih => exact ih.tail he
  · intro h
    induction h with
    | single he => exact isAncestor.edge he
    | tail _ he ih => exact isAncestor.trans ih he

/-- No vertex has an edge to itself (a directed self-loop would be a length-one cycle). -/
theorem irrefl (v : V) : ¬G.edge v v := by
  intro h
  exact G.acyclic v (Relation.TransGen.single h)

/-- If there is an edge from `u` to `v`, then there is no edge from `v` to `u`
(a two-cycle is forbidden by acyclicity). -/
theorem asymm {u v : V} (h : G.edge u v) : ¬G.edge v u := by
  intro h'
  exact G.acyclic u ((Relation.TransGen.single h).tail h')

/-- Ancestor relation is irreflexive: no vertex is its own ancestor (this is
acyclicity, restated for the inductive ancestor relation). -/
theorem isAncestor_irrefl (v : V) : ¬G.isAncestor v v := by
  intro h
  exact G.acyclic v (G.isAncestor_iff_transGen.mp h)

/-- Ancestor relation is transitive. -/
theorem isAncestor_trans {u v w : V} (h1 : G.isAncestor u v) (h2 : G.isAncestor v w) :
    G.isAncestor u w := by
  induction h2 with
  | edge he => exact isAncestor.trans h1 he
  | trans _ he ih => exact isAncestor.trans ih he

/-- First-step decomposition: if `u` is an ancestor of `v`, then either `edge u v`
    or there exists a child `c` of `u` such that `c` is an ancestor of `v`. -/
theorem isAncestor_child {u v : V} (h : G.isAncestor u v) :
    G.edge u v ∨ ∃ c, G.edge u c ∧ G.isAncestor c v := by
  induction h with
  | edge he => exact Or.inl he
  | trans _ he' ih =>
    rcases ih with he | ⟨c, huc, hcw⟩
    · exact Or.inr ⟨_, he, isAncestor.edge he'⟩
    · exact Or.inr ⟨c, huc, isAncestor.trans hcw he'⟩

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [two vertices, the first and the second](hyp:u,v), [the descendant relation](goal) holds precisely when there is a directed path from the second vertex to the first. -/
def isDescendant (u v : V) : Prop := G.isAncestor v u

-- ============================================================
-- Backward reachability fixpoint (order-free decidable ancestry)
-- ============================================================

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a finite vertex set](hyp:S), [one backward ancestor-expansion step](goal) returns that set together with every parent of every member of the set. -/
def ancStep (S : Finset V) : Finset V := S ∪ S.biUnion G.parents

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a vertex](hyp:v), [the strict-ancestor set](goal) is obtained by starting with the vertex’s parents and applying backward ancestor expansion once for each vertex in the population. -/
def ancClosure (v : V) : Finset V :=
  (G.ancStep)^[Fintype.card V] (G.parents v)

/-- One `ancStep` preserves the invariant "every element is an ancestor of `v`". -/
private theorem ancStep_preserves {v : V} {S : Finset V}
    (hS : ∀ x ∈ S, G.isAncestor x v) : ∀ x ∈ G.ancStep S, G.isAncestor x v := by
  intro x hx
  rw [ancStep, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact hS x hx
  · rw [Finset.mem_biUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact G.isAncestor_trans (isAncestor.edge (G.mem_parents.mp hxy)) (hS y hy)

/-- Iterating `ancStep` preserves the "ancestor of `v`" invariant. -/
private theorem iterate_ancStep_sound {v : V} {S : Finset V}
    (hS : ∀ x ∈ S, G.isAncestor x v) (k : ℕ) :
    ∀ x ∈ (G.ancStep)^[k] S, G.isAncestor x v := by
  induction k generalizing S with
  | zero => simpa using hS
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (G.ancStep_preserves hS)

/-- Each set is contained in its `ancStep`. -/
private theorem subset_ancStep (S : Finset V) : S ⊆ G.ancStep S := by
  intro x hx; rw [ancStep, Finset.mem_union]; exact Or.inl hx

/-- Any finite set of graph nodes remains contained after applying the graph's ancestor-step
operation any number of times. -/
theorem subset_iterate_ancStep (S : Finset V) (k : ℕ) :
    S ⊆ (G.ancStep)^[k] S := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (G.subset_ancStep _)

/-- A fixpoint of `ancStep` is fixed by any number of iterations. -/
private theorem iterate_of_fixpoint {T : Finset V} (h : G.ancStep T = T) (j : ℕ) :
    (G.ancStep)^[j] T = T := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, h]

omit G [DecidableEq V] [Fintype V] in
/-- If each of a specified number of successive applications of a function on finite
    sets strictly increases cardinality, the final set has grown by at least that number. -/
theorem le_card_iterate (f : Finset V → Finset V) (S₀ : Finset V) (k : ℕ)
    (hstrict : ∀ j, j < k →
      (f^[j] S₀).card < (f^[j + 1] S₀).card) :
    (f^[0] S₀).card + k ≤ (f^[k] S₀).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ihk := ih (fun j hj => hstrict j (Nat.lt_succ_of_lt hj))
    have hlast := hstrict k (Nat.lt_succ_self k)
    omega

/-- The backward-reachability closure is a fixpoint of `ancStep`: after `|V|`
iterations the accumulating set has stabilized (it either reached a fixpoint or
became all of `Finset.univ`). -/
private theorem ancStep_ancClosure (v : V) :
    G.ancStep (G.ancClosure v) = G.ancClosure v := by
  have hexists : ∃ k ≤ Fintype.card V,
      (G.ancStep)^[k] (G.parents v) = (G.ancStep)^[k + 1] (G.parents v) := by
    by_contra hcon
    push_neg at hcon
    have hstrict : ∀ j, j < Fintype.card V + 1 →
        ((G.ancStep)^[j] (G.parents v)).card < ((G.ancStep)^[j + 1] (G.parents v)).card := by
      intro j hj
      have hsub : (G.ancStep)^[j] (G.parents v) ⊆ (G.ancStep)^[j + 1] (G.parents v) := by
        rw [Function.iterate_succ_apply']; exact G.subset_ancStep _
      have hne : (G.ancStep)^[j] (G.parents v) ≠ (G.ancStep)^[j + 1] (G.parents v) :=
        hcon j (Nat.lt_succ_iff.mp hj)
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    have hge : ((G.ancStep)^[0] (G.parents v)).card + (Fintype.card V + 1)
        ≤ ((G.ancStep)^[Fintype.card V + 1] (G.parents v)).card :=
      le_card_iterate G.ancStep (G.parents v) (Fintype.card V + 1) hstrict
    have hle : ((G.ancStep)^[Fintype.card V + 1] (G.parents v)).card ≤ Fintype.card V :=
      Finset.card_le_univ _
    simp only [Function.iterate_zero, id_eq] at hge
    omega
  obtain ⟨k, hkN, hk⟩ := hexists
  have hfixk : G.ancStep ((G.ancStep)^[k] (G.parents v)) = (G.ancStep)^[k] (G.parents v) := by
    have hsucc : (G.ancStep)^[k + 1] (G.parents v) = G.ancStep ((G.ancStep)^[k] (G.parents v)) :=
      Function.iterate_succ_apply' G.ancStep k (G.parents v)
    rw [← hsucc]; exact hk.symm
  have hSN : (G.ancStep)^[Fintype.card V] (G.parents v) = (G.ancStep)^[k] (G.parents v) := by
    obtain ⟨d, hd⟩ := Nat.le.dest hkN
    rw [← hd, Nat.add_comm k d, Function.iterate_add_apply]
    exact G.iterate_of_fixpoint hfixk d
  unfold ancClosure
  rw [hSN]; exact hfixk

/-- Every parent of a vertex in its computed ancestor set also belongs to that ancestor set. -/
theorem ancClosure_closed (v : V) {x : V} (hx : x ∈ G.ancClosure v) :
    G.parents x ⊆ G.ancClosure v := by
  intro p hp
  have hbu : p ∈ (G.ancClosure v).biUnion G.parents := Finset.mem_biUnion.mpr ⟨x, hx, hp⟩
  have hstep : p ∈ G.ancStep (G.ancClosure v) := by
    rw [ancStep, Finset.mem_union]; exact Or.inr hbu
  rwa [G.ancStep_ancClosure v] at hstep

/-- A finite set that contains every parent of each of its vertices contains every ancestor of
each vertex it contains. -/
theorem isAncestor_mem_of_closed {T : Finset V}
    (hT : ∀ x ∈ T, G.parents x ⊆ T) {u w : V} (h : G.isAncestor u w) :
    w ∈ T → u ∈ T := by
  induction h with
  | edge e => intro hw; exact hT _ hw (G.mem_parents.mpr e)
  | trans _ e ih => intro hw; exact ih (hT _ hw (G.mem_parents.mpr e))

/-- Membership in the backward-reachability fixpoint is exactly ancestry:
a vertex lies in `G.ancClosure v` iff it is an ancestor of `v`. This makes the
ancestor relation decidable using only the (decidable) edge relation, with no
reference to any topological order. -/
theorem mem_ancClosure {u v : V} : u ∈ G.ancClosure v ↔ G.isAncestor u v := by
  constructor
  · intro hu
    have hbase : ∀ x ∈ G.parents v, G.isAncestor x v :=
      fun x hx => isAncestor.edge (G.mem_parents.mp hx)
    exact G.iterate_ancStep_sound hbase (Fintype.card V) u hu
  · intro h
    have hclosed : ∀ x ∈ G.ancClosure v, G.parents x ⊆ G.ancClosure v :=
      fun x hx => G.ancClosure_closed v hx
    have hpar : G.parents v ⊆ G.ancClosure v :=
      G.subset_iterate_ancStep (G.parents v) (Fintype.card V)
    cases h with
    | edge e => exact hpar (G.mem_parents.mpr e)
    | trans h' e => exact G.isAncestor_mem_of_closed hclosed h' (hpar (G.mem_parents.mpr e))

/-- For [a finite vertex population with decidable equality](hyp:V) and [a directed acyclic graph on that population](hyp:G), the [decision procedure for the ancestor relation](goal) determines, for every ordered pair of vertices, whether the first is an ancestor of the second.

    It is computed from the edge relation alone via the backward-reachability fixpoint `ancClosure`. -/
instance decIsAncestor : DecidableRel G.isAncestor :=
  fun u v => decidable_of_iff _ (G.mem_ancClosure (u := u) (v := v))

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a vertex](hyp:v), [the ancestor set](goal) is the finite set of all vertices from which a directed path reaches that vertex. -/
def ancestors (v : V) : Finset V :=
  Finset.univ.filter (fun u => G.isAncestor u v)

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a vertex](hyp:v), [the descendant set](goal) is the finite set of all vertices reachable from that vertex by a directed path. -/
def descendants (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.isAncestor v w)

/-- Membership characterization for `ancestors`: `u ∈ G.ancestors v ↔ G.isAncestor u v`. -/
theorem mem_ancestors {v u : V} : u ∈ G.ancestors v ↔ G.isAncestor u v := by
  simp [ancestors]

/-- Membership characterization for `descendants`: `w ∈ G.descendants v ↔ G.isAncestor v w`. -/
theorem mem_descendants {v w : V} : w ∈ G.descendants v ↔ G.isAncestor v w := by
  simp [descendants]

/-- Parents are a subset of ancestors. -/
theorem parents_subset_ancestors (v : V) : G.parents v ⊆ G.ancestors v := by
  intro u hu
  rw [mem_ancestors]
  exact isAncestor.edge (G.mem_parents.mp hu)

/-- Children are a subset of descendants. -/
theorem children_subset_descendants (v : V) : G.children v ⊆ G.descendants v := by
  intro w hw
  rw [mem_descendants]
  exact isAncestor.edge (G.mem_children.mp hw)

-- ============================================================
-- Ancestors/Descendants of a set
-- ============================================================

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a finite vertex set](hyp:S), [the set of its strict ancestors](goal) contains exactly the vertices from which a directed path reaches at least one member of the given set. -/
def ancestorsSet (S : Finset V) : Finset V :=
  Finset.univ.filter (fun u => ∃ v ∈ S, G.isAncestor u v)

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a finite vertex set](hyp:S), [its ancestral closure](goal) is that set together with every vertex from which a directed path reaches one of its members. -/
def ancestralSet (S : Finset V) : Finset V :=
  S ∪ G.ancestorsSet S

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a finite vertex set](hyp:S), [the set of its strict descendants](goal) contains exactly the vertices reachable by a directed path from at least one member of the given set. -/
def descendantsSet (S : Finset V) : Finset V :=
  Finset.univ.filter (fun w => ∃ v ∈ S, G.isAncestor v w)

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a vertex](hyp:v), [the non-descendant set](goal) contains exactly the vertices other than that vertex which cannot be reached from it by a directed path. -/
def nonDescendants (v : V) : Finset V :=
  Finset.univ.filter (fun w => ¬G.isAncestor v w ∧ w ≠ v)

-- ============================================================
-- Canonical topological order (derived)
-- ============================================================

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a vertex](hyp:v), [its ancestor rank](goal) is the number of that vertex’s strict ancestors. -/
def ancestorRank (v : V) : ℕ := (G.ancClosure v).card

/-- Along an edge the strict-ancestor count strictly increases. -/
theorem ancestorRank_lt_of_edge {a b : V} (hab : G.edge a b) :
    G.ancestorRank a < G.ancestorRank b := by
  unfold ancestorRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · rw [mem_ancClosure]; exact isAncestor.edge hab
    · rw [mem_ancClosure]; exact G.isAncestor_irrefl a
  · intro w hw
    rw [mem_ancClosure] at hw ⊢
    exact G.isAncestor_trans hw (isAncestor.edge hab)

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a vertex](hyp:v), [the derived topological number](goal) is its number of strict ancestors times the population size, plus a fixed tie-breaking enumeration number. This number is injective across vertices and strictly increases along every directed edge.

This is `noncomputable` because the tie-breaking enumeration of a bare finite
type requires a choice of ordering (there is no computable enumeration of an
arbitrary `Fintype`); the underlying rank `ancestorRank` is computable.
`topoOrder` is used only for its ordering properties, never reduced
on concrete values — the decidable ancestor relation `decIsAncestor` is computed
independently via `ancClosure`. -/
noncomputable def topoOrder (v : V) : ℕ :=
  G.ancestorRank v * Fintype.card V + (Fintype.equivFin V v).val

/-- The derived topological order is injective, so it provides a canonical total
order on the finite vertex type. -/
theorem topoOrder_injective : Function.Injective G.topoOrder := by
  intro u v huv
  unfold topoOrder at huv
  have hu : (Fintype.equivFin V u).val < Fintype.card V := (Fintype.equivFin V u).isLt
  have hv : (Fintype.equivFin V v).val < Fintype.card V := (Fintype.equivFin V v).isLt
  have hmod : (Fintype.equivFin V u).val = (Fintype.equivFin V v).val := by
    have := congrArg (· % Fintype.card V) huv
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using this
  have : (Fintype.equivFin V u) = (Fintype.equivFin V v) := Fin.ext hmod
  exact (Fintype.equivFin V).injective this

/-- The derived topological order is edge-consistent: if there is an edge from `u`
to `v`, then `topoOrder u < topoOrder v`. This witnesses acyclicity. -/
theorem topoOrder_lt : ∀ u v, G.edge u v → G.topoOrder u < G.topoOrder v := by
  intro u v huv
  unfold topoOrder
  have hrank : G.ancestorRank u < G.ancestorRank v := G.ancestorRank_lt_of_edge huv
  have hv : (Fintype.equivFin V v).val < Fintype.card V := (Fintype.equivFin V v).isLt
  have hu : (Fintype.equivFin V u).val < Fintype.card V := (Fintype.equivFin V u).isLt
  have hle : G.ancestorRank u + 1 ≤ G.ancestorRank v := by omega
  have key : (G.ancestorRank u + 1) * Fintype.card V ≤ G.ancestorRank v * Fintype.card V :=
    Nat.mul_le_mul hle (le_refl (Fintype.card V))
  have expand : (G.ancestorRank u + 1) * Fintype.card V
      = G.ancestorRank u * Fintype.card V + Fintype.card V := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Ancestors respect the topological order: if `u` is an ancestor of `v` then
`G.topoOrder u < G.topoOrder v`, so ancestor pairs are strictly ordered by `topoOrder`. -/
theorem isAncestor_topoOrder_lt {u v : V} (h : G.isAncestor u v) :
    G.topoOrder u < G.topoOrder v := by
  induction h with
  | edge he => exact G.topoOrder_lt _ _ he
  | trans _ he ih => exact Nat.lt_trans ih (G.topoOrder_lt _ _ he)

-- ============================================================
-- Root nodes
-- ============================================================

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G) and [a vertex](hyp:v), [the root condition](goal) holds exactly when no directed edge enters that vertex. -/
def isRoot (v : V) : Prop := G.parents v = ∅

/-- For [a finite vertex population with decidable equality](hyp:V), [a directed acyclic graph on that population](hyp:G), and [a vertex](hyp:v), the [decision procedure for the root condition](goal) determines whether no directed edge enters that vertex.

    It reduces to deciding whether the parent set is empty. -/
instance decIsRoot (v : V) : Decidable (G.isRoot v) :=
  inferInstanceAs (Decidable (G.parents v = ∅))

/-- For [a finite directed acyclic graph on a vertex population](hyp:V,G), [the root set](goal) is the finite set of all vertices with no incoming directed edge. -/
def roots : Finset V :=
  Finset.univ.filter (fun v => G.isRoot v)

-- ============================================================
-- Acyclicity from an explicit topological numbering
-- ============================================================

omit [DecidableEq V] [Fintype V] in
/-- **Acyclicity from a topological ranking.** Given an edge relation `e` on `V` and a ranking
function `τ` into a type equipped with a transitive, irreflexive relation `r`, if [`τ` strictly
increases (with respect to `r`) along every edge of `e`](hyp:hτ), then [`e` has no directed
cycle: no vertex is reachable from itself via the transitive closure of `e`](goal).

A cycle `v ⇝ v` would force the strictly increasing `τ` to satisfy `r (τ v) (τ v)`,
contradicting irreflexivity of `r`. This is the standard way to discharge the `acyclic` field
when building a `DAG` from a construction that already carries a topological numbering
in hand (concrete examples, SWIG parity orders, a parent graph's order).

The numbering appears only inside this (proof-level) lemma, so a `DAG` whose
`acyclic` field is `DAG.acyclic_of_topoOrder hτ` stays computable even when the
witnessing `τ` is `noncomputable` — the witness certifies acyclicity but is erased,
and the resulting DAG's own `topoOrder` is the canonical derived rank, not `τ`. -/
theorem acyclic_of_topoOrder {W : Type*} {r : W → W → Prop} [IsTrans W r] [Std.Irrefl r]
    {e : V → V → Prop} {τ : V → W}
    (hτ : ∀ u v, e u v → r (τ u) (τ v)) : ∀ v, ¬ Relation.TransGen e v v := by
  have key : ∀ {a b : V}, Relation.TransGen e a b → r (τ a) (τ b) := by
    intro a b h
    induction h with
    | single hab => exact hτ _ _ hab
    | tail _ hbc ih => exact IsTrans.trans _ _ _ ih (hτ _ _ hbc)
  intro v hv
  exact absurd (key hv) (Std.Irrefl.irrefl _)

/-- Every vertex reached by a nonempty directed path has an incoming edge, namely the
final edge of that path. -/
theorem isAncestor_has_parent (G : DAG V) {u v : V}
    (h : G.isAncestor u v) : G.parents v ≠ ∅ := by
  intro hempty
  have hmem : ∀ w, w ∉ G.parents v :=
    fun w => (Finset.eq_empty_iff_forall_notMem.mp hempty) w
  induction h with
  | edge he => exact hmem u (G.mem_parents.mpr he)
  | trans _ he _ => exact hmem _ (G.mem_parents.mpr he)

end DAG

end Causalean
