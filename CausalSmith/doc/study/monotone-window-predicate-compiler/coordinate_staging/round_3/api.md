Warning: truncated output (original token count: 123229)
Total output lines: 3193

472429 ../../CausalSmith/doc/study/monotone-window-predicate-compiler/coordinate_staging/round_2/api.md
Warning: truncated output (original token count: 551782)
... 1158551 bytes omitted ...

# Causalean Lean 4 Library — API Reference

This document is **docstring-canonical**: each declaration's plain-English description is authored in its Lean docstring (first paragraph = the NL translation), and the per-declaration tables below are a *derived* view of those docstrings (signatures come from the compiled types). Do not hand-edit a per-declaration description or signature here — edit the declaration's docstring, then regenerate (`lake build && lake exe library_index` to refresh the index, then `cd CausalSmith/tools && npm run doc:gen` to re-splice the tables). Per-decl tables live inside `<!-- GEN:<module> -->` … `<!-- /GEN -->` markers; everything outside them (per-submodule narrative, conceptual grouping, usage examples drawn from `SCM/Examples/IV.lean`) is hand-written. CI runs `npm run doc:check`. For per-declaration lookup, prefer `npm run search` (`--scope module` for file-level orientation) over reading this file.

---

## 1. `Graph/DAG.lean` — Directed Acyclic Graphs

### Structure: `DAG V`

A DAG on a finite vertex type `V` with decidable equality.

| Field | Type | Description |
|---|---|---|
| `edge` | `V → V → Prop` | Directed edge relation |
| `decEdge` | `DecidableRel edge` | Decidability instance (auto-registered) |
| `topoOrder` | `V → ℕ` | Topological ordering witness |
| `topoOrder_lt` | `∀ u v, edge u v → topoOrder u < topoOrder v` | Edges respect the ordering (witnesses acyclicity) |

**Construction pattern:**

```lean
inductive MyNode | A | B | C deriving DecidableEq, Repr
instance : Fintype MyNode where ...

def myDAG : DAG MyNode where
  edge     | .A, .B => True | .B, .C => True | _, _ => False
  decEdge  := inferInstance  -- after proving DecidableRel
  topoOrder | .A => 0 | .B => 1 | .C => 2
  topoOrder_lt := by intro u v h; cases u <;> cases v <;> simp_all [...]
```

See `SCM/Examples/IV.lean` for a full 4-node example.

**Term-mode ancestry proofs:**

```lean
-- One edge: use .edge
example : ivDAG.isAncestor Z D :=
  DAG.isAncestor.edge (show ivDAG.edge Z D from trivial)

-- Transitivity: use .trans (ancestor_proof) (edge_proof)
example : ivDAG.isAncestor Z Y :=
  DAG.isAncestor.trans
    (DAG.isAncestor.edge (show ivDAG.edge Z D from trivial))
    (show ivDAG.edge D Y from trivial)
```

### Declarations

_Generated from docstrings — do not hand-edit; run `npm run doc:gen` (see CLAUDE.md). Edit the Lean docstring to change a description._

<!-- GEN:Causalean.Graph.DAG -->
| Decl | Signature | Description |
|---|---|---|
| `DAG` | `(V : Type u_2) → [DecidableEq V] → [Fintype V] → Type u_2` | A Directed Acyclic Graph on a finite vertex type: a decidable edge relation together with the condition that no vertex is connected to itself by a directed path — the transitive closure of the edge relation is irreflexive. Irreflexivity of the transitive closure is exactly the statement that the graph has no directed cycle. |
| `DAG.parents` | `V → Finset V` | For a finite directed acyclic graph on a vertex population and a vertex, the parent set is the finite set of all vertices having a directed edge into that vertex. |
| `DAG.children` | `V → Finset V` | For a finite directed acyclic graph on a vertex population and a vertex, the child set is the finite set of all vertices to which that vertex has a directed edge. |
| `DAG.mem_parents` | `u ∈ G.parents v ↔ G.edge u v` | Membership characterization for `parents`: `u ∈ G.parents v ↔ G.edge u v`. |
| `DAG.mem_children` | `w ∈ G.children v ↔ G.edge v w` | Membership characterization for `children`: `w ∈ G.children v ↔ G.edge v w`. |
| `DAG.isAncestor` | `V → V → Prop` | For a finite vertex population with decidable equality and a directed acyclic graph on that population, the ancestor relation holds from one vertex to another exactly when there is a directed path from the former to the latter. It is established either by a directed edge from the former vertex to the latter or by an existing ancestor path followed by a directed edge. |
| `DAG.isAncestor_iff_transGen` | `G.isAncestor u v ↔ Relation.TransGen G.edge u v` | The inductive ancestor relation coincides with `Relation.TransGen` of the edge relation: both are the transitive closure of the edge relation. |
| `DAG.irrefl` | `¬G.edge v v` | No vertex has an edge to itself (a directed self-loop would be a length-one cycle). |
| `DAG.asymm` | `G.edge u v → ¬G.edge v u` | If there is an edge from `u` to `v`, then there is no edge from `v` to `u` (a two-cycle is forbidden by acyclicity). |
| `DAG.isAncestor_irrefl` | `¬G.isAncestor v v` | Ancestor relation is irreflexive: no vertex is its own ancestor (this is acyclicity, restated for the inductive ancestor relation). |
| `DAG.isAncestor_trans` | `G.isAncestor u v → G.isAncestor v w → G.isAncestor u w` | Ancestor relation is transitive. |
| `DAG.isAncestor_child` | `G.isAncestor u v → G.edge u v ∨ ∃ c, G.edge u c ∧ G.isAncestor c v` | First-step decomposition: if `u` is an ancestor of `v`, then either `edge u v` or there exists a child `c` of `u` such that `c` is an ancestor of `v`. |
| `DAG.isDescendant` | `V → V → Prop` | For a finite directed acyclic graph on a vertex population and two vertices, the first and the second, the descendant relation holds precisely when there is a directed path from the second vertex to the first. |
| `DAG.ancStep` | `Finset V → Finset V` | For a finite directed acyclic graph on a vertex population and a finite vertex set, one backward ancestor-expansion step returns that set together with every parent of every member of the set. |
| `DAG.ancClosure` | `V → Finset V` | For a finite directed acyclic graph on a vertex population and a vertex, the strict-ancestor set is obtained by starting with the vertex’s parents and applying backward ancestor expansion once for each vertex in the population. |
| `DAG.subset_iterate_ancStep` | `S ⊆ G.ancStep^[k] S` | Any finite set of graph nodes remains contained after applying the graph's ancestor-step operation any number of times. |
| `DAG.le_card_iterate` | `(∀ j < k, (f^[j] S₀).card < (f^[j + 1] S₀).card) → (f^[0] S₀).card + k ≤ (f^[k] S₀).card` | If each of a specified number of successive applications of a function on finite sets strictly increases cardinality, the final set has grown by at least that number. |
| `DAG.ancClosure_closed` | `x ∈ G.ancClosure v → G.parents x ⊆ G.ancClosure v` | Every parent of a vertex in its computed ancestor set also belongs to that ancestor set. |
| `DAG.isAncestor_mem_of_closed` | `(∀ x ∈ T, G.parents x ⊆ T) → ∀ {u w : V}, G.isAncestor u w → w ∈ T → u ∈ T` | A finite set that contains every parent of each of its vertices contains every ancestor of each vertex it contains. |
| `DAG.mem_ancClosure` | `u ∈ G.ancClosure v ↔ G.isAncestor u v` | Membership in the backward-reachability fixpoint is exactly ancestry: a vertex lies in `G.ancClosure v` iff it is an ancestor of `v`. This makes the ancestor relation decidable using only the (decidable) edge relation, with no reference to any topological order. |
| `DAG.decIsAncestor` | `(G : Causalean.DAG V) → DecidableRel G.isAncestor` | For a finite vertex population with decidable equality and a directed acyclic graph on that population, the decision procedure for the ancestor relation determines, for every ordered pair of vertices, whether the first is an ancestor of the second. |
| `DAG.ancestors` | `V → Finset V` | For a finite directed acyclic graph on a vertex population and a vertex, the ancestor set is the finite set of all vertices from which a directed path reaches that vertex. |
| `DAG.descendants` | `V → Finset V` | For a finite directed acyclic graph on a vertex population and a vertex, the descendant set is the finite set of all vertices reachable from that vertex by a directed path. |
| `DAG.mem_ancestors` | `u ∈ G.ancestors v ↔ G.isAncestor u v` | Membership characterization for `ancestors`: `u ∈ G.ancestors v ↔ G.isAncestor u v`. |
| `DAG.mem_descendants` | `w ∈ G.descendants v ↔ G.isAncestor v w` | Membership characterization for `descendants`: `w ∈ G.descendants v ↔ G.isAncestor v w`. |
| `DAG.parents_subset_ancestors` | `G.parents v ⊆ G.ancestors v` | Parents are a subset of ancestors. |
| `DAG.children_subset_descendants` | `G.children v ⊆ G.descendants v` | Children are a subset of descendants. |
| `DAG.ancestorsSet` | `Finset V → Finset V` | For a finite directed acyclic graph on a vertex population and a finite vertex set, the set of its strict ancestors contains exactly the vertices from which a directed path reaches at least one member of the given set. |
| `DAG.ancestralSet` | `Finset V → Finset V` | For a finite directed acyclic graph on a vertex population and a finite vertex set, its ancestral closure is that set together with every vertex from which a directed path reaches one of its members. |
| `DAG.descendantsSet` | `Finset V → Finset V` | For a finite directed acyclic graph on a vertex population and a finite vertex set, the set of its strict descendants contains exactly the vertices reachable by a directed path from at least one member of the given set. |
| `DAG.nonDescendants` | `V → Finset V` | For a finite directed acyclic graph on a vertex population and a vertex, the non-descendant set contains exactly the vertices other than that vertex which cannot be reached from it by a directed path. |
| `DAG.ancestorRank` | `V → ℕ` | For a finite directed acyclic graph on a vertex population and a vertex, its ancestor rank is the number of that vertex’s strict ancestors. |
| `DAG.ancestorRank_lt_of_edge` | `G.edge a b → G.ancestorRank a < G.ancestorRank b` | Along an edge the strict-ancestor count strictly increases. |
| `DAG.topoOrder` | `V → ℕ` | For a finite directed acyclic graph on a vertex population and a vertex, the derived topological number is its number of strict ancestors times the population size, plus a fixed tie-breaking enumeration number. This number is injective across vertices and strictly increases along every directed edge. |
| `DAG.topoOrder_injective` | `Function.Injective G.topoOrder` | The derived topological order is injective, so it provides a canonical total order on the finite vertex type. |
| `DAG.topoOrder_lt` | `G.edge u v → G.topoOrder u < G.topoOrder v` | The derived topological order is edge-consistent: if there is an edge from `u` to `v`, then `topoOrder u < topoOrder v`. This witnesses acyclicity. |
| `DAG.isAncestor_topoOrder_lt` | `G.isAncestor u v → G.topoOrder u < G.topoOrder v` | Ancestors respect the topological order: if `u` is an ancestor of `v` then `G.topoOrder u < G.topoOrder v`, so ancestor pairs are strictly ordered by `topoOrder`. |
| `DAG.isRoot` | `V → Prop` | For a finite directed acyclic graph on a vertex population and a vertex, the root condition holds exactly when no directed edge enters that vertex. |
| `DAG.decIsRoot` | `(G : Causalean.DAG V) → (v : V) → Decidable (G.isRoot v)` | For a finite vertex population with decidable equality, a directed acyclic graph on that population, and a vertex, the decision procedure for the root condition determines whether no directed edge enters that vertex. |
| `DAG.roots` | `Finset V` | For a finite directed acyclic graph on a vertex population, the root set is the finite set of all vertices with no incoming directed edge. |
| `DAG.acyclic_of_topoOrder` | `(∀ (u v : V), e u v → r (τ u) (τ v)) → ∀ (v : V), ¬Relation.TransGen e v v` | Acyclicity from a topological ranking. Given an edge relation `e` on `V` and a ranking function `τ` into a type equipped with a transitive, irreflexive relation `r`, if `τ` strictly increases (with respect to `r`) along every edge of `e`, then `e` has no directed cycle: no vertex is reachable from itself via the transitive closure of `e`. |
| `DAG.isAncestor_has_parent` | `G.isAncestor u v → G.parents v ≠ ∅` | Every vertex reached by a nonempty directed path has an incoming edge, namely the final edge of that path. |
<!-- /GEN -->


## Mathlib/Algorithms/MonotoneWindowDeque — verified finite sliding-window maxima

This package provides a purely functional, rightmost-stable monotone deque for maximum queries on
a finite stream with nondecreasing contiguous window endpoints.  It exposes input schedules,
invariant-preserving updates, head/maximum correctness, exact event accounting, memory bounds, and
fixed-pass composition without any causal-model assumptions.

### Inputs and window enumeration

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Basic -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.Stream` | `Type u_1 → Type u_1` | A finite ordered stream of values in a type records its length and value at each natural-number index. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Window` | `ℕ → Type` | A contiguous half-open window in a stream of given length has a left endpoint no larger than its right endpoint, which does not exceed the stream length. |
| `Mathlib.Algorithms.MonotoneWindowDeque.ActiveAt` | `ℕ → ℕ → ℕ → Prop` | A left endpoint, a right endpoint, and an index determine whether the index is active in the half-open interval. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Active` | `ℕ → Prop` | A bounded window and an index determine whether the index is active in that window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Window.indices` | `List ℕ` | A bounded window determines its increasing list of active indices. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Window.indexFinset` | `Finset ℕ` | A bounded window determines its finite set of active indices. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Window.mem_indices_iff` | `i ∈ w.indices ↔ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active w i` | A bounded window has the same active indices in its list enumeration and in its active-window condition. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Window.mem_indexFinset_iff` | `i ∈ w.indexFinset ↔ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active w i` | A bounded window has the same active indices in its finite-set enumeration and in its active-window condition. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Window.card_indexFinset` | `w.indexFinset.card = w.right - w.left` | A bounded window has as many active indices as its width. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Window.indices_eq_nil_iff` | `w.indices = [] ↔ w.left = w.right` | A bounded window has an empty index list exactly when its two endpoints coincide. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Window.indexFinset_nonempty_iff` | `w.indexFinset.Nonempty ↔ w.left < w.right` | A bounded window has an active index exactly when its left endpoint is strictly below its right endpoint. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Schedule` | `ℕ → Type` | A finite schedule for a stream of given length contains bounded windows with nondecreasing left and right endpoints. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Schedule.steps` | `ℕ` | A finite schedule determines its number of scheduled windows. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Schedule.left_le_of_get_lt` | `i < j → (schedule.windows.get ⟨i, hi⟩).left ≤ (schedule.windows.get ⟨j, hj⟩).left` | A finite schedule, two valid schedule positions, and their strict order ensure that the earlier left endpoint is no larger. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Schedule.right_le_of_get_lt` | `i < j → (schedule.windows.get ⟨i, hi⟩).right ≤ (schedule.windows.get ⟨j, hj⟩).right` | A finite schedule, two valid schedule positions, and their strict order ensure that the earlier right endpoint is no larger. |
<!-- /GEN -->

### Deque kernel and invariant

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.Deque` | `Type` | A monotone deque is represented by its front-to-back list of natural-number indices. |
| `Mathlib.Algorithms.MonotoneWindowDeque.initialDeque` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque` | The initial deque is empty before any stream index enters. |
| `Mathlib.Algorithms.MonotoneWindowDeque.expireFront` | `ℕ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque` | A left endpoint and a deque determine the deque after front expiration. |
| `Mathlib.Algorithms.MonotoneWindowDeque.expiredFront` | `ℕ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → List ℕ` | A left endpoint and a deque determine the recorded front pops. |
| `Mathlib.Algorithms.MonotoneWindowDeque.pruneBack` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → ℕ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque` | A stream, a deque, and a new index determine the deque after rightmost-stable back pruning, which removes ties in favor of the newer index. |
| `Mathlib.Algorithms.MonotoneWindowDeque.prunedBack` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → ℕ → List ℕ` | A stream, a deque, and a new index determine the recorded back pops. |
| `Mathlib.Algorithms.MonotoneWindowDeque.push` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → ℕ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque` | A stream, a deque, and a new index determine the deque after one rightmost-stable insertion. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PushBatch` | `Type` | A batch insertion records its final deque, every pushed index, and every index removed from the back while processing the batch. |
| `Mathlib.Algorithms.MonotoneWindowDeque.pushAll` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → List ℕ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.PushBatch` | A stream determines the recorded batch insertion from an initial deque and a list of entering indices. |
| `Mathlib.Algorithms.MonotoneWindowDeque.ValidAt` | `ℕ → ℕ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → Prop` | A stream, two raw endpoints, and a deque satisfy the validity invariant when retained indices are active and ordered and omitted active indices are dominated. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Valid` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Window stream.length → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → Prop` | A stream, a bounded window, and a deque determine whether the deque is valid for that window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.initialDeque_validAt` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream 0 0 Causalean.Mathlib.Algorithms.MonotoneWindowDeque.initialDeque` | A stream has an empty initial deque satisfying the zero-width invariant. |
| `Mathlib.Algorithms.MonotoneWindowDeque.expiredFront_append_expireFront` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.expiredFront left q ++ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.expireFront left q = q` | A left endpoint and a deque have a reported front-pop prefix followed by the retained deque exactly equal to the original deque. |
| `Mathlib.Algorithms.MonotoneWindowDeque.pruneBack_append_prunedBack` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.pruneBack stream q i ++ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.prunedBack stream q i = q` | A stream, a deque, and a new index have a retained prefix and reported back-pop suffix exactly equal to the original deque. |
| `Mathlib.Algorithms.MonotoneWindowDeque.pruneBack_prefix` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.pruneBack stream q i <+: q` | A stream, a deque, and a new index ensure that back pruning retains a prefix of the old deque. |
| `Mathlib.Algorithms.MonotoneWindowDeque.pruneBack_index_ordered` | `List.Pairwise (fun x1 x2 => x1 < x2) q → List.Pairwise (fun x1 x2 => x1 < x2) (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.pruneBack stream q i)` | A stream, a new index, and strictly ordered old deque indices ensure that back pruning preserves strict index order. |
| `Mathlib.Algorithms.MonotoneWindowDeque.pruneBack_value_decreasing` | `List.Pairwise (fun j k => stream.value k < stream.value j) q → List.Pairwise (fun j k => stream.value k < stream.value j) (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.pruneBack stream q i)` | A stream, a new index, and strictly decreasing old deque values ensure that back pruning preserves strict value decrease. |
| `Mathlib.Algorithms.MonotoneWindowDeque.mem_push_iff` | `k ∈ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.push stream q i ↔ k ∈ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.pruneBack stream q i ∨ k = i` | A stream, a deque, a new index, and a queried index have the stated membership characterization after one push. |
| `Mathlib.Algorithms.MonotoneWindowDeque.push_index_ordered` | `List.Pairwise (fun x1 x2 => x1 < x2) q → (∀ j ∈ q, j < i) → List.Pairwise (fun x1 x2 => x1 < x2) (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.push stream q i)` | A stream, strictly ordered old deque indices, and all old indices being earlier than the new one ensure that one push preserves strict index order. |
| `Mathlib.Algorithms.MonotoneWindowDeque.push_value_decreasing` | `List.Pairwise (fun j k => stream.value k < stream.value j) q → List.Pairwise (fun j k => stream.value k < stream.value j) (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.push stream q i)` | A stream and strictly decreasing old deque values ensure that one rightmost-stable push leaves strictly decreasing values. |
| `Mathlib.Algorithms.MonotoneWindowDeque.mem_prunedBack_dominated` | `(∀ k ∈ q, k < i) → j ∈ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.prunedBack stream q i → j < i ∧ stream.value j ≤ stream.value i` | A stream, all old indices being earlier than the new index, and an index recorded as a back pop ensure that the popped index is earlier and no larger in value than the new index. |
| `Mathlib.Algorithms.MonotoneWindowDeque.ValidAt.nodup` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left right q → List.Nodup q` | A valid raw-window deque has no duplicate indices. |
<!-- /GEN -->

### Updates and preservation

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Update -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.StepTrace` | `Type` | A stream has a step record containing its before and after deques and exact push, front-pop, and back-pop event lists. |
| `Mathlib.Algorithms.MonotoneWindowDeque.update` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → ℕ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Window stream.length → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.StepTrace stream` | A stream, the prior right endpoint, a new bounded window, and the prior deque determine the recorded monotone-deque update, expiring the front before inserting newly entered active indices. |
| `Mathlib.Algorithms.MonotoneWindowDeque.update_pushed` | `(Causalean.Mathlib.Algorithms.MonotoneWindowDeque.update stream oldRight window q).pushed = List.range' (max oldRight window.left) (window.right - max oldRight window.left)` | A stream, a prior right endpoint, a new window, and a prior deque have an update push log equal to the newly entered active interval. |
| `Mathlib.Algorithms.MonotoneWindowDeque.expireFront_preserves` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream oldLeft oldRight q → oldLeft ≤ newLeft → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream newLeft oldRight (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.expireFront newLeft q)` | A valid old raw-window deque and a nondecreasing new left endpoint ensure that front expiration preserves the full raw-window invariant, including an empty intermediate interval. |
| `Mathlib.Algorithms.MonotoneWindowDeque.ValidAt.to_max_right` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left right q → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left (max right left) q` | A valid raw-window deque remains valid when its right endpoint is enlarged to at least its left endpoint. |
| `Mathlib.Algorithms.MonotoneWindowDeque.push_succ_preserves` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left right q → left ≤ right → right < stream.length → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left (right + 1) (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.push stream q right)` | A valid raw-window deque, a left endpoint no larger than the current right endpoint, and room for one more stream index ensure that pushing the right-boundary index preserves the invariant for the enlarged window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.pushAll_range_preserves` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left start q → left ≤ start → start + count ≤ stream.length → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left (start + count) (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.pushAll stream q (List.range' start count)).state` | A valid raw-window deque, a left endpoint no larger than the range start, and a range ending within the stream ensure that pushing the whole consecutive range preserves the invariant. |
| `Mathlib.Algorithms.MonotoneWindowDeque.pushAll_interval_preserves` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left oldRight q → oldRight ≤ newRight → newRight ≤ stream.length → left ≤ newRight → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left newRight (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.pushAll stream q (List.range' (max oldRight left) (newRight - max oldRight left))).state` | A valid deque after front expiration, a nondecreasing right endpoint, a new endpoint within the stream, and a valid new raw interval ensure that inserting newly entered active indices restores the invariant. |
| `Mathlib.Algorithms.MonotoneWindowDeque.update_preserves` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Valid stream oldWindow q → oldWindow.left ≤ newWindow.left → oldWindow.right ≤ newWindow.right → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Valid stream newWindow (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.update stream oldWindow.right newWindow q).after` | A valid old-window deque, a nondecreasing left endpoint, and a nondecreasing right endpoint ensure that one update produces a valid new-window deque. |
| `Mathlib.Algorithms.MonotoneWindowDeque.update_initial_preserves` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Valid stream window (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.update stream 0 window []).after` | A stream and its first bounded window ensure that updating from the empty initial interval produces a valid deque. |
<!-- /GEN -->

### Head correctness

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Correctness -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.windowValues` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Window stream.length → Finset α` | A stream and a bounded window determine the finite set of values observed in that window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.windowValues_nonempty` | `window.left < window.right → (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.windowValues stream window).Nonempty` | A stream, a bounded window, and strictly ordered window endpoints ensure that the window's finite value set is nonempty. |
| `Mathlib.Algorithms.MonotoneWindowDeque.windowMax` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → (window : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Window stream.length) → window.left < window.right → α` | A stream, a bounded window, and strictly ordered window endpoints determine the window maximum. |
| `Mathlib.Algorithms.MonotoneWindowDeque.ValidAt.head_argmax` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ValidAt stream left right q → left < right → right ≤ stream.length → ∃ head tail, q = head :: tail ∧ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ActiveAt left right head ∧ head < stream.length ∧ ∀ (i : ℕ), Causalean.Mathlib.Algorithms.MonotoneWindowDeque.ActiveAt left right i → i < stream.length → stream.value i ≤ stream.value head` | A valid raw-window deque, a nonempty raw interval, and a right endpoint within the stream ensure that the deque head is active and maximizes the stream value over that interval. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Valid.head_argmax` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Valid stream window q → window.left < window.right → ∃ head tail, q = head :: tail ∧ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active window head ∧ ∀ (i : ℕ), Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active window i → stream.value i ≤ stream.value head` | A valid bounded-window deque and a nonempty window ensure that its head is an active argmax. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Valid.head_value_eq_windowMax` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Valid stream window q → ∀ (hne : window.left < window.right), ∃ head tail, q = head :: tail ∧ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active window head ∧ stream.value head = Causalean.Mathlib.Algorithms.MonotoneWindowDeque.windowMax stream window hne ∧ ∀ (i : ℕ), Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active window i → stream.value i ≤ stream.value head` | A valid bounded-window deque and a nonempty window ensure that its head is an active argmax whose value equals the finite-window maximum. |
<!-- /GEN -->

### Schedule scans

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Scan -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.scanFrom` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → ℕ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Deque → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Window stream.length) → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.StepTrace stream)` | A stream determines the scan trace produced from a prior right endpoint, deque, and list of windows. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Schedule stream.length → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.StepTrace stream)` | A stream and a monotone window schedule determine the complete scan trace from the empty initial state. |
| `Mathlib.Algorithms.MonotoneWindowDeque.length_scan` | `(Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule).length = schedule.steps` | A stream and a monotone window schedule ensure that the scan has exactly one trace step for each scheduled window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_valid_at` | `∃ step, (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)[k]? = some step ∧ step.window = schedule.windows.get ⟨k, hk⟩ ∧ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Valid stream step.window step.after` | A stream, a monotone window schedule, and a valid schedule position ensure that the corresponding scan step has a valid deque for its window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_head_argmax` | `(schedule.windows.get ⟨k, hk⟩).left < (schedule.windows.get ⟨k, hk⟩).right → ∃ step head tail, (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)[k]? = some step ∧ step.window = schedule.windows.get ⟨k, hk⟩ ∧ step.after = head :: tail ∧ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active step.window head ∧ ∀ (i : ℕ), Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active step.window i → stream.value i ≤ stream.value head` | A stream, a monotone window schedule, a valid schedule position, and a nonempty window at that position ensure that the scan head is active and maximizes the stream value in that window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_head_value_eq_windowMax` | `∃ step head tail, (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)[k]? = some step ∧ step.window = schedule.windows.get ⟨k, hk⟩ ∧ step.after = head :: tail ∧ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active step.window head ∧ stream.value head = Causalean.Mathlib.Algorithms.MonotoneWindowDeque.windowMax stream (schedule.windows.get ⟨k, hk⟩) hne ∧ ∀ (i : ℕ), Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active step.window i → stream.value i ≤ stream.value head` | A stream, a monotone window schedule, a valid schedule position, and a nonempty window at that position ensure that the scan head is an active argmax whose value equals the finite-window maximum. |
<!-- /GEN -->

### Amortized accounting

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Accounting -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.TracePushed` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.StepTrace stream) → List ℕ` | A stream and a scan trace determine the aggregate push log. |
| `Mathlib.Algorithms.MonotoneWindowDeque.TraceFrontPopped` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.StepTrace stream) → List ℕ` | A stream and a scan trace determine the aggregate front-pop log. |
| `Mathlib.Algorithms.MonotoneWindowDeque.TraceBackPopped` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.StepTrace stream) → List ℕ` | A stream and a scan trace determine the aggregate back-pop log. |
| `Mathlib.Algorithms.MonotoneWindowDeque.dequeOperations` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.StepTrace stream) → ℕ` | A stream and a scan trace determine the total number of deque mutations. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scanCost` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Schedule stream.length → ℕ` | A stream and a monotone window schedule determine the scan cost, including one bookkeeping unit per window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.peakStored` | `(stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α) → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.StepTrace stream) → ℕ` | A stream and a scan trace determine the peak stored deque size. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_push_count_le_one` | `List.count i (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TracePushed stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)) ≤ 1` | A stream, a monotone window schedule, and an index ensure that the index is pushed at most once in the aggregate scan log. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_front_pop_count_le_one` | `List.count i (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TraceFrontPopped stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)) ≤ 1` | A stream, a monotone window schedule, and an index ensure that the index is front-popped at most once in the aggregate scan log. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_back_pop_count_le_one` | `List.count i (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TraceBackPopped stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)) ≤ 1` | A stream, a monotone window schedule, and an index ensure that the index is back-popped at most once in the aggregate scan log. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_pop_logs_disjoint` | `(Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TraceFrontPopped stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)).Disjoint (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TraceBackPopped stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule))` | A stream and a monotone window schedule ensure that no index appears in both front-pop and back-pop logs. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_popped_was_pushed` | `i ∈ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TraceFrontPopped stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule) ∨ i ∈ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TraceBackPopped stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule) → i ∈ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TracePushed stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)` | A stream, a monotone window schedule, and an index recorded as a front or back pop ensure that the index was previously pushed. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_total_pops_le_pushes` | `(Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TraceFrontPopped stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)).length + (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TraceBackPopped stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)).length ≤ (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TracePushed stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)).length` | A stream and a monotone window schedule ensure that total front and back pops are no more numerous than total pushes. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_total_pushes_le_length` | `(Causalean.Mathlib.Algorithms.MonotoneWindowDeque.TracePushed stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)).length ≤ stream.length` | A stream and a monotone window schedule ensure that total pushes are at most the stream length. |
| `Mathlib.Algorithms.MonotoneWindowDeque.dequeOperations_le_two_mul_length` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.dequeOperations stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule) ≤ 2 * stream.length` | A stream and a monotone window schedule ensure that total deque mutations are at most twice the stream length. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scanCost_le` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scanCost stream schedule ≤ 2 * stream.length + schedule.steps` | A stream and a monotone window schedule ensure that scan cost is at most twice stream length plus the number of scheduled windows. |
| `Mathlib.Algorithms.MonotoneWindowDeque.Valid.length_le_windowWidth` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Valid stream window q → List.length q ≤ window.right - window.left` | A valid bounded-window deque has stored length at most its window width. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_memory_le_windowWidth` | `∃ step, (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule)[k]? = some step ∧ List.length step.after ≤ (schedule.windows.get ⟨k, hk⟩).right - (schedule.windows.get ⟨k, hk⟩).left` | A stream, a monotone window schedule, and a valid schedule position ensure that the corresponding scan state stores no more indices than its window width. |
| `Mathlib.Algorithms.MonotoneWindowDeque.peakStored_le_length` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.peakStored stream (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream schedule) ≤ stream.length` | A stream and a monotone window schedule ensure that peak deque storage is at most the stream length. |
<!-- /GEN -->

### Constantly many passes

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Passes -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.FixedPasses` | `ℕ → Type` | A stream and a finite pass count have a family of monotone-window schedules, one for each pass. |
| `Mathlib.Algorithms.MonotoneWindowDeque.FixedPasses.totalCost` | `ℕ` | A fixed family of passes determines the sum of its individual scan costs. |
| `Mathlib.Algorithms.MonotoneWindowDeque.FixedPasses.totalSteps` | `ℕ` | A fixed family of passes determines its total number of scheduled windows. |
| `Mathlib.Algorithms.MonotoneWindowDeque.FixedPasses.head_value_eq_windowMax` | `∃ step head tail, (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream (family.schedule p))[k]? = some step ∧ step.window = (family.schedule p).windows.get ⟨k, hk⟩ ∧ step.after = head :: tail ∧ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active step.window head ∧ stream.value head = Causalean.Mathlib.Algorithms.MonotoneWindowDeque.windowMax stream ((family.schedule p).windows.get ⟨k, hk⟩) hne ∧ ∀ (i : ℕ), Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active step.window i → stream.value i ≤ stream.value head` | A fixed family of passes, a selected pass, a valid position in that pass, and a nonempty window there ensure that the scan head is an active argmax with the finite-window maximum value. |
| `Mathlib.Algorithms.MonotoneWindowDeque.FixedPasses.totalCost_le` | `family.totalCost ≤ 2 * passes * stream.length + family.totalSteps` | A fixed family of passes ensures that its total cost is at most twice the pass count times stream length plus its total scheduled-window count. |
| `Mathlib.Algorithms.MonotoneWindowDeque.FixedPasses.memory_le_windowWidth` | `∃ step, (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan stream (family.schedule p))[k]? = some step ∧ List.length step.after ≤ ((family.schedule p).windows.get ⟨k, hk⟩).right - ((family.schedule p).windows.get ⟨k, hk⟩).left` | A fixed family of passes, a selected pass, and a valid position in that pass ensure that the corresponding state stores no more than its window width. |
<!-- /GEN -->

### Raw-key predicate schedules

These modules compile prefix-shaped entry and suffix-shaped stay predicates on sparse raw keys to
the position windows used by the verified deque. They also give a raw-key execution trace equal to
the position-level scan and transfer argmax and resource guarantees to that trace.

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.PredicateSchedule -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule` | `List ι → List κ → Type (max u_1 u_2)` | A sparse raw-key list and an ordered step list determine a predicate window specification whose entry predicate, stay predicate, entry-prefix law, stay-suffix law, entry monotonicity across steps, and stay antitonicity across steps describe a monotone active window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.entryTest` | `κ → ι → Bool` | A predicate schedule, a step, and a raw key determine the Boolean entry test used by executable list operations. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.expiredTest` | `κ → ι → Bool` | A predicate schedule, a step, and a raw key determine the Boolean test that the key has expired. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.entered` | `κ → List ι` | A predicate schedule and a step determine the raw prefix that has entered by that step. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.rightEndpoint` | `κ → ℕ` | A predicate schedule and a step determine the right position endpoint, namely the length of the entered raw-key prefix. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.expiredPrefix` | `κ → List ι` | A predicate schedule and a step determine the expired prefix of entered keys, namely the initial segment that no longer satisfies the stay predicate. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.leftEndpoint` | `κ → ℕ` | A predicate schedule and a step determine the left position endpoint, namely the length of the expired prefix among entered keys. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.rightEndpoint_le_length` | `P.rightEndpoint s ≤ keys.length` | A predicate schedule has every right endpoint bounded by the raw-key count. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.leftEndpoint_le_rightEndpoint` | `P.leftEndpoint s ≤ P.rightEndpoint s` | A predicate schedule has every left endpoint bounded by its right endpoint. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.windowAt` | `κ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Window keys.length` | A predicate schedule and a step determine a bounded half-open position window, including when the raw-key list or the active window is empty. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.take_rightEndpoint_eq_entered` | `List.take (P.rightEndpoint s) keys = P.entered s` | A predicate schedule has its right prefix exactly equal to the `takeWhile` entry segment. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.take_leftEndpoint_eq_expiredPrefix` | `List.take (P.leftEndpoint s) (List.take (P.rightEndpoint s) keys) = P.expiredPrefix s` | A predicate schedule has its left prefix exactly equal to the `takeWhile` segment of entered keys that fail the stay predicate. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.drop_leftEndpoint_eq_dropWhile` | `List.drop (P.leftEndpoint s) (List.take (P.rightEndpoint s) keys) = List.dropWhile (P.expiredTest s) (List.take (P.rightEndpoint s) keys)` | A predicate schedule has the keys between its endpoints exactly equal to dropping the non-staying prefix from the entered prefix. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.active_windowAt_iff` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active (P.windowAt s) i ↔ P.entry s (keys.get ⟨i, hi⟩) ∧ P.stay s (keys.get ⟨i, hi⟩)` | A predicate schedule, a step, and an in-bounds position satisfy the exact equivalence between position activity and the raw entry-and-stay predicates. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.rightEndpoint_mono_of_entry` | `(∀ x ∈ keys, P.entry s x → P.entry t x) → P.rightEndpoint s ≤ P.rightEndpoint t` | Predicate inclusion from an earlier step to a later step makes right endpoints nondecreasing. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.leftEndpoint_mono_of_predicates` | `(∀ x ∈ keys, P.entry s x → P.entry t x) → (∀ x ∈ keys, P.stay t x → P.stay s x) → P.leftEndpoint s ≤ P.leftEndpoint t` | Expanding entry and shrinking stay from one step to another make left endpoints nondecreasing. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.newlyEntering_eq_drop_entered` | `(∀ x ∈ keys, P.entry s x → P.entry t x) → List.takeWhile (P.entryTest t) (List.drop (P.rightEndpoint s) keys) = List.drop (P.rightEndpoint s) (P.entered t)` | A predicate schedule, an earlier step, a later step, and entry inclusion have newly entered raw keys exactly equal to the later entered prefix after dropping the earlier right endpoint. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.rightEndpoint_eq_add_newlyEntering` | `(∀ x ∈ keys, P.entry s x → P.entry t x) → P.rightEndpoint t = P.rightEndpoint s + (List.takeWhile (P.entryTest t) (List.drop (P.rightEndpoint s) keys)).length` | A predicate schedule, an earlier step, a later step, and entry inclusion have later right endpoint equal to the earlier endpoint plus the exact `takeWhile` entering-segment length. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.newlyExpired_eq_takeWhile` | `(∀ x ∈ keys, P.entry s x → P.entry t x) → (∀ x ∈ keys, P.stay t x → P.stay s x) → List.take (P.leftEndpoint t - P.leftEndpoint s) (List.drop (P.leftEndpoint s) (List.take (P.rightEndpoint t) keys)) = List.takeWhile (P.expiredTest t) (List.drop (P.leftEndpoint s) (List.take (P.rightEndpoint t) keys))` | A predicate schedule, an earlier step, a later step, entry expansion, and stay shrinkage have the keys crossing the left endpoint exactly equal to the `takeWhile` non-staying segment. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.leftEndpoint_eq_add_newlyExpired` | `(∀ x ∈ keys, P.entry s x → P.entry t x) → (∀ x ∈ keys, P.stay t x → P.stay s x) → P.leftEndpoint t = P.leftEndpoint s + (List.takeWhile (P.expiredTest t) (List.drop (P.leftEndpoint s) (List.take (P.rightEndpoint t) keys))).length` | A predicate schedule, an earlier step, a later step, entry expansion, and stay shrinkage have later left endpoint equal to the earlier endpoint plus the exact `takeWhile` expiration-segment length. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.schedule` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Schedule keys.length` | A predicate schedule compiles to the monotone bounded-window schedule over key positions. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.schedule_steps` | `P.schedule.steps = steps.length` | A predicate schedule compiles to one position window for each raw step. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.schedule_window_get` | `P.schedule.windows.get ⟨k, Eq.mpr (id (congrArg (LT.lt k) (List.length_map P.windowAt))) hk⟩ = P.windowAt (steps.get ⟨k, hk⟩)` | A predicate schedule and a valid step-list position compile the window at that position to the endpoints of the corresponding raw step. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.active_schedule_iff` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Active (P.schedule.windows.get ⟨k, Eq.mpr (id (congrArg (LT.lt k) (List.length_map P.windowAt))) hk⟩) i ↔ P.entry (steps.get ⟨k, hk⟩) (keys.get ⟨i, hi⟩) ∧ P.stay (steps.get ⟨k, hk⟩) (keys.get ⟨i, hi⟩)` | A predicate schedule, a valid step position, and an in-bounds key position characterize activity in the compiled scheduled window by the raw predicates. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.rightEndpoint_le_of_step_lt` | `i < j → P.rightEndpoint (steps.get ⟨i, hi⟩) ≤ P.rightEndpoint (steps.get ⟨j, hj⟩)` | A predicate schedule, two valid step positions, and their strict order ensure the earlier compiled right endpoint is no larger. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.leftEndpoint_le_of_step_lt` | `i < j → P.leftEndpoint (steps.get ⟨i, hi⟩) ≤ P.leftEndpoint (steps.get ⟨j, hj⟩)` | A predicate schedule, two valid step positions, and their strict order ensure the earlier compiled left endpoint is no larger. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.windowAt_empty` | `(P.windowAt s).left = 0 ∧ (P.windowAt s).right = 0` | A predicate schedule over an empty raw-key list has both endpoints equal to zero at every step. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.PredicateRawScan -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.keyedStream` | `List ι → (ι → α) → α → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α` | A raw-key list, a raw-key score, and an out-of-bounds fallback score determine the total position stream used by the generic deque. The fallback is never observed at a valid position. |
| `Mathlib.Algorithms.MonotoneWindowDeque.positionsToKeys` | `List ι → List ℕ → List ι` | A raw-key list and a list of natural positions determine the raw keys obtained by safe lookup of every in-bounds position. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawPruneBack` | `(ι → α) → List ι → ι → List ι` | A raw score, a raw deque, and a new key determine the deque prefix after deleting its suffix of scores no larger than the new score. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawPrunedBack` | `(ι → α) → List ι → ι → List ι` | A raw score, a raw deque, and a new key determine the keys removed from the back by the deterministic rightmost-stable tie policy. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawPush` | `(ι → α) → List ι → ι → List ι` | A raw score, a raw deque, and a new key determine one rightmost-stable monotone push; equal old scores are removed in favor of the new key. |
| `Mathlib.Algorithms.MonotoneWindowDeque.RawPushBatch` | `Type u_4 → Type u_4` | A raw-key type determines a batch record with the final key deque, the pushed keys, and the keys removed from the back. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawPushAll` | `(ι → α) → List ι → List ι → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawPushBatch ι` | A raw score determines the recorded batch of rightmost-stable pushes, given by leaving an empty input list unchanged and pushing the first key before recursing on the remainder. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawPush_getLast?_eq` | `(Causalean.Mathlib.Algorithms.MonotoneWindowDeque.rawPush score q x).getLast? = some x` | One raw rightmost-stable push has the newly pushed key as its final element, including when all old entries tie with it. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawPrunedBack_score_le` | `y ∈ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.rawPrunedBack score q x → score y ≤ score x` | A key removed by rightmost-stable back pruning has score no larger than the newly pushed key, so equal-score ties deterministically favor the newer occurrence. |
| `Mathlib.Algorithms.MonotoneWindowDeque.RawState` | `Type u_4 → Type u_4` | A raw-key type determines a predicate-scan state with the unentered suffix and the current raw-key deque. |
| `Mathlib.Algorithms.MonotoneWindowDeque.RawDequeTrace` | `Type u_4 → Type u_4` | A raw-key type determines a deque-update trace with the deque before updating, the deque after expiration, the final deque, the pushed keys, the front-popped keys, and the back-popped keys. |
| `Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace` | `Type u_4 → Type u_5 → Type (max u_4 u_5)` | A raw-key type and a step type determine a predicate-scan step record that extends a deque update with the current step, the pending suffix before updating, the pending suffix afterward, and the complete entered prefix before expiration filtering. |
| `Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace.dequeTrace` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawDequeTrace ι` | A raw predicate step trace determines its exact generic-shaped deque trace. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.rawUpdate` | `(ι → α) → κ → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawState ι → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace ι κ` | A predicate schedule, a raw score, a step, and a raw state determine the next recorded raw-key update. It advances entry by `takeWhile`, removes the non-staying prefixes by `dropWhile`, and pushes precisely the surviving new suffix. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.rawScanFrom` | `(ι → α) → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawState ι → List κ → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace ι κ)` | A predicate schedule and a raw score determine the raw trace obtained by folding over a supplied suffix of steps from a supplied state. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.rawScan` | `(ι → α) → List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace ι κ)` | A predicate schedule and a raw score determine the complete raw-key scan from all keys pending and an empty deque. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.length_rawScan` | `(P.rawScan score).length = steps.length` | A predicate schedule and a raw score produce one raw trace entry per step. |
| `Mathlib.Algorithms.MonotoneWindowDeque.mapStepTrace` | `List ι → {stream : Causalean.Mathlib.Algorithms.MonotoneWindowDeque.Stream α} → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.StepTrace stream → Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawDequeTrace ι` | A raw-key list maps one generic position-level step to the exact raw-key deque trace by safe lookup in every list-valued field. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_predicateSchedule_state_eq` | `List.map (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.mapStepTrace keys) (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.keyedStream keys score fallback) P.schedule) = List.map Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace.dequeTrace (P.rawScan score)` | A predicate schedule, a raw-key score, and a fallback score have the generic position scan mapped through raw-key lookup exactly equal to the corresponding raw-key predicate scan, including every deque state and push/pop log. |
| `Mathlib.Algorithms.MonotoneWindowDeque.scan_predicateSchedule_after_eq` | `k < steps.length → ∃ generic raw, (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.keyedStream keys score fallback) P.schedule)[k]? = some generic ∧ (P.rawScan score)[k]? = some raw ∧ Causalean.Mathlib.Algorithms.MonotoneWindowDeque.positionsToKeys keys generic.after = raw.after` | A predicate schedule, a raw score, a valid step position, and a fallback score have the generic deque after that step mapped through key lookup equal to the raw predicate-scan deque. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque.PredicateAccounting -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Algorithms.MonotoneWindowDeque.rawTracePushed` | `List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace ι κ) → List ι` | A raw predicate-scan trace determines the aggregate list of pushed raw keys. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawTraceFrontPopped` | `List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace ι κ) → List ι` | A raw predicate-scan trace determines the aggregate list of front-popped raw keys. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawTraceBackPopped` | `List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace ι κ) → List ι` | A raw predicate-scan trace determines the aggregate list of back-popped raw keys. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawDequeOperations` | `List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace ι κ) → ℕ` | A raw predicate-scan trace determines its exact number of deque mutations. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicateWindowSchedule.rawScanCost` | `(ι → α) → ℕ` | A predicate schedule and a raw score determine the raw scan cost, including one bookkeeping unit per step. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawPeakStored` | `List (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.RawStepTrace ι κ) → ℕ` | A raw predicate-scan trace determines the largest raw deque length reached. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawScanCost_eq_scanCost` | `P.rawScanCost score = Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scanCost (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.keyedStream keys score fallback) P.schedule` | A predicate schedule, a raw score, and a fallback score have raw operation cost exactly equal to the generic compiled position-scan cost. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawPeakStored_eq_peakStored` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.rawPeakStored (P.rawScan score) = Causalean.Mathlib.Algorithms.MonotoneWindowDeque.peakStored (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.keyedStream keys score fallback) (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.scan (Causalean.Mathlib.Algorithms.MonotoneWindowDeque.keyedStream keys score fallback) P.schedule)` | A predicate schedule, a raw score, and a fallback score have raw peak storage exactly equal to generic compiled position-scan peak storage. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawScanCost_le` | `P.rawScanCost score ≤ 2 * keys.length + steps.length` | A predicate schedule, a raw score, and a fallback score ensure raw scan cost is at most twice the number of sparse keys plus the number of steps. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawPeakStored_le_length` | `Causalean.Mathlib.Algorithms.MonotoneWindowDeque.rawPeakStored (P.rawScan score) ≤ keys.length` | A predicate schedule, a raw score, and a fallback score ensure raw peak deque storage is at most the number of sparse keys. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawScan_memory_le_windowWidth` | `∃ trace, (P.rawScan score)[k]? = some trace ∧ trace.after.length ≤ P.rightEndpoint (steps.get ⟨k, hk⟩) - P.leftEndpoint (steps.get ⟨k, hk⟩)` | A predicate schedule, a raw score, a fallback score, and a valid step position ensure the raw deque stored there is no wider than its compiled window. |
| `Mathlib.Algorithms.MonotoneWindowDeque.rawScan_head_argmax` | `(∃ i, P.entry (steps.get ⟨k, hk⟩) (keys.get i) ∧ P.stay (steps.get ⟨k, hk⟩) (keys.get i)) → ∃ trace head tail headPos, (P.rawScan score)[k]? = some trace ∧ trace.step = steps.get ⟨k, hk⟩ ∧ trace.after = head :: tail ∧ head = keys.get headPos ∧ P.entry (steps.get ⟨k, hk⟩) head ∧ P.stay (steps.get ⟨k, hk⟩) head ∧ (∀ (i : Fin keys.length), P.entry (steps.get ⟨k, hk⟩) (keys.get i) → P.stay (steps.get ⟨k, hk⟩) (keys.get i) → score (keys.get i) ≤ score head) ∧ ∀ (i : Fin keys.length), P.entry (steps.get ⟨k, hk⟩) (keys.get i) → P.stay (steps.get ⟨k, hk⟩) (keys.get i) → score (keys.get i) = score head → ↑i ≤ ↑headPos` | A predicate schedule, a raw score, a fallback score, a valid step position, and a nonempty raw predicate window ensure the raw deque head is an active score maximizer, with equal maxima resolved at the greatest key position. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicatePasses` | `List ι → List κ → ℕ → Type (max u_1 u_2)` | A raw-key list, a step list, and a finite pass count determine a pass family with one predicate-window schedule per pass. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicatePasses.totalRawCost` | `(ι → α) → ℕ` | A fixed predicate-pass family and a raw score determine the sum of the raw costs of all passes. |
| `Mathlib.Algorithms.MonotoneWindowDeque.PredicatePasses.totalRawCost_le` | `family.totalRawCost score ≤ 2 * passes * keys.length + passes * steps.length` | A fixed predicate-pass family, a raw score, and a fallback score ensure total raw cost is at most twice pass count times key count plus pass count times step count. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque -->
_(no documented declarations in Causalean.Mathlib.Algorithms.MonotoneWindowDeque)_
<!-- /GEN -->

---

## 1a. `Graph/FiniteDensity/OrderedLocalMarkov/` — Ordered local Markov property

Finite-DAG density factorizations imply the ordered local-Markov property: a coordinate is conditionally independent of earlier nonparents once a set containing its parents is conditioned on. The modules separate topological-coordinate bookkeeping, the density-to-independence bridge, and the factorization theorem.

### `Coordinates.lean`

<!-- GEN:Causalean.Graph.FiniteDensity.OrderedLocalMarkov.Coordinates -->
| Decl | Signature | Description |
|---|---|---|
| `Graph.FiniteDensity.TopologicalRanking` | `Causalean.DAG V → Type u_1` | A finite DAG is equipped with a numeric position for each vertex, distinct positions for distinct vertices, and strictly increasing positions along every directed edge. |
| `Graph.FiniteDensity.canonicalTopologicalRanking` | `(G : Causalean.DAG V) → Causalean.Graph.FiniteDensity.TopologicalRanking G` | A finite DAG has the canonical topological ranking supplied by its DAG API. |
| `Graph.FiniteDensity.predecessors` | `V → Finset V` | A topological ranking and vertex determine the finite set of vertices strictly preceding that vertex. |
| `Graph.FiniteDensity.parents_subset_predecessors` | `G.parents i ⊆ Causalean.Graph.FiniteDensity.predecessors τ i` | A topological ranking places every parent of a vertex among its predecessors. |
| `Graph.FiniteDensity.not_mem_predecessors` | `i ∉ Causalean.Graph.FiniteDensity.predecessors τ i` | A vertex does not belong to its strict predecessor set. |
| `Graph.FiniteDensity.parentClosed_predecessors` | `Causalean.Graph.FiniteDensity.ParentClosed G (Causalean.Graph.FiniteDensity.predecessors τ i)` | The predecessor set of a vertex in a topologically ranked DAG contains all parents of each of its members. |
| `Graph.FiniteDensity.measurable_orderedCoordinate` | `Measurable fun x => x i` | Reading a single coordinate from a finite product is measurable. |
| `Graph.FiniteDensity.measurable_predecessorResidualProjection` | `Measurable (Causalean.Graph.FiniteDensity.coordinateProjection (Causalean.Graph.FiniteDensity.predecessors τ i \ A))` | Projecting onto the predecessors outside a conditioning set is measurable. |
| `Graph.FiniteDensity.coordinateConditioning_comap_le` | `MeasurableSpace.comap (Causalean.Graph.FiniteDensity.coordinateProjection A) inferInstance ≤ inferInstance` | The σ-algebra generated by projection onto a conditioning coordinate block is no finer than the ambient product σ-algebra. |
<!-- /GEN -->

### `Local.lean`

<!-- GEN:Causalean.Graph.FiniteDensity.OrderedLocalMarkov.Local -->
| Decl | Signature | Description |
|---|---|---|
| `Graph.FiniteDensity.Factorization.localMarkovParents_of_parentClosed` | `Causalean.Graph.FiniteDensity.ParentClosed G P → i ∉ P → ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (Causalean.Graph.FiniteDensity.coordinateProjection (G.parents i)) inferInstance) (Causalean.Graph.FiniteDensity.coordinateConditioning_comap_le (G.parents i)) (fun x => x i) (Causalean.Graph.FiniteDensity.coordinateProjection (P \ G.parents i)) B.observationalMeasure` | For a finite DAG density factorization, a parent-closed coordinate block, and a vertex omitted from that block, the vertex coordinate is conditionally independent of the block's non-parent coordinates given its parent coordinates. |
<!-- /GEN -->

### `Main.lean`

<!-- GEN:Causalean.Graph.FiniteDensity.OrderedLocalMarkov.Main -->
| Decl | Signature | Description |
|---|---|---|
| `Graph.FiniteDensity.Factorization.localMarkovSuperset_of_parentClosed` | `Causalean.Graph.FiniteDensity.ParentClosed G P → i ∉ P → A ⊆ P → G.parents i ⊆ A → ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (Causalean.Graph.FiniteDensity.coordinateProjection A) inferInstance) (Causalean.Graph.FiniteDensity.coordinateConditioning_comap_le A) (fun x => x i) (Causalean.Graph.FiniteDensity.coordinateProjection (P \ A)) B.observationalMeasure` | For a finite DAG density factorization, a parent-closed block omitting a vertex, and a conditioning subset of that block containing every parent, the vertex coordinate is conditionally independent of all remaining block coordinates given the chosen conditioning coordinates. |
| `Graph.FiniteDensity.Factorization.orderedLocalMarkov` | `∀ A ⊆ Causalean.Graph.FiniteDensity.predecessors τ i, G.parents i ⊆ A → ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (Causalean.Graph.FiniteDensity.coordinateProjection A) inferInstance) (Causalean.Graph.FiniteDensity.coordinateConditioning_comap_le A) (fun x => x i) (Causalean.Graph.FiniteDensity.coordinateProjection (Causalean.Graph.FiniteDensity.predecessors τ i \ A)) B.observationalMeasure` | For a finite DAG density factorization, an arbitrary topological ranking, a vertex, a conditioning predecessor set, and proof that it lies among the predecessors and contains every parent, the vertex coordinate is conditionally independent of all other predecessors given that set. |
| `Graph.FiniteDensity.Factorization.orderedLocalMarkov_canonical` | `∀ A ⊆ Causalean.Graph.FiniteDensity.predecessors (Causalean.Graph.FiniteDensity.canonicalTopologicalRanking G) i, G.parents i ⊆ A → ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (Causalean.Graph.FiniteDensity.coordinateProjection A) inferInstance) (Causalean.Graph.FiniteDensity.coordinateConditioning_comap_le A) (fun x => x i) (Causalean.Graph.FiniteDensity.coordinateProjection (Causalean.Graph.FiniteDensity.predecessors (Causalean.Graph.FiniteDensity.canonicalTopologicalRanking G) i \ A)) B.observationalMeasure` | For a finite DAG density factorization, a vertex, a conditioning set in the canonical predecessor block, and proof that it is a predecessor subset containing every parent, the vertex coordinate is conditionally independent of all other canonical predecessors given that set. |
| `Graph.FiniteDensity.UnitCubeFactorization.orderedLocalMarkov_unitCubeReference` | `∀ A ⊆ Causalean.Graph.FiniteDensity.predecessors τ i, G.parents i ⊆ A → ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (Causalean.Graph.FiniteDensity.coordinateProjection A) inferInstance) (Causalean.Graph.FiniteDensity.coordinateConditioning_comap_le A) (fun x => x i) (Causalean.Graph.FiniteDensity.coordinateProjection (Causalean.Graph.FiniteDensity.predecessors τ i \ A)) ((Causalean.Graph.FiniteDensity.unitCubeReference V).withDensity (Causalean.Graph.FiniteDensity.Factorization.observationalDensity B))` | For a unit-cube DAG density factorization, an arbitrary topological ranking, a vertex, a conditioning predecessor set, and proof that it lies among the predecessors and contains every parent, the vertex is conditionally independent of all remaining predecessors given that set under the unit-cube reference measure. |
<!-- /GEN -->

### `Mathlib/CondIndep/ThreeBlockDensity.lean`

The generic three-block density argument is collected with conditional-independence infrastructure because it is independent of DAGs and coordinates.

<!-- GEN:Causalean.Mathlib.CondIndep.ThreeBlockDensity -->
| Decl | Signature | Description |
|---|---|---|
| `condIndepFun_threeBlock_of_density_factors` | `Measurable d → ∀ [inst_9 : MeasureTheory.IsFiniteMeasure ((muY.prod (muZ.prod muC)).withDensity d)] (a : Y × C → ENNReal) (b : Z × C → ENNReal), Measurable a → Measurable b → (d =ᵐ[muY.prod (muZ.prod muC)] fun q => a (q.1, q.2.2) * b (q.2.1, q.2.2)) → ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (fun q => q.2.2) inferInstance) (Measurable.comap_le (Measurable.comp measurable_snd measurable_snd)) (fun q => q.1) (fun q => q.2.1) ((muY.prod (muZ.prod muC)).withDensity d)` | For three coordinate reference measures, a measurable finite joint density, first and second block factors, measurability of those factors, and their almost-everywhere product representation, the first and second coordinate maps are conditionally independent given the third coordinate. |
<!-- /GEN -->

---

## 2. `Graph/DSep/` — d-Separation (Bayes Ball)

**Files:** `DSep/BayesBall.lean` (core BFS algorithm), `DSep/ActivePath.lean` (path correctness), `DSep/Separation.lean` (dSep definition + structural lemmas), `DSep/Ancestral.lean` (ancestral reduction), `DSep/InduceTransport.lean` (induced-SWIG d-separation transport), `DSep/BackdoorBridges.lean` (ID theorem helpers).

### Bayes Ball internals

| Definition | Signature | Description |
|---|---|---|
| `DAG.BBDir` | `inductive` | `.fromParent` or `.fromChild` |
| `DAG.BBState V` | `V × BBDir` | A vertex with arrival direction |
| `DAG.bbZAncestors` | `(Z : Finset V) → Finset V` | `Z` ∪ ancestors of `Z` (for collider activation) |
| `DAG.bbStep` | `(Z : Finset V) → BBState V → Finset (BBState V)` | One Bayes Ball transition step |
| `DAG.bbReachable` | `(Z X : Finset V) → Finset (BBState V)` | Fixed-point BFS from `X` given `Z` |
| `DAG.bbReachableVertices` | `(Z X : Finset V) → Finset V` | Projection to vertices |

### Monotonicity

| Theorem | Signature | Description |
|---|---|---|
| `DAG.bbReachable_mono_source` | `X' ⊆ X → bbReachable Z X' ⊆ bbReachable Z X` | BFS reachability monotone in source (proven) |
| `DAG.bbReachableVertices_mono_source` | `X' ⊆ X → bbReachableVertices Z X' ⊆ bbReachableVertices Z X` | Vertex reachability monotone in source (proven) |
| `DAG.bbReachableVertices_iff_activePath` | `v ∈ bbReachableVertices Z X ↔ ∃ x ∈ X, ∃ p, p.length ≥ 2 ∧ IsActivePath Z p ∧ p.head? = some x ∧ p.getLast? = some v` | Bayes Ball reachability is equivalent to existence of an active path from the source set | **Proved** |
| `DAG.dSep_subset_left` | `X' ⊆ X → dSep X Y Z → dSep X' Y Z` | d-separation monotone in the source set | **Proved** |
| `DAG.bbZAncestors_union_eq` | `bbZAncestors (Z ∪ S) = bbZAncestors Z ∪ bbZAncestors S` | Ancestral set distributes over union (used to split collider-activation witnesses) | **Proved** |
| `DAG.activePath_transfer_cond_to_source` | active path from `x ∈ X` to `w` given `Z ∪ S` → active path from some `x' ∈ X ∪ S` to `w` given `Z` | Path-level surgery lemma underlying source-to-cond transfer; proof sketch in docstring (last-`S` suffix + directed detour at `S`-only-activated colliders) | **Proved** |
| `DAG.dSep_source_to_cond` | `dSep (X ∪ S) Y Z → dSep X Y (Z ∪ S)` | Moves a source set into the conditioning set in d-separation; reduces to `activePath_transfer_cond_to_source` via the BFS↔active-path equivalence | **Proved** |
| `DAG.dSep_mono_conditioningSet` | `(G' : DAG V) → (∀ u v, G'.edge u v → G.edge u v) → G.dSep X Y Z → G'.dSep X Y Z` | d-sep transfers from a supergraph `G` to any subgraph `G'`: fewer edges cannot create new active paths; used for backdoor / Rule 3 to move d-sep from `G(x)` to the split graph `G(x,z)` | **Proved** |
| `DAG.ancestralSet_idem` | `ancestralSet (ancestralSet S) = ancestralSet S` | Ancestral closure is idempotent; used to certify post-intervention ancestral query supports as ancestrally closed | **Proved** |
| `SWIGGraph.dSep_union_fixed_of_induce_dSep` | observed `X,Y,Z ⊆ R ∩ observed` + ancestral closure of `R` + d-sep in `G.induce R` → ambient d-sep given `Z ∪ fixed` | Transport bridge from an ancestral induced SWIG to the ambient SWIG after conditioning on fixed roots; isolates the fixed-node active-path bookkeeping needed by the Markov bridge | **Sorry** |

### d-Separation

| Definition | Signature | Description |
|---|---|---|
| `DAG.dSep` | `(X Y Z : Finset V) → Prop` | `Disjoint (bbReachableVertices Z X) Y` |
| `DAG.decDSep` | `Decidable (G.dSep X Y Z)` | Decidable instance |

**Usage (all decidable by `decide`):**

```lean
-- Z and Y are NOT d-separated by ∅ (active causal path)
example : ¬ivDAG.dSep {Z} {Y} ∅ := by decide

-- Conditioning on collider D opens the backdoor path
example : ¬ivDAG.dSep {Z} {Y} {D} := by decide

-- Conditioning on {D, U} blocks all paths
example : ivDAG.dSep {Z} {Y} {D, U} := by decide

-- Instrument independence: Z ⊥ U | ∅
example : ivDAG.dSep {Z} {U} ∅ := by decide
```

### Backdoor bridges — `Graph/DSep/BackdoorBridges.lean`

Graph-theoretic helpers consumed by `SCM/ID/Backdoor.lean`.

| Theorem | Signature | Description | Status |
|---|---|---|---|
| `DAG.dSep_union_roots_right` | `dSep X Y Z → (∀ r ∈ R, ∀ u, ¬ edge u r) → Disjoint R X → Disjoint R Y → dSep X Y (Z ∪ R)` | Adjoining root vertices (no incoming edges) to the conditioning set preserves d-separation; the Disjoint hypotheses are currently unused (retained for clarity of intent) | **Proved** |

---

## 3. `Graph/SWIG.lean` — SWIG Graph (Definition 4)

### SWIG Node Type

| Definition | Signature | Description |
|---|---|---|
| `SWIGNode` | `inductive` with `random` / `fixed` | Node-level split for each base variable |
| `swigΩ` | `(Ω : N → Type*) → SWIGNode N → Type _` | Shared value space for random/fixed versions |
| `iotaMap` | `SWIGNode N → SWIGNode N` | `fixed n ↦ random n` link map |

### SWIG DAG Construction

| Definition | Signature | Description |
|---|---|---|
| `swigEdge` | `DAG N → Finset N → SWIGNode N → SWIGNode N → Prop` | Edge rewiring under node-splitting |
| `swigTopo` | `DAG N → SWIGNode N → ℕ` | Interleaved topological order |
| `swigDAG` | `DAG N → Finset N → DAG (SWIGNode N)` | SWIG DAG constructor |
| `initialSWIG` | `DAG N → DAG (SWIGNode N)` | No-intervention SWIG (fixed nodes isolated) |

### Structure: `SWIGGraph N` (Definition 4)

A SWIG Graph `G = (S, V, U, E, ι)` — the graph-level causal structure with a three-way
partition and root constraints, factored out as its own structure and later extended
by `Causalean.SCM`.

| Field | Type | Description |
|---|---|---|
| `dag` | `DAG (SWIGNode N)` | The underlying SWIG DAG |
| `fixed` | `Finset (SWIGNode N)` | Fixed (intervention) nodes S |
| `observed` | `Finset (SWIGNode N)` | Observed (endogenous) random nodes V |
| `unobserved` | `Finset (SWIGNode N)` | Unobserved (exogenous) random nodes U |
| `fixed_is_fixed` | `∀ s ∈ fixed, ∃ n, s = SWIGNode.fixed n` | Shape invariant for fixed nodes |
| `observed_is_random` | `∀ v ∈ observed, ∃ n, v = SWIGNode.random n` | Shape invariant for observed nodes |
| `unobserved_is_random` | `∀ u ∈ unobserved, ∃ n, u = SWIGNode.random n` | Shape invariant for unobserved nodes |
| `obs_unobs_disjoint` | `Disjoint observed unobserved` | V and U are disjoint |
| `dag_edges_classified` | `∀ u v, dag.edge u v → u, v ∈ fixed ∪ observed ∪ unobserved` | Every edge endpoint is classified; preserved under `induce` (replaces the older `obs_unobs_cover_random`) |
| `fixed_image_in_observed` | `∀ s ∈ fixed, iotaMap s ∈ observed` | Graph-level image of ι lands in V |
| `fixed_are_roots` | `∀ s ∈ fixed, dag.parents s = ∅` | S are root nodes |
| `unobs_are_roots` | `∀ u ∈ unobserved, dag.parents u = ∅` | U are root nodes |
| `fixed_outside_fixed_isolated` | `∀ n, fixed n ∉ fixed → parents,children = ∅` | Non‑listed fixed nodes are isolated |
| `all_children_in_observed` | `∀ u ∈ U ∪ S ∪ V, children u ⊆ observed` | Children of non‑random nodes lie in V |

### Graph-level ι map

| Definition | Signature | Description |
|---|---|---|
| `SWIGGraph.iota` | `SWIGGraph N → {s // s ∈ fixed} → {v // v ∈ observed}` | Canonical ι : S → V built from `iotaMap` |
| `SWIGGraph.iotaNode` | `SWIGGraph N → {s // s ∈ fixed} → SWIGNode N` | Forgetful version of ι |
| `SWIGGraph.iotaN` | `SWIGGraph N → {n // fixed n ∈ fixed} → {n // random n ∈ observed}` | ι at the base type level |
| `SWIGGraph.isStandard` | `SWIGGraph N → Prop` | `fixed = ∅` (no interventions) |

---

## 3c. `Graph/SWIGSplitMono.lean` — Monolithic Multi-target Split (one-shot)

**Monolithic** multi-target split on a `SWIGGraph`.  Reroutes every
`.random D → w` edge (for `D ∈ X`) to `.fixed D → w` in a single pass rather
than by iterating a single-target split over `X.toList`.

**Why monolith…83229 tokens truncated…
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.valleePoussinMeanCLM` | `(n : ℕ) → 0 < n → C(AddCircle Real.pi, ℂ) →L[ℂ] ℂ` | For a positive integer order, the continuous-linear de la Vallée--Poussin mean maps a continuous complex-valued function on the circle of period π to twice its Fejér mean of order twice the given order, minus its Fejér mean of the given order. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.valleePoussinMean_fourier_nat` | `k ≤ n → (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.valleePoussinMeanCLM n hn) (fourier ↑k) = 1` | For a positive order and a frequency at most that order, the de la Vallée--Poussin mean preserves the nonnegative Fourier character. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.valleePoussinMean_fourier_neg_nat` | `k ≤ n → (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.valleePoussinMeanCLM n hn) (fourier (-↑k)) = 1` | For a positive order and a frequency magnitude at most that order, the de la Vallée--Poussin mean preserves the negative Fourier character. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctionalCLM` | `(n : ℕ) → 0 < n → C(AddCircle Real.pi, ℂ) →L[ℂ] ℂ` | For a positive integer order, the continuous-linear cusp functional maps a continuous complex-valued function on the circle of period π to its value at zero minus its de la Vallée--Poussin mean of that order. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctional_fourier_nat` | `k ≤ n → (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctionalCLM n hn) (fourier ↑k) = 0` | For a positive order and a nonnegative frequency at most that order, the cusp functional annihilates the Fourier character. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctional_fourier_neg_nat` | `k ≤ n → (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctionalCLM n hn) (fourier (-↑k)) = 0` | For a positive order and a negative frequency magnitude at most that order, the cusp functional annihilates the Fourier character. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctional_fourier_nat_nonneg` | `0 ≤ ((Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctionalCLM n hn) (fourier ↑k)).re` | For a positive order and a nonnegative frequency, the real part of the cusp multiplier is nonnegative. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctional_fourier_neg_nat_nonneg` | `0 ≤ ((Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctionalCLM n hn) (fourier (-↑k))).re` | For a positive order and a negative frequency magnitude, the real part of the cusp multiplier is nonnegative. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctional_fourier_nat_high` | `2 * n ≤ k → (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctionalCLM n hn) (fourier ↑k) = 1` | For a positive order and a nonnegative frequency at least twice that order, the cusp functional has multiplier one. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctional_fourier_neg_nat_high` | `2 * n ≤ k → (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctionalCLM n hn) (fourier (-↑k)) = 1` | For a positive order and a negative frequency magnitude at least twice that order, the cusp functional has multiplier one. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctional_norm_apply_le` | `‖(Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctionalCLM n hn) f‖ ≤ 4 * ‖f‖` | For a positive order and a continuous input, the cusp functional is bounded by four times the uniform norm. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fourier_pair_eq` | `(↑A - ↑B * Complex.I) / 2 * (fourier ↑k) ↑t + (↑A + ↑B * Complex.I) / 2 * (fourier (-↑k)) ↑t = ↑(A * Real.cos (2 * ↑k * t) + B * Real.sin (2 * ↑k * t))` | For two real coefficients, a frequency, and a circle coordinate, the conjugate Fourier pair equals the corresponding real sine--cosine mode. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.exists_fourierPoly_sinDouble` | `p.natDegree ≤ n → ∃ q, (∀ (t : ℝ), q ↑t = ↑(Polynomial.eval (Real.sin (2 * t)) p)) ∧ (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.cuspFunctionalCLM n hn) q = 0` | For a polynomial of degree at most a positive order, there is a corresponding Fourier polynomial that agrees after sine composition and is annihilated by the cusp functional. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.circleDouble` | `C(AddCircle Real.pi, AddCircle Real.pi)` | The circle-doubling map is the continuous map from the additive circle of period π to itself that sends each point to twice that point. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fourier_comp_circleDouble` | `(fourier j).comp Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.circleDouble = fourier (2 * j)` | For a Fourier frequency, composition with circle doubling doubles that frequency. |
<!-- /GEN -->

### Measure duality and prior projections

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Duality -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.IsSymmetric` | `MeasureTheory.Measure ℝ → Prop` | For a Borel measure on the real line, symmetry about zero means that reflecting every point through zero leaves the measure unchanged. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.IsSupportedOnUnitInterval` | `MeasureTheory.Measure ℝ → Prop` | For a measure on the real line, support on the unit interval means that the complement of the closed interval from −1 to 1 has measure zero. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.AbsExtremalDecomposition` | `ℕ → Type` | Extremal signed-measure data represented by its positive and negative parts. Each part has mass `1/2`, is symmetric and supported on `[-1,1]`; their degree-`K` moments agree, while their absolute first moments differ by `E_K`. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.exists_absExtremalDecomposition` | `Nonempty (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.AbsExtremalDecomposition K)` | For a polynomial degree limit, a normalized extremal signed-measure decomposition exists. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.AbsMomentMatchedPriors` | `ℕ → Type` | Two symmetric probability measures on `[-1,1]` whose moments match through degree `K` and whose absolute first moments have the oriented gap `2 E_K`. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.AbsExtremalDecomposition.toMomentMatchedPriors` | `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.AbsMomentMatchedPriors K` | For a nonnegative moment-degree limit and an absolute-value extremal decomposition at that limit, the associated pair of moment-matched priors has first prior equal to twice the decomposition's negative measure and second prior equal to twice its positive measure. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.exists_symmetric_momentMatched_absGap` | `0 < K → Even K → Nonempty (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.AbsMomentMatchedPriors K)` | For a positive even degree, a symmetric moment-matched probability-prior pair with the exact absolute-moment gap exists. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.priorZero_isProbabilityMeasure` | `MeasureTheory.IsProbabilityMeasure P.ν₀` | For a packaged prior pair, its first prior is a probability measure. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.priorOne_isProbabilityMeasure` | `MeasureTheory.IsProbabilityMeasure P.ν₁` | For a packaged prior pair, its second prior is a probability measure. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.priorZero_mass` | `P.ν₀ Set.univ = 1` | For a packaged prior pair, its first prior has total mass one. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.priorOne_mass` | `P.ν₁ Set.univ = 1` | For a packaged prior pair, its second prior has total mass one. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.priorZero_supported` | `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.IsSupportedOnUnitInterval P.ν₀` | For a packaged prior pair, its first prior is supported on the unit interval. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.priorOne_supported` | `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.IsSupportedOnUnitInterval P.ν₁` | For a packaged prior pair, its second prior is supported on the unit interval. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.priorZero_symmetric` | `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.IsSymmetric P.ν₀` | For a packaged prior pair, its first prior is symmetric about zero. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.priorOne_symmetric` | `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.IsSymmetric P.ν₁` | For a packaged prior pair, its second prior is symmetric about zero. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.prior_moments_eq` | `j ≤ K → ∫ (x : ℝ), x ^ j ∂P.ν₀ = ∫ (x : ℝ), x ^ j ∂P.ν₁` | For a packaged prior pair and a moment order no larger than the degree limit, the two priors have equal moments of that order. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.prior_absMoment_gap` | `∫ (x : ℝ), \|x\| ∂P.ν₁ - ∫ (x : ℝ), \|x\| ∂P.ν₀ = 2 * Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K` | For a packaged prior pair, the oriented difference in absolute first moments is twice the best approximation error. |
<!-- /GEN -->

### Inverse-degree approximation rate

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Rate -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs_upper` | `0 < K → Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K ≤ 1 / ↑K` | For a positive polynomial degree, the best absolute-value approximation error is at most one divided by that degree. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs_lower` | `0 < K → 1 / 100 / ↑K ≤ Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K` | For a positive polynomial degree, the cusp of absolute value forces the stated inverse-degree lower bound. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs_order` | `∃ c C, 0 < c ∧ c ≤ C ∧ ∀ (K : ℕ), 0 < K → c / ↑K ≤ Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K ∧ Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K ≤ C / ↑K` | There are universal positive constants that sandwich the best absolute-value approximation error between constant multiples of the reciprocal degree for every positive degree. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality -->
_(no documented declarations in Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality)_
<!-- /GEN -->


## 10a'''''''''. `Mathlib/Analysis/JacksonApproximation/` — order-four Jackson tensor approximation

This package constructs the normalized fourth-power Jackson kernel with explicit moment bounds,
converts its finite trigonometric expansions into algebraic polynomials, tensorizes the construction,
and transports the resulting approximation and coefficient bounds to four-dimensional rectangles.

### Kernel and moment bounds

<!-- GEN:Causalean.Mathlib.Analysis.JacksonApproximation.Kernel -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.JacksonApproximation.jraw` | `ℕ → ℝ → ℝ` | A nonnegative integer order and a real argument determine the raw order-four Jackson kernel, obtained from the fourth power of the Dirichlet sine quotient with its removable singularities filled continuously. |
| `Mathlib.Analysis.JacksonApproximation.jrawMass` | `ℕ → ℝ` | An integer order determines the raw Jackson mass, the integral of the raw kernel over the standard period from minus π to π. |
| `Mathlib.Analysis.JacksonApproximation.jackson` | `ℕ → ℝ → ℝ` | An integer order and a real argument determine the normalized order-four Jackson kernel, equal to the raw kernel divided by its mass over the standard period. |
| `Mathlib.Analysis.JacksonApproximation.jraw_eq_of_sin_ne_zero` | `Real.sin (t / 2) ≠ 0 → Causalean.Mathlib.Analysis.JacksonApproximation.jraw K t = (Real.sin (↑K * t / 2) / Real.sin (t / 2)) ^ 4` | At order K and argument t, if the denominator sine is nonzero, then the raw kernel equals the displayed fourth power of the sine quotient. |
| `Mathlib.Analysis.JacksonApproximation.jraw_eq_of_sin_eq_zero` | `Real.sin (t / 2) = 0 → Causalean.Mathlib.Analysis.JacksonApproximation.jraw K t = ↑K ^ 4` | At order K and argument t, if the denominator sine vanishes, then the raw kernel equals K to the fourth power. |
| `Mathlib.Analysis.JacksonApproximation.continuous_jraw` | `Continuous (Causalean.Mathlib.Analysis.JacksonApproximation.jraw K)` | For integer order K, the raw Jackson kernel is continuous on the real line. |
| `Mathlib.Analysis.JacksonApproximation.measurable_jraw` | `Measurable (Causalean.Mathlib.Analysis.JacksonApproximation.jraw K)` | For integer order K, the raw Jackson kernel is Borel measurable. |
| `Mathlib.Analysis.JacksonApproximation.integrableOn_jraw` | `MeasureTheory.IntegrableOn (Causalean.Mathlib.Analysis.JacksonApproximation.jraw K) (Set.Icc (-Real.pi) Real.pi) MeasureTheory.volume` | For integer order K, the raw Jackson kernel is integrable over the standard period. |
| `Mathlib.Analysis.JacksonApproximation.jraw_nonneg` | `0 ≤ Causalean.Mathlib.Analysis.JacksonApproximation.jraw K t` | At integer order K and real argument t, the raw Jackson kernel is nonnegative. |
| `Mathlib.Analysis.JacksonApproximation.jraw_even` | `Function.Even (Causalean.Mathlib.Analysis.JacksonApproximation.jraw K)` | For integer order K, the raw Jackson kernel is symmetric about zero. |
| `Mathlib.Analysis.JacksonApproximation.jrawMass_eq` | `0 < K → Causalean.Mathlib.Analysis.JacksonApproximation.jrawMass K = 2 * Real.pi / 3 * ↑K * (2 * ↑K ^ 2 + 1)` | For integer order K that is strictly positive, the raw Jackson mass equals two π thirds times K times two K squared plus one. |
| `Mathlib.Analysis.JacksonApproximation.jrawMass_lower` | `0 < K → 4 * Real.pi / 3 * ↑K ^ 3 ≤ Causalean.Mathlib.Analysis.JacksonApproximation.jrawMass K` | For integer order K that is strictly positive, the raw Jackson mass is at least four π thirds times K cubed. |
| `Mathlib.Analysis.JacksonApproximation.jrawMass_upper` | `0 < K → Causalean.Mathlib.Analysis.JacksonApproximation.jrawMass K ≤ 2 * Real.pi * ↑K ^ 3` | For integer order K that is strictly positive, the raw Jackson mass is at most two π times K cubed. |
| `Mathlib.Analysis.JacksonApproximation.jrawMass_pos` | `0 < K → 0 < Causalean.Mathlib.Analysis.JacksonApproximation.jrawMass K` | For integer order K that is strictly positive, the raw Jackson mass is strictly positive. |
| `Mathlib.Analysis.JacksonApproximation.continuous_jackson` | `Continuous (Causalean.Mathlib.Analysis.JacksonApproximation.jackson K)` | For integer order K, the normalized Jackson kernel is continuous on the real line. |
| `Mathlib.Analysis.JacksonApproximation.measurable_jackson` | `Measurable (Causalean.Mathlib.Analysis.JacksonApproximation.jackson K)` | For integer order K, the normalized Jackson kernel is Borel measurable. |
| `Mathlib.Analysis.JacksonApproximation.integrableOn_jackson` | `MeasureTheory.IntegrableOn (Causalean.Mathlib.Analysis.JacksonApproximation.jackson K) (Set.Icc (-Real.pi) Real.pi) MeasureTheory.volume` | For integer order K, the normalized Jackson kernel is integrable over the standard period. |
| `Mathlib.Analysis.JacksonApproximation.jackson_nonneg` | `0 < K → ∀ (t : ℝ), 0 ≤ Causalean.Mathlib.Analysis.JacksonApproximation.jackson K t` | At integer order K that is strictly positive and real argument t, the normalized Jackson kernel is nonnegative. |
| `Mathlib.Analysis.JacksonApproximation.jackson_even` | `Function.Even (Causalean.Mathlib.Analysis.JacksonApproximation.jackson K)` | For integer order K, the normalized Jackson kernel is symmetric about zero. |
| `Mathlib.Analysis.JacksonApproximation.jackson_integral_eq_one` | `0 < K → ∫ (t : ℝ) in Set.Icc (-Real.pi) Real.pi, Causalean.Mathlib.Analysis.JacksonApproximation.jackson K t = 1` | For integer order K that is strictly positive, the normalized Jackson kernel has unit mass over the standard period. |
| `Mathlib.Analysis.JacksonApproximation.jackson_first_moment` | `0 < K → ∫ (t : ℝ) in Set.Icc (-Real.pi) Real.pi, \|t\| * Causalean.Mathlib.Analysis.JacksonApproximation.jackson K t ≤ 32 / ↑K` | For integer order K that is strictly positive, the normalized absolute first moment is at most thirty-two divided by K. |
| `Mathlib.Analysis.JacksonApproximation.jackson_second_moment` | `0 < K → ∫ (t : ℝ) in Set.Icc (-Real.pi) Real.pi, t ^ 2 * Causalean.Mathlib.Analysis.JacksonApproximation.jackson K t ≤ 64 / ↑K ^ 2` | For integer order K that is strictly positive, the normalized second moment is at most sixty-four divided by K squared. |
| `Mathlib.Analysis.JacksonApproximation.jraw_isTrigPolyLE` | `0 < K → Causalean.Mathlib.Analysis.BernsteinSzegoTrig.IsTrigPolyLE (2 * (K - 1)) (Causalean.Mathlib.Analysis.JacksonApproximation.jraw K)` | For integer order K that is strictly positive, the raw Jackson kernel is a real trigonometric polynomial with frequency at most twice the predecessor of K. |
| `Mathlib.Analysis.JacksonApproximation.jackson_isTrigPolyLE` | `0 < K → Causalean.Mathlib.Analysis.BernsteinSzegoTrig.IsTrigPolyLE (2 * (K - 1)) (Causalean.Mathlib.Analysis.JacksonApproximation.jackson K)` | For integer order K that is strictly positive, the normalized Jackson kernel is a real trigonometric polynomial with frequency at most twice the predecessor of K. |
<!-- /GEN -->

### Even trigonometric extraction

<!-- GEN:Causalean.Mathlib.Analysis.JacksonApproximation.TrigExtraction -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE` | `ℕ → (ℝ → ℝ) → Prop` | A frequency limit and a real-valued function determine the assertion that the function is a real trigonometric polynomial within that limit. |
| `Mathlib.Analysis.JacksonApproximation.polyCoeffL1` | `Polynomial ℝ → ℝ` | A real polynomial determines its coefficient one-norm, the sum of the absolute values of its nonzero coefficients. |
| `Mathlib.Analysis.JacksonApproximation.even_trigPoly_exists_polynomial` | `Causalean.Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE n q → Function.Even q → ∃ p, p.natDegree ≤ n ∧ ∀ (t : ℝ), Polynomial.eval (Real.cos t) p = q t` | Given a frequency limit and a real function, if the function is a trigonometric polynomial within that limit and is symmetric about zero, then it is an ordinary polynomial in the cosine coordinate with degree at most that limit. |
| `Mathlib.Analysis.JacksonApproximation.polynomial_cos_is_even_trigPoly` | `p.natDegree ≤ n → (Causalean.Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE n fun t => Polynomial.eval (Real.cos t) p) ∧ Function.Even fun t => Polynomial.eval (Real.cos t) p` | Given a frequency limit and a real polynomial whose degree is at most that limit, composition with cosine is an even trigonometric polynomial within the same frequency limit. |
| `Mathlib.Analysis.JacksonApproximation.chebyshev_coeffL1_le` | `Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1 (Polynomial.Chebyshev.T ℝ ↑n) ≤ 3 ^ n` | For a nonnegative integer index, the coefficient one-norm of the corresponding first-kind Chebyshev polynomial is at most three to that index. |
| `Mathlib.Analysis.JacksonApproximation.cosine_sum_exists_polynomial` | `∃ p, p.natDegree ≤ n ∧ (∀ (t : ℝ), Polynomial.eval (Real.cos t) p = ∑ k ∈ Finset.range (n + 1), a k * Real.cos (↑k * t)) ∧ Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1 p ≤ ∑ k ∈ Finset.range (n + 1), \|a k\| * 3 ^ k` | Given a frequency limit and real cosine coefficients, the finite cosine sum has an ordinary polynomial representation of bounded degree whose coefficient one-norm is bounded by the stated weighted sum. |
<!-- /GEN -->

### Tensor convolution and multivariate extraction

<!-- GEN:Causalean.Mathlib.Analysis.JacksonApproximation.Tensor -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.JacksonApproximation.periodBox` | `(d : ℕ) → Set (Fin d → ℝ)` | A finite dimension determines the standard period box, whose coordinates all lie between minus π and π. |
| `Mathlib.Analysis.JacksonApproximation.normalizedCube` | `(d : ℕ) → Set (Fin d → ℝ)` | A finite dimension determines the normalized cube, whose coordinates all lie between minus one and one. |
| `Mathlib.Analysis.JacksonApproximation.tensorJackson` | `ℕ → (d : ℕ) → (Fin d → ℝ) → ℝ` | An integer kernel order, a finite dimension, and a point in period coordinates determine the tensor Jackson kernel, the product of the one-dimensional kernels across coordinates. |
| `Mathlib.Analysis.JacksonApproximation.cosPoint` | `(Fin d → ℝ) → Fin d → ℝ` | A finite dimension and a point in period coordinates determine the coordinatewise cosine point. |
| `Mathlib.Analysis.JacksonApproximation.cosPoint_mem_normalizedCube` | `Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint t ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d` | For a finite dimension and a point in period coordinates, the coordinatewise cosine point lies in the normalized cube. |
| `Mathlib.Analysis.JacksonApproximation.cosLift` | `((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ` | A finite dimension, a real function on normalized coordinates, and a point in period coordinates determine the cosine lift of the function by coordinatewise cosine precomposition. |
| `Mathlib.Analysis.JacksonApproximation.tensorConvolution` | `ℕ → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ` | A finite dimension, an integer kernel order, a real function on normalized coordinates, and a point in period coordinates determine the tensor Jackson convolution, the kernel-weighted average of the translated cosine lift over the period box. |
| `Mathlib.Analysis.JacksonApproximation.tensorJackson_nonneg` | `0 < K → ∀ (u : Fin d → ℝ), 0 ≤ Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d u` | For a finite dimension, integer order K that is strictly positive, and a point in period coordinates, the tensor Jackson kernel is nonnegative. |
| `Mathlib.Analysis.JacksonApproximation.measurable_tensorJackson` | `Measurable (Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d)` | For integer order K and a finite dimension, the tensor Jackson kernel is measurable. |
| `Mathlib.Analysis.JacksonApproximation.integrableOn_tensorJackson` | `MeasureTheory.IntegrableOn (Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d) (Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d) MeasureTheory.volume` | For integer order K and a finite dimension, the tensor Jackson kernel is integrable over the standard period box. |
| `Mathlib.Analysis.JacksonApproximation.integral_periodBox_prod` | `(∀ (i : Fin d), MeasureTheory.IntegrableOn (g i) (Set.Icc (-Real.pi) Real.pi) MeasureTheory.volume) → ∫ (u : Fin d → ℝ) in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d, ∏ i, g i (u i) = ∏ i, ∫ (t : ℝ) in Set.Icc (-Real.pi) Real.pi, g i t` | Given a finite dimension, one integrand for each coordinate, and integrability of every coordinate integrand over the standard period, the integral of their product over the period box equals the product of their one-dimensional integrals. |
| `Mathlib.Analysis.JacksonApproximation.tensorJackson_integral_eq_one` | `0 < K → ∫ (u : Fin d → ℝ) in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d, Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d u = 1` | For a finite dimension and integer order K that is strictly positive, the tensor Jackson kernel has unit mass over the period box. |
| `Mathlib.Analysis.JacksonApproximation.tensorJackson_first_moment_eq` | `0 < K → ∀ (i : Fin d), ∫ (u : Fin d → ℝ) in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d, \|u i\| * Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d u = ∫ (t : ℝ) in Set.Icc (-Real.pi) Real.pi, \|t\| * Causalean.Mathlib.Analysis.JacksonApproximation.jackson K t` | For a finite dimension, integer order K that is strictly positive, and a selected coordinate, the tensor kernel's absolute first moment in that coordinate equals the one-dimensional first moment. |
| `Mathlib.Analysis.JacksonApproximation.tensorJackson_second_moment_eq` | `0 < K → ∀ (i : Fin d), ∫ (u : Fin d → ℝ) in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox d, u i ^ 2 * Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K d u = ∫ (t : ℝ) in Set.Icc (-Real.pi) Real.pi, t ^ 2 * Causalean.Mathlib.Analysis.JacksonApproximation.jackson K t` | For a finite dimension, integer order K that is strictly positive, and a selected coordinate, the tensor kernel's second moment in that coordinate equals the one-dimensional second moment. |
| `Mathlib.Analysis.JacksonApproximation.tensorConvolution_nonneg` | `0 < K → ∀ {f : (Fin d → ℝ) → ℝ}, (∀ z ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d, 0 ≤ f z) → ∀ (x : Fin d → ℝ), 0 ≤ Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K f x` | For a finite dimension, integer order K that is strictly positive, a function that is nonnegative throughout the normalized cube, and a selected point in period coordinates, the tensor convolution is nonnegative at that point. |
| `Mathlib.Analysis.JacksonApproximation.tensorConvolution_const` | `0 < K → ∀ (c : ℝ) (x : Fin d → ℝ), Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K (fun x => c) x = c` | For a finite dimension, integer order K that is strictly positive, a real constant, and a point in period coordinates, tensor convolution preserves the constant function. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Analysis.JacksonApproximation.TensorExtraction -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.JacksonApproximation.tensorConvolution_exists_mvPolynomial` | `0 < K → ∀ (f : (Fin d → ℝ) → ℝ), ContinuousOn f (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d) → ∃ p, (∀ (x : Fin d → ℝ), (MvPolynomial.eval (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)) p = Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K f x) ∧ (∀ m ∈ p.support, ∀ (i : Fin d), m i ≤ 2 * (K - 1)) ∧ p.totalDegree ≤ d * (2 * (K - 1))` | For a finite dimension, integer order K that is strictly positive, and a function that is continuous on the normalized cube, its tensor Jackson convolution is represented after the cosine change of coordinates by a multivariate polynomial with the stated coordinate and total-degree bounds. |
| `Mathlib.Analysis.JacksonApproximation.tensorConvolution_approx_lipschitz` | `0 < K → ∀ (f : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L → ContinuousOn f (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d) → (∀ x ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d, ∀ y ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d, \|f x - f y\| ≤ L * ∑ i, \|x i - y i\|) → ∀ (x : Fin d → ℝ), \|Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K f x - f (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)\| ≤ 32 * ↑d * L / ↑K` | For a finite dimension, integer order K that is strictly positive, a function, a nonnegative Lipschitz constant, continuity on the normalized cube, the stated local coordinatewise Lipschitz bound, and a point in period coordinates, tensor Jackson convolution approximates the cosine lift there within thirty-two times dimension times the Lipschitz constant divided by K. |
<!-- /GEN -->

### Four-dimensional coefficient envelope

<!-- GEN:Causalean.Mathlib.Analysis.JacksonApproximation.CoefficientEnvelopeFour -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.JacksonApproximation.mvCoeffL1` | `MvPolynomial (Fin d) ℝ → ℝ` | A finite dimension and a real multivariate polynomial determine its coefficient one-norm, the sum of the absolute values of all monomial coefficients. |
| `Mathlib.Analysis.JacksonApproximation.tensorConvolution_exists_mvPolynomial_four_coeffBound` | `0 < K → ∀ (f : (Fin 4 → ℝ) → ℝ) (B : ℝ), 0 ≤ B → ContinuousOn f (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) → (∀ z ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4, \|f z\| ≤ B) → ∃ p, (∀ (x : Fin 4 → ℝ), (MvPolynomial.eval (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)) p = Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K f x) ∧ (∀ m ∈ p.support, ∀ (i : Fin 4), m i ≤ 2 * (K - 1)) ∧ p.totalDegree ≤ 8 * (K - 1) ∧ Causalean.Mathlib.Analysis.JacksonApproximation.mvCoeffL1 p ≤ 2 ^ (40 * K + 20) * B` | For integer order K that is strictly positive, a function on four normalized coordinates that is continuous on the normalized cube, a nonnegative uniform bound, and the corresponding bound on the function throughout the cube, its tensor convolution has a four-variable polynomial representation with the stated support, degree, and exponential coefficient one-norm bounds. |
<!-- /GEN -->

### Affine rectangle transport

<!-- GEN:Causalean.Mathlib.Analysis.JacksonApproximation.AffineFour -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.JacksonApproximation.affinePoint` | `(Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ) → Fin d → ℝ` | A finite dimension, a rectangle center, coordinate radii, and normalized coordinates determine the corresponding point under the center-plus-radius affine map. |
| `Mathlib.Analysis.JacksonApproximation.normalizedPoint` | `(Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ) → Fin d → ℝ` | A finite dimension, a rectangle center, coordinate radii, and a point in the rectangle's ambient space determine its normalized coordinates by subtracting the center and dividing coordinatewise by the radii. |
| `Mathlib.Analysis.JacksonApproximation.centeredRectangle` | `(Fin d → ℝ) → (Fin d → ℝ) → Set (Fin d → ℝ)` | A finite dimension, a center, and coordinate radii determine the closed centered rectangle consisting of points whose coordinatewise distance from the center does not exceed the corresponding radius. |
| `Mathlib.Analysis.JacksonApproximation.normalizedPoint_affinePoint` | `(∀ (i : Fin d), 0 < r i) → Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint c r (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z) = z` | For a finite dimension, a center, coordinate radii, and normalized coordinates, if every radius is positive, then normalizing the affine image recovers the original normalized coordinates. |
| `Mathlib.Analysis.JacksonApproximation.affinePoint_normalizedPoint` | `(∀ (i : Fin d), 0 < r i) → Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint c r y) = y` | For a finite dimension, a center, coordinate radii, and a point, if every radius is positive, then applying the affine map to the normalized point recovers the original point. |
| `Mathlib.Analysis.JacksonApproximation.affinePoint_mem_centeredRectangle` | `(∀ (i : Fin d), 0 < r i) → z ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d → Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z ∈ Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r` | For a finite dimension, a center, coordinate radii, and normalized coordinates, if every radius is nonnegative and the normalized point lies in the normalized cube, then its affine image lies in the centered rectangle. |
| `Mathlib.Analysis.JacksonApproximation.normalizedPoint_mem_normalizedCube` | `(∀ (i : Fin d), 0 < r i) → y ∈ Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r → Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint c r y ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d` | For a finite dimension, a center, coordinate radii, and a point, if every radius is positive and the point lies in the centered rectangle, then its normalized coordinates lie in the normalized cube. |
| `Mathlib.Analysis.JacksonApproximation.mvPolynomial_affine_substitution_four` | `(∀ (i : Fin 4), 0 < r i) → (∀ m ∈ q.support, ∀ (i : Fin 4), m i ≤ n) → ∃ p, (∀ (y : Fin 4 → ℝ), (MvPolynomial.eval y) p = (MvPolynomial.eval (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint c r y)) q) ∧ (∀ m ∈ p.support, ∀ (i : Fin 4), m i ≤ n) ∧ p.totalDegree ≤ q.totalDegree ∧ Causalean.Mathlib.Analysis.JacksonApproximation.mvCoeffL1 p ≤ Causalean.Mathlib.Analysis.JacksonApproximation.mvCoeffL1 q * ∏ i, max 1 ((1 + \|c i\|) / r i) ^ n` | Given a four-variable polynomial, a center, coordinate radii that are strictly positive, a coordinate-degree limit, and the corresponding support bound, affine substitution produces a four-variable polynomial with the stated evaluation, support, total-degree, and coefficient one-norm bounds. |
| `Mathlib.Analysis.JacksonApproximation.affineJackson_exists_mvPolynomial_four` | `0 < K → ∀ (c r : Fin 4 → ℝ), (∀ (i : Fin 4), 0 < r i) → ∀ (f : (Fin 4 → ℝ) → ℝ), ContinuousOn f (Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r) → ∃ p q, (∀ (y : Fin 4 → ℝ), (MvPolynomial.eval y) p = (MvPolynomial.eval (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint c r y)) q) ∧ (∀ (x : Fin 4 → ℝ), (MvPolynomial.eval (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)) q = Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K (fun z => f (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z)) x) ∧ (∀ m ∈ p.support, ∀ (i : Fin 4), m i ≤ 2 * (K - 1)) ∧ p.totalDegree ≤ 8 * (K - 1)` | For integer order K that is strictly positive, a rectangle center, positive coordinate radii, and a function that is continuous on the centered rectangle, the affine Jackson construction has a four-variable polynomial representation with the stated evaluation, support, and degree bounds. |
| `Mathlib.Analysis.JacksonApproximation.affineJackson_approx_four` | `0 < K → ∀ (c r : Fin 4 → ℝ), (∀ (i : Fin 4), 0 < r i) → ∀ (f : (Fin 4 → ℝ) → ℝ) (L : ℝ), 0 ≤ L → ContinuousOn f (Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r) → (∀ y ∈ Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r, ∀ z ∈ Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r, \|f y - f z\| ≤ L * ∑ i, \|(y i - z i) / r i\|) → ∃ p, (∀ m ∈ p.support, ∀ (i : Fin 4), m i ≤ 2 * (K - 1)) ∧ p.totalDegree ≤ 8 * (K - 1) ∧ ∀ y ∈ Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r, \|(MvPolynomial.eval y) p - f y\| ≤ 128 * L / ↑K` | For integer order K that is strictly positive, a rectangle center, positive coordinate radii, a function, a nonnegative Lipschitz constant, continuity on the centered rectangle, and the stated Lipschitz bound in normalized coordinates, there is a degree-controlled polynomial that approximates the function throughout the rectangle within one hundred twenty-eight times the Lipschitz constant divided by K. |
| `Mathlib.Analysis.JacksonApproximation.affineJackson_coeffBound_four` | `0 < K → ∀ (c r : Fin 4 → ℝ), (∀ (i : Fin 4), 0 < r i) → ∀ (f : (Fin 4 → ℝ) → ℝ) (B : ℝ), 0 ≤ B → ContinuousOn f (Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r) → (∀ y ∈ Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r, \|f y\| ≤ B) → ∃ p q, (∀ (y : Fin 4 → ℝ), (MvPolynomial.eval y) p = (MvPolynomial.eval (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedPoint c r y)) q) ∧ (∀ (x : Fin 4 → ℝ), (MvPolynomial.eval (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint x)) q = Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K (fun z => f (Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint c r z)) x) ∧ (∀ m ∈ p.support, ∀ (i : Fin 4), m i ≤ 2 * (K - 1)) ∧ p.totalDegree ≤ 8 * (K - 1) ∧ Causalean.Mathlib.Analysis.JacksonApproximation.mvCoeffL1 p ≤ 2 ^ (40 * K + 20) * B * ∏ i, max 1 ((1 + \|c i\|) / r i) ^ (2 * (K - 1))` | For integer order K that is strictly positive, a rectangle center, positive coordinate radii, a function, a nonnegative uniform bound, continuity on the centered rectangle, and the corresponding uniform bound throughout the rectangle, the affine Jackson construction has a four-variable polynomial representation with the stated evaluation, support, degree, and exponential coefficient one-norm bounds. |
<!-- /GEN -->

## 10a''''''''''. `Mathlib/Analysis/SymmetricTensorPencil/` — quantitative symmetric-tensor-pencil local inverse

This finite-dimensional recovery substrate turns a small error in a symmetric rank-one tensor decomposition into a permutation-aligned error bound for its factor columns. It separates the reusable chain into contractions, lifted conditioning, pencil perturbation, spectral matching, and normalization.

### Finite tensors and contractions

<!-- GEN:Causalean.Mathlib.Analysis.SymmetricTensorPencil.Basic -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.SymmetricTensorPencil.Vec` | `ℕ → Type` | A finite real vector with `p` coordinates. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.FactorMatrix` | `ℕ → ℕ → Type` | A real matrix whose `n` columns are vectors with `p` coordinates. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.Tensor` | `ℕ → ℕ → Type` | An order-`r` real tensor on a `p`-dimensional coordinate space, represented as an array. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.LiftIndex` | `ℕ → ℕ → Type` | The ordered multi-index space used for a degree-`d` tensor-power lift. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm` | `(ι → ℝ) → ℝ` | The Euclidean/Frobenius norm of a finite real array. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.matrixFrobeniusNorm` | `Matrix ι κ ℝ → ℝ` | The Frobenius norm of a finite real matrix. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm` | `Matrix ι ι ℝ → ℝ` | The Euclidean operator norm of a finite real square matrix. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue` | `Matrix ι κ ℝ → ℝ` | The last domain-indexed singular value of a finite real matrix. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.dot` | `Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p → ℝ` | The Euclidean dot product of two finite real vectors. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.rankOneTensor` | `(r : ℕ) → {p : ℕ} → Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p → Causalean.Mathlib.Analysis.SymmetricTensorPencil.Tensor p r` | The order-`r` rank-one tensor power of a vector. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor` | `(r : ℕ) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.FactorMatrix p n → (Fin n → ℝ) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.Tensor p r` | The symmetric tensor represented by weighted rank-one tensor powers of the columns. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.liftedDirections` | `(d : ℕ) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.FactorMatrix p n → Matrix (Causalean.Mathlib.Analysis.SymmetricTensorPencil.LiftIndex p d) (Fin n) ℝ` | The matrix whose columns are the ordered degree-`d` tensor powers of the factor columns. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.blockIndex` | `Causalean.Mathlib.Analysis.SymmetricTensorPencil.LiftIndex p d → (Fin q → Fin p) → Fin (d + d + q) → Fin p` | Concatenate two degree-`d` indices and one degree-`q` index into an order-`d+d+q` index. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.contractLast` | `(Fin q → Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p) → Matrix (Causalean.Mathlib.Analysis.SymmetricTensorPencil.LiftIndex p d) (Causalean.Mathlib.Analysis.SymmetricTensorPencil.LiftIndex p d) ℝ` | Contract the final `q` modes of an order-`d+d+q` tensor against a family of `q` probes. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.pencilProbes` | `Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p → Fin q → Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p` | The probe family containing `q-1` copies of `u` followed by one copy of `w`. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm_le_matrixFrobenius` | `Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm A ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.matrixFrobeniusNorm A` | The Euclidean operator norm of a finite real square matrix is at most its entrywise Frobenius norm. The stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.contractLast_frobeniusNorm_le` | `(∀ (a : Fin q), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (probes a) ≤ 1) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.matrixFrobeniusNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.contractLast T probes) ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm T` | Contracting a finite tensor against probes of norm at most one cannot increase its Frobenius norm. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.contractLast_operatorNorm_le` | `(∀ (a : Fin q), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (probes a) ≤ 1) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.contractLast T probes) ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm T` | The operator norm of a contracted tensor is bounded by the original tensor's Frobenius norm when every contraction probe has norm at most one. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.contractLast_decompositionTensor` | `0 < q → ∀ (C : Causalean.Mathlib.Analysis.SymmetricTensorPencil.FactorMatrix p n) (lam : Fin n → ℝ) (u w : Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p), Causalean.Mathlib.Analysis.SymmetricTensorPencil.contractLast (Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor (d + d + q) C lam) (Causalean.Mathlib.Analysis.SymmetricTensorPencil.pencilProbes u w) = (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C * Matrix.diagonal fun j => lam j * Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C j) ^ (q - 1) * Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot w (Matrix.col C j)) * (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C).transpose` | Contracting a weighted symmetric rank-one decomposition against `q-1` copies of `u` and one copy of `w` gives the lifted factor matrix times the corresponding diagonal loadings times its transpose. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm_liftedColumn_eq_one` | `0 < d → ∀ (C : Causalean.Mathlib.Analysis.SymmetricTensorPencil.FactorMatrix p n), (∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Matrix.col C j) = 1) → ∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm ((Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C).col j) = 1` | Unit columns have unit degree-`d` tensor lifts for every positive lifting degree. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.matrixFrobeniusNorm_liftedDirections` | `0 < d → ∀ (C : Causalean.Mathlib.Analysis.SymmetricTensorPencil.FactorMatrix p n), (∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Matrix.col C j) = 1) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.matrixFrobeniusNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) = √↑n` | The Frobenius norm of a lifted factor matrix with unit original columns is the square root of the number of columns. Under the listed assumptions, the stated conclusion follows. |
<!-- /GEN -->

### Lifted conditioning

<!-- GEN:Causalean.Mathlib.Analysis.SymmetricTensorPencil.Conditioning -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.SymmetricTensorPencil.OrthonormalColumns` | `Matrix ι κ ℝ → Prop` | A finite matrix has orthonormal columns when its transpose times itself is the identity. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.SameColumnSpace` | `Matrix ι κ ℝ → Matrix ι κ ℝ → Prop` | Two finite matrices have the same column space when their associated Euclidean linear maps have equal ranges. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue_transpose_mul_eq` | `Causalean.Mathlib.Analysis.SymmetricTensorPencil.OrthonormalColumns U → Causalean.Mathlib.Analysis.SymmetricTensorPencil.SameColumnSpace U V → Function.Injective ⇑(Matrix.toEuclideanLin V) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue (U.transpose * V) = Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue V` | Compressing a full-column-rank matrix in an orthonormal basis of its column space preserves its least column singular value. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm_compress_le` | `Causalean.Mathlib.Analysis.SymmetricTensorPencil.OrthonormalColumns U → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (U.transpose * A * U) ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm A` | An orthonormal compression cannot increase the Euclidean operator norm of a square matrix. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.injective_of_pos_le_leastColumnSingularValue` | `0 < sigma → sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue A → Function.Injective ⇑(Matrix.toEuclideanLin A)` | A positive lower bound for the last column singular value implies full column rank. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.compressedLift_leastSingularValue` | `0 < sigma → sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.OrthonormalColumns U → Causalean.Mathlib.Analysis.SymmetricTensorPencil.SameColumnSpace U (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) → sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue (U.transpose * Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C)` | If a lifted factor has least singular value at least `sigma`, then its coordinates in any orthonormal basis of its column space have the same lower singular-value bound. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.compressedLift_operatorNorm_le_sqrt` | `0 < d → Causalean.Mathlib.Analysis.SymmetricTensorPencil.OrthonormalColumns U → (∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Matrix.col C j) = 1) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (U.transpose * Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) ≤ √↑n` | The square coordinate matrix of a degree lift with unit columns has operator norm at most the square root of the number of factor columns. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.compressedLift_inverse_operatorNorm_le` | `0 < sigma → sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.OrthonormalColumns U → Causalean.Mathlib.Analysis.SymmetricTensorPencil.SameColumnSpace U (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (U.transpose * Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C)⁻¹ ≤ sigma⁻¹` | The inverse of the square coordinate matrix of a well-conditioned degree lift has operator norm at most the reciprocal of the lifted least-singular-value margin. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.compressedLift_condition_le` | `0 < d → 0 < sigma → (∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Matrix.col C j) = 1) → sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.OrthonormalColumns U → Causalean.Mathlib.Analysis.SymmetricTensorPencil.SameColumnSpace U (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (U.transpose * Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) * Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (U.transpose * Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C)⁻¹ ≤ √↑n / sigma` | A degree lift with unit columns and least singular value at least `sigma` has compressed diagonalizer condition number at most `sqrt n / sigma`. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.compressedDenominator_leastSingularValue` | `0 < q → 0 < sigma → 0 < kappa → Causalean.Mathlib.Analysis.SymmetricTensorPencil.OrthonormalColumns U → Causalean.Mathlib.Analysis.SymmetricTensorPencil.SameColumnSpace U (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) → sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) → (∀ (j : Fin n), kappa ≤ \|lam j\|) → (∀ (j : Fin n), sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C j)) → kappa * sigma ^ (q + 2) ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue ((U.transpose * Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C * Matrix.diagonal fun j => lam j * Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C j) ^ q) * (U.transpose * Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C).transpose)` | Given a factor matrix, its coefficients, a denominator probe, orthonormal lifted coordinates, positive degree and margins, a lifted singular-value margin, coefficient lower bounds, and probe-loading lower bounds, the compressed denominator contraction has least singular value at least the assembled margin. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.compressedNumerator_operatorNorm_le` | `0 < d → 0 < q → 0 ≤ Lambda → Causalean.Mathlib.Analysis.SymmetricTensorPencil.OrthonormalColumns U → (∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Matrix.col C j) = 1) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm u = 1 → Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm w = 1 → (∀ (j : Fin n), \|lam j\| ≤ Lambda) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (U.transpose * Causalean.Mathlib.Analysis.SymmetricTensorPencil.contractLast (Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor (d + d + q) C lam) (Causalean.Mathlib.Analysis.SymmetricTensorPencil.pencilProbes u w) * U) ≤ ↑n * Lambda` | Every compressed numerator contraction has operator norm at most `n * Lambda` when the factor columns and the contraction probe are unit and the coefficients are bounded by `Lambda`. Under the listed assumptions, the stated conclusion follows. |
<!-- /GEN -->

### Pencil perturbations

<!-- GEN:Causalean.Mathlib.Analysis.SymmetricTensorPencil.Pencil -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.SymmetricTensorPencil.rightPencil` | `Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ` | The right generalized-eigenvalue pencil formed from a numerator and denominator matrix. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.pencilPerturbationConstant` | `ℕ → ℝ → ℝ → ℝ` | The explicit Lipschitz coefficient for a right pencil whose denominator has lower singular value `eta` and whose numerator norm is at most `n * Lambda`. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.inverse_operatorNorm_le_reciprocal` | `0 < eta → eta ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue A → IsUnit A.det ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm A⁻¹ ≤ eta⁻¹` | A positive lower bound on the least singular value of a real square matrix makes its determinant a unit and bounds the operator norm of its inverse by the reciprocal margin. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.inverse_perturbation_bound` | `0 < eta → 0 ≤ e → eta ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue A → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (A' - A) ≤ e → e < eta / 2 → IsUnit A'.det ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm A'⁻¹ ≤ 2 / eta ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (A'⁻¹ - A⁻¹) ≤ 2 * e / eta ^ 2` | If a square matrix with least singular value at least `eta` is perturbed by at most `e < eta / 2`, the perturbed matrix stays invertible and its inverse norm is at most `2 / eta`. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.rightPencil_perturbation_bound` | `0 < eta → 0 ≤ Lambda → 0 ≤ e → eta ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue Au → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm Aw ≤ ↑n * Lambda → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Aw' - Aw) ≤ e → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Au' - Au) ≤ e → e < eta / 2 → IsUnit Au.det ∧ IsUnit Au'.det ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.rightPencil Aw' Au' - Causalean.Mathlib.Analysis.SymmetricTensorPencil.rightPencil Aw Au) ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.pencilPerturbationConstant n eta Lambda * e` | Given reference and perturbed numerator and denominator contractions, positive denominator, numerator, and error margins, a denominator singular-value bound, a numerator norm bound, numerator and denominator perturbation bounds, and a small-error condition, the two right generalized-eigenvalue pencils are invertible where required and differ by the explicit Lipschitz bound. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.rightPencil_eq_diagonalization` | `IsUnit S.det → (∀ (j : Fin n), lam j * den j ≠ 0) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.rightPencil ((S * Matrix.diagonal fun j => lam j * num j) * S.transpose) ((S * Matrix.diagonal fun j => lam j * den j) * S.transpose) = (S * Matrix.diagonal fun j => num j / den j) * S⁻¹` | Exact contracted factorizations produce a simultaneous diagonalization of every right pencil, with diagonal entries equal to probe-loading ratios. Under the listed assumptions, the stated conclusion follows. |
<!-- /GEN -->

### Spectral localization and matching

<!-- GEN:Causalean.Mathlib.Analysis.SymmetricTensorPencil.SpectralMatching -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.SymmetricTensorPencil.PairwiseGap` | `(ι → ℝ) → ℝ → Prop` | A finite real scalar family has pairwise gap at least `gap`. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.diagonalizableMatrix` | `Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ` | The matrix diagonalized by `S` with the prescribed real diagonal entries. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector` | `Matrix (Fin n) (Fin n) ℝ → Fin n → Matrix (Fin n) (Fin n) ℝ` | The rank-one spectral projector selected by coordinate `j` of an invertible diagonalizer. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector_operatorNorm_le` | `IsUnit S.det → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm S * Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm S⁻¹ ≤ chi → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S j) ≤ chi` | Every coordinate projector of a diagonalizer has Euclidean operator norm at most the declared condition-number envelope. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.diagonalizableMatrix_eigenvalue_localization` | `IsUnit S.det → IsUnit S'.det → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm S * Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm S⁻¹ ≤ chi → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.diagonalizableMatrix S' values' - Causalean.Mathlib.Analysis.SymmetricTensorPencil.diagonalizableMatrix S values) ≤ delta → ∀ (j' : Fin n), ∃ j, \|values' j' - values j\| ≤ chi * delta` | Every prescribed eigenvalue of a nearby explicitly diagonalized matrix lies within `chi * delta` of some eigenvalue of the reference diagonalization. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.exists_permutation_matching_of_localization` | `0 ≤ radius → Causalean.Mathlib.Analysis.SymmetricTensorPencil.PairwiseGap values' gap → (∀ (j' : Fin n), ∃ j, \|values' j' - values j\| ≤ radius) → 2 * radius < gap → ∃ pi, ∀ (j : Fin n), \|values' (pi j) - values j\| ≤ radius` | One-sided localization between two equally sized finite scalar families becomes a permutation matching when the source family is separated by more than twice the localization radius. Under the listed assumptions, the stated conclusion follows. |
<!-- /GEN -->

### Spectral projectors

<!-- GEN:Causalean.Mathlib.Analysis.SymmetricTensorPencil.Projectors -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.SymmetricTensorPencil.abs_trace_le_card_mul_operatorNorm` | `\|A.trace\| ≤ ↑n * Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm A` | The trace of a real square matrix is at most the dimension times its Euclidean operator norm in absolute value. The stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector_perturbation_of_matched_eigenvalue` | `IsUnit S.det → IsUnit S'.det → 0 < sigma → 0 < chi → 0 ≤ delta → Causalean.Mathlib.Analysis.SymmetricTensorPencil.PairwiseGap values sigma → Causalean.Mathlib.Analysis.SymmetricTensorPencil.PairwiseGap values' sigma → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm S * Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm S⁻¹ ≤ chi → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.diagonalizableMatrix S' values' - Causalean.Mathlib.Analysis.SymmetricTensorPencil.diagonalizableMatrix S values) ≤ delta → \|values' j' - values j\| ≤ chi * delta → 6 * chi * delta < sigma → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S' j' - Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S j) ≤ 6 * chi ^ 2 * delta / sigma ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S j) ≤ chi ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S' j') ≤ 2 * chi` | Matched simple eigenvalues of two nearby diagonalizable matrices have close coordinate projectors, and the perturbed projector remains controlled by twice the reference condition envelope. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.exists_permutation_projector_matching` | `IsUnit S.det → IsUnit S'.det → 0 < sigma → 0 < chi → 0 ≤ delta → Causalean.Mathlib.Analysis.SymmetricTensorPencil.PairwiseGap values sigma → Causalean.Mathlib.Analysis.SymmetricTensorPencil.PairwiseGap values' sigma → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm S * Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm S⁻¹ ≤ chi → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.diagonalizableMatrix S' values' - Causalean.Mathlib.Analysis.SymmetricTensorPencil.diagonalizableMatrix S values) ≤ delta → 6 * chi * delta < sigma → ∃ pi, ∀ (j : Fin n), \|values' (pi j) - values j\| < sigma / 3 ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S' (pi j) - Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S j) ≤ 6 * chi ^ 2 * delta / sigma ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S j) ≤ chi ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S' (pi j)) ≤ 2 * chi` | Given two diagonalizers, their simple spectra, invertibility, positive separation, conditioning, and error margins, separation of both spectra, a diagonalizer condition bound, a pencil perturbation bound, and the required small-error condition, one permutation matches the simple spectral projectors with explicit eigenvalue and operator-norm bounds. Under the listed assumptions, the stated conclusion follows. |
<!-- /GEN -->

### Direction recovery

<!-- GEN:Causalean.Mathlib.Analysis.SymmetricTensorPencil.Recovery -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.SymmetricTensorPencil.standardBasis` | `(p : ℕ) → Fin p → Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p` | The standard coordinate vector in a finite real coordinate space. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.normalizeFinite` | `(ι → ℝ) → ι → ℝ` | Normalize a finite real array by its Euclidean norm, with the conventional zero value when the input is zero. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.normalizeVec` | `Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p` | Normalize a finite coordinate vector by its Euclidean norm. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.recoverRankOneLift` | `Matrix (Causalean.Mathlib.Analysis.SymmetricTensorPencil.LiftIndex p d) (Causalean.Mathlib.Analysis.SymmetricTensorPencil.LiftIndex p d) ℝ → Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p → Causalean.Mathlib.Analysis.SymmetricTensorPencil.LiftIndex p d → ℝ` | Apply a candidate projector to a degree-`d` rank-one lift and normalize the resulting lifted direction. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.recoverRankOneLift_error_le` | `0 < d → ∀ (P P' : Matrix (Causalean.Mathlib.Analysis.SymmetricTensorPencil.LiftIndex p d) (Causalean.Mathlib.Analysis.SymmetricTensorPencil.LiftIndex p d) ℝ) (c : Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p) {delta : ℝ}, Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm c = 1 → ((P.mulVec fun I => ∏ k, c (I k)) = fun I => ∏ k, c (I k)) → 0 ≤ delta → delta < 1 → Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (P' - P) ≤ delta → Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.recoverRankOneLift P' c - fun I => ∏ k, c (I k)) ≤ 2 * delta / (1 - delta)` | A matched nearby projector recovers the normalized rank-one lifted direction with error at most `2 * delta / (1 - delta)`. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.traceCoordinates` | `(Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p → Matrix (Fin n) (Fin n) ℝ) → (Fin n → Matrix (Fin n) (Fin n) ℝ) → Fin n → Causalean.Mathlib.Analysis.SymmetricTensorPencil.Vec p` | Trace coordinates evaluate each coordinate pencil on a selected rank-one spectral projector. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.traceCoordinates_diagonalization` | `IsUnit S.det → (∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C j) ≠ 0) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.traceCoordinates (fun w => Causalean.Mathlib.Analysis.SymmetricTensorPencil.diagonalizableMatrix S fun j => Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot w (Matrix.col C j) / Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C j)) (Causalean.Mathlib.Analysis.SymmetricTensorPencil.coordinateProjector S) = fun j => (Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C j))⁻¹ • Matrix.col C j` | For an exact simultaneous diagonalization, trace coordinates recover a factor column divided by its positive denominator-probe loading. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.traceCoordinates_perturbation_bound` | `(∀ (i : Fin p), Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (G' (Causalean.Mathlib.Analysis.SymmetricTensorPencil.standardBasis p i) - G (Causalean.Mathlib.Analysis.SymmetricTensorPencil.standardBasis p i)) ≤ pencilError) → (∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (P' j - P j) ≤ projectorError) → (∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (P' j) ≤ projectorNorm) → (∀ (i : Fin p), Causalean.Mathlib.Analysis.SymmetricTensorPencil.squareOperatorNorm (G (Causalean.Mathlib.Analysis.SymmetricTensorPencil.standardBasis p i)) ≤ pencilNorm) → ∀ (i : Fin p) (j : Fin n), \|Causalean.Mathlib.Analysis.SymmetricTensorPencil.traceCoordinates G' P' j i - Causalean.Mathlib.Analysis.SymmetricTensorPencil.traceCoordinates G P j i\| ≤ ↑n * (pencilError * projectorNorm + pencilNorm * projectorError)` | Given reference and perturbed coordinate pencils, reference and perturbed projectors, coordinate-pencil error bounds, projector error bounds, perturbed-projector norm bounds, and reference-pencil norm bounds, every trace coordinate obeys the explicit product error bound. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm_sub_le_sqrt_mul` | `0 ≤ b → (∀ (i : Fin p), \|x i - y i\| ≤ b) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (x - y) ≤ √↑p * b` | A uniform coordinatewise error bound gives a Euclidean error bound larger by at most the square root of the number of coordinates. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.normalizeVec_sub_normalizeVec_le` | `0 < Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm x → 0 < Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm y → Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.normalizeVec x - Causalean.Mathlib.Analysis.SymmetricTensorPencil.normalizeVec y) ≤ 2 * Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (x - y) / min (Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm x) (Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm y)` | Normalization is quantitatively stable away from zero: the distance between normalized vectors is at most twice their original distance divided by the smaller input norm. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.normalizeVec_inv_smul_eq` | `Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm c = 1 → 0 < a → Causalean.Mathlib.Analysis.SymmetricTensorPencil.normalizeVec (a⁻¹ • c) = c` | Positively rescaling a unit vector and then normalizing returns the original vector. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.matrixFrobeniusNorm_le_sqrt_mul_of_columns` | `0 ≤ b → (∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Matrix.col A j - Matrix.col B j) ≤ b) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.matrixFrobeniusNorm (A - B) ≤ √↑n * b` | If corresponding columns have Euclidean error at most `b`, their matrix Frobenius error is at most `sqrt n * b`. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.permuteColumns` | `Equiv.Perm (Fin n) → Causalean.Mathlib.Analysis.SymmetricTensorPencil.FactorMatrix p n` | Permute the columns of a finite factor matrix. With its explicit inputs, the defined object is given by the displayed formula. |
<!-- /GEN -->

### Assembled local inverse

<!-- GEN:Causalean.Mathlib.Analysis.SymmetricTensorPencil.Main -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.SymmetricTensorPencil.contractedMargin` | `ℕ → ℝ → ℝ → ℝ` | The contracted denominator singular-value margin assembled from coefficient, probe, and lifted-factor margins. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.liftedConditionEnvelope` | `ℕ → ℝ → ℝ` | The condition-number envelope for a lifted matrix with `n` unit columns and least singular value at least `sigma`. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.localInverseRadius` | `ℕ → ℕ → ℝ → ℝ → ℝ → ℝ` | The admissible tensor perturbation radius for the quantitative tensor-pencil inverse. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.traceRecoveryConstant` | `ℕ → ℕ → ℝ → ℝ → ℝ → ℝ` | The coordinatewise trace-recovery Lipschitz factor for the quantitative tensor-pencil inverse. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.factorRecoveryConstant` | `ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ` | The final factor-matrix Frobenius Lipschitz factor for the quantitative tensor-pencil inverse. With its explicit inputs, the defined object is given by the displayed formula. |
| `Mathlib.Analysis.SymmetricTensorPencil.localInverse_constants_pos` | `0 < p → 0 < n → 0 < q → ∀ {sigma kappa Lambda : ℝ}, 0 < sigma → 0 < kappa → kappa ≤ Lambda → 0 < Causalean.Mathlib.Analysis.SymmetricTensorPencil.contractedMargin q sigma kappa ∧ 0 < Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedConditionEnvelope n sigma ∧ 0 < Causalean.Mathlib.Analysis.SymmetricTensorPencil.pencilPerturbationConstant n (Causalean.Mathlib.Analysis.SymmetricTensorPencil.contractedMargin q sigma kappa) Lambda ∧ 0 < Causalean.Mathlib.Analysis.SymmetricTensorPencil.localInverseRadius n q sigma kappa Lambda ∧ 0 < Causalean.Mathlib.Analysis.SymmetricTensorPencil.traceRecoveryConstant n q sigma kappa Lambda ∧ 0 < Causalean.Mathlib.Analysis.SymmetricTensorPencil.factorRecoveryConstant p n q sigma kappa Lambda` | For positive dimensions and admissible positive margins, the contracted margin, lifted condition envelope, pencil constant, local radius, trace constant, and factor constant are all strictly positive. Under the listed assumptions, the stated conclusion follows. |
| `Mathlib.Analysis.SymmetricTensorPencil.exists_permutation_factorMatrix_frobeniusNorm_le` | `0 < p → 0 < n → 0 < d → 0 < q → 0 < sigma ∧ sigma ≤ 1 → 0 < kappa → kappa ≤ Lambda → Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm u = 1 → Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm v = 1 → ((∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Matrix.col C j) = 1) ∧ ∀ (j : Fin n), Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Matrix.col C' j) = 1) → ((∀ (j : Fin n), kappa ≤ \|lam j\| ∧ \|lam j\| ≤ Lambda) ∧ ∀ (j : Fin n), kappa ≤ \|lam' j\| ∧ \|lam' j\| ≤ Lambda) → ((∀ (j : Fin n), sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C j)) ∧ ∀ (j : Fin n), sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C' j)) → sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C) ∧ sigma ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.leastColumnSingularValue (Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedDirections d C') → Causalean.Mathlib.Analysis.SymmetricTensorPencil.PairwiseGap (fun j => Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot v (Matrix.col C j) / Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C j)) sigma ∧ Causalean.Mathlib.Analysis.SymmetricTensorPencil.PairwiseGap (fun j => Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot v (Matrix.col C' j) / Causalean.Mathlib.Analysis.SymmetricTensorPencil.dot u (Matrix.col C' j)) sigma → Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor (d + d + q) C' lam' - Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor (d + d + q) C lam) < Causalean.Mathlib.Analysis.SymmetricTensorPencil.localInverseRadius n q sigma kappa Lambda → ∃ pi, Causalean.Mathlib.Analysis.SymmetricTensorPencil.matrixFrobeniusNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.permuteColumns C' pi - C) ≤ Causalean.Mathlib.Analysis.SymmetricTensorPencil.factorRecoveryConstant p n q sigma kappa Lambda * Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm (Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor (d + d + q) C' lam' - Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor (d + d + q) C lam)` | Quantitative symmetric-tensor-pencil local inverse. Given two finite factor matrices, their coefficient vectors, two probes, the gap and coefficient margins, positive ambient dimensions and degrees, an admissible singular-value margin, positive and compatible coefficient bounds, unit probes, unit factor columns, two-sided coefficient bounds, positive denominator loadings, well-conditioned lifted directions, separated pencil ratios, and a tensor perturbation below the explicit local radius, one column permutation makes the factor-matrix Frobenius error at most the stated Lipschitz factor times the tensor Frobenius error. Under the listed assumptions, the stated conclusion follows. |
<!-- /GEN -->
