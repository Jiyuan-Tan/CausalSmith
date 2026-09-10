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

## Mathlib/Combinatorics/JohnsonKneser — uniform-slice harmonic analysis

This package provides a reusable real-valued harmonic decomposition for fixed-size subsets of a finite population.  It defines the inclusion-degree filtration and its canonical orthogonal Johnson layers, proves that centered slice functions decompose into positive degrees, and gives the Kneser disjointness operator's signed binomial and normalized falling-factorial eigenvalues.

### Uniform slice and inclusion-degree filtration

<!-- GEN:Causalean.Mathlib.Combinatorics.JohnsonKneser.Basic -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Combinatorics.JohnsonKneser.Omega` | `ℕ → ℕ → Type` | For a population with `n` labelled units and a requested subset size `M`, the uniform slice is represented by the `M`-element subsets of that population. |
| `Mathlib.Combinatorics.JohnsonKneser.instDecidableEqOmega` | `(n M : ℕ) → DecidableEq (Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega n M)` | — |
| `Mathlib.Combinatorics.JohnsonKneser.instFintypeOmega` | `(n M : ℕ) → Fintype (Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega n M)` | — |
| `Mathlib.Combinatorics.JohnsonKneser.SliceFn` | `ℕ → ℕ → Type` | For a population size `n` and a slice size `M`, the slice-function space is the real Euclidean space of functions on that uniform slice. |
| `Mathlib.Combinatorics.JohnsonKneser.sliceInner` | `Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M → ℝ` | For a first slice function and a second slice function, the uniform-slice inner product is the average of their pointwise products over all slice points. |
| `Mathlib.Combinatorics.JohnsonKneser.mean` | `ℝ` | For a slice function, its uniform mean is the average of its values over the slice. |
| `Mathlib.Combinatorics.JohnsonKneser.constFn` | `ℝ → Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M` | For a real value, the constant slice function is the function taking that value at every slice point. |
| `Mathlib.Combinatorics.JohnsonKneser.center` | `Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M` | For a slice function, its centered version is obtained by subtracting its uniform mean at every slice point. |
| `Mathlib.Combinatorics.JohnsonKneser.inclusionMonomial` | `Finset (Fin n) → Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M` | For a set of labelled units, its inclusion monomial is one on slice points containing that set and zero elsewhere. |
| `Mathlib.Combinatorics.JohnsonKneser.degreeAtMost` | `(n M : ℕ) → ℕ → Submodule ℝ (Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M)` | For a population size, a slice size, and a degree bound, the degree-at-most subspace is the linear span of inclusion monomials indexed by sets no larger than that bound. |
| `Mathlib.Combinatorics.JohnsonKneser.degreeAtMost_mono` | `d ≤ e → Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M d ≤ Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M e` | When the first degree bound does not exceed the second, every function in the first inclusion-degree subspace also belongs to the second. |
| `Mathlib.Combinatorics.JohnsonKneser.mem_degreeAtMost_zero_iff` | `M ≤ n → ∀ (f : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M), f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M 0 ↔ ∃ c, f = Causalean.Mathlib.Combinatorics.JohnsonKneser.constFn c` | When the requested slice size is feasible, a slice function belongs to the degree-zero subspace exactly when it is constant, for the given slice function. |
| `Mathlib.Combinatorics.JohnsonKneser.degreeAtMost_eq_top` | `M ≤ n → Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M M = ⊤` | When the requested slice size is feasible, inclusion monomials through degree `M` span every real function on the uniform slice. |
| `Mathlib.Combinatorics.JohnsonKneser.card_omega` | `M ≤ n → Fintype.card (Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega n M) = n.choose M` | When the requested slice size is feasible, the uniform slice has exactly the usual binomial number of points. |
| `Mathlib.Combinatorics.JohnsonKneser.sliceInner_eq` | `M ≤ n → ∀ (f g : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M), Causalean.Mathlib.Combinatorics.JohnsonKneser.sliceInner f g = (↑(n.choose M))⁻¹ * inner ℝ f g` | When the requested slice size is feasible, the uniform inner product of the two given slice functions equals the ordinary function-space inner product divided by the number of slice points, for the first function and the second function. |
| `Mathlib.Combinatorics.JohnsonKneser.mean_constFn` | `M ≤ n → ∀ (c : ℝ), Causalean.Mathlib.Combinatorics.JohnsonKneser.mean (Causalean.Mathlib.Combinatorics.JohnsonKneser.constFn c) = c` | When the requested slice size is feasible, the uniform mean of the given constant slice function equals its constant value, for the real value. |
<!-- /GEN -->

### Johnson harmonic projections

<!-- GEN:Causalean.Mathlib.Combinatorics.JohnsonKneser.Harmonics -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic` | `(n M : ℕ) → ℕ → Submodule ℝ (Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M)` | For a population size and a slice size, the Johnson harmonic subspaces are the degree-zero inclusion layer at degree zero and the new orthogonal inclusion-degree layer at each positive degree. |
| `Mathlib.Combinatorics.JohnsonKneser.harmonicProjection` | `(n M : ℕ) → Fin (M + 1) → Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M →ₗ[ℝ] Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M` | For a population size, a slice size, and a harmonic degree, the harmonic projection is the canonical linear orthogonal projection onto that degree's Johnson harmonic subspace. |
| `Mathlib.Combinatorics.JohnsonKneser.harmonicProjection_add` | `(Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) (f + g) = (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f + (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) g` | For a harmonic degree, the projection of the sum equals the sum of the projections of the first slice function and the second slice function. |
| `Mathlib.Combinatorics.JohnsonKneser.harmonicProjection_smul` | `(Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) (c • f) = c • (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f` | For a harmonic degree, a real scalar, and a slice function, projecting after scalar multiplication equals scalar multiplication after projection. |
| `Mathlib.Combinatorics.JohnsonKneser.degreeAtMost_succ_eq_sup_harmonic` | `Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M (d + 1) = Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M d ⊔ Causalean.Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic n M (d + 1)` | For a degree bound, the next inclusion-degree space is the sum of the preceding space and its new Johnson harmonic layer. |
| `Mathlib.Combinatorics.JohnsonKneser.degreeAtMost_eq_iSup_harmonic` | `Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M M = ⨆ k, Causalean.Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic n M ↑k` | The full degree-at-most-`M` space is the supremum of the Johnson harmonic layers from degree zero through degree `M`. |
| `Mathlib.Combinatorics.JohnsonKneser.harmonicProjection_mem` | `(Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic n M ↑k` | For a harmonic degree and a slice function, the projected component belongs to that degree's Johnson harmonic subspace. |
| `Mathlib.Combinatorics.JohnsonKneser.harmonicProjection_eq_self_iff` | `(Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f = f ↔ f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic n M ↑k` | For a harmonic degree and a slice function, projection leaves the function unchanged exactly when it already lies in that harmonic subspace. |
| `Mathlib.Combinatorics.JohnsonKneser.harmonicProjection_idem` | `(Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) ((Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f) = (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f` | For a harmonic degree and a slice function, applying the harmonic projection twice gives the same component as applying it once. |
| `Mathlib.Combinatorics.JohnsonKneser.sliceInner_residual_eq_zero` | `M ≤ n → ∀ (k : Fin (M + 1)) (f g : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M), g ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic n M ↑k → Causalean.Mathlib.Combinatorics.JohnsonKneser.sliceInner (f - (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f) g = 0` | When the requested slice size is feasible, the residual after projection is orthogonal under the uniform slice inner product to the given harmonic function, for a harmonic degree, a slice function, a comparison function, and evidence that the comparison function is in that harmonic subspace. |
| `Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic_pairwise_orthogonal` | `M ≤ n → ∀ {j k : Fin (M + 1)}, j ≠ k → ∀ {f g : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M}, f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic n M ↑j → g ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic n M ↑k → Causalean.Mathlib.Combinatorics.JohnsonKneser.sliceInner f g = 0` | When the requested slice size is feasible and the two harmonic degrees are distinct, functions in those two Johnson harmonic subspaces are orthogonal under the uniform slice inner product, for the first function's membership evidence and the second function's membership evidence. |
| `Mathlib.Combinatorics.JohnsonKneser.sum_harmonicProjection_eq` | `M ≤ n → ∀ (f : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M), ∑ k, (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f = f` | When the requested slice size is feasible, the given slice function equals the finite sum of its harmonic projections from degree zero through degree `M`, for the slice function. |
| `Mathlib.Combinatorics.JohnsonKneser.harmonicProjection_zero_eq_mean` | `M ≤ n → ∀ (f : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M), (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M ⟨0, Nat.zero_lt_succ M⟩) f = Causalean.Mathlib.Combinatorics.JohnsonKneser.constFn (Causalean.Mathlib.Combinatorics.JohnsonKneser.mean f)` | When the requested slice size is feasible, the degree-zero projection of the given slice function is the constant function at its uniform mean, for the slice function. |
| `Mathlib.Combinatorics.JohnsonKneser.sum_positive_harmonicProjection_eq_center` | `M ≤ n → ∀ (f : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M), ∑ k with 0 < ↑k, (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f = Causalean.Mathlib.Combinatorics.JohnsonKneser.center f` | When the requested slice size is feasible, centering the given slice function equals the sum of its positive-degree harmonic projections, for the slice function. |
| `Mathlib.Combinatorics.JohnsonKneser.harmonicProjection_pairwise_orthogonal` | `M ≤ n → ∀ (f : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M) {j k : Fin (M + 1)}, j ≠ k → Causalean.Mathlib.Combinatorics.JohnsonKneser.sliceInner ((Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M j) f) ((Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f) = 0` | When the requested slice size is feasible and the two harmonic degrees are distinct, the corresponding projected components of the given function are orthogonal under the uniform slice inner product, for the slice function. |
<!-- /GEN -->

### Kneser operator

<!-- GEN:Causalean.Mathlib.Combinatorics.JohnsonKneser.Kneser -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency` | `(n M : ℕ) → Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M →ₗ[ℝ] Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M` | For a population size and a slice size, the unnormalized Kneser adjacency operator is specified by summing a function over all equally sized subsets disjoint from the argument, preserving addition, and commuting with real scalar multiplication. |
| `Mathlib.Combinatorics.JohnsonKneser.disjointIndicator` | `Finset (Fin n) → Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M` | For a set of labelled units, its disjointness indicator is one at slice points disjoint from that set and zero elsewhere. |
| `Mathlib.Combinatorics.JohnsonKneser.disjointIndicator_eq_sum_powerset` | `Causalean.Mathlib.Combinatorics.JohnsonKneser.disjointIndicator S = ∑ T ∈ S.powerset, (-1) ^ T.card • Causalean.Mathlib.Combinatorics.JohnsonKneser.inclusionMonomial T` | For a set of labelled units, its disjointness indicator equals the alternating inclusion-exclusion sum of the inclusion monomials of its subsets. |
| `Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency_inclusionMonomial_eq` | `2 * M ≤ n → ∀ (S : Finset (Fin n)), S.card ≤ M → (Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency n M) (Causalean.Mathlib.Combinatorics.JohnsonKneser.inclusionMonomial S) = ↑((n - M - S.card).choose (M - S.card)) • Causalean.Mathlib.Combinatorics.JohnsonKneser.disjointIndicator S` | When two disjoint slice-sized subsets can fit in the population and the indexing set is no larger than the slice size, Kneser adjacency maps the given inclusion monomial to its disjointness indicator times the number of compatible completions, for the indexing set. |
| `Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency_inclusionMonomial_mod_lower` | `2 * M ≤ n → ∀ {d : ℕ}, 0 < d → ∀ (S : Finset (Fin n)), S.card = d → d ≤ M → (Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency n M) (Causalean.Mathlib.Combinatorics.JohnsonKneser.inclusionMonomial S) - ((-1) ^ d * ↑((n - M - d).choose (M - d))) • Causalean.Mathlib.Combinatorics.JohnsonKneser.inclusionMonomial S ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M (d - 1)` | When two disjoint slice-sized subsets can fit in the population, the degree is positive, the indexing set has exactly that degree, and the degree does not exceed the slice size, Kneser adjacency differs from its classical degree eigenvalue times that monomial only by a lower-degree function. |
| `Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency_mem_degreeAtMost` | `2 * M ≤ n → ∀ {d : ℕ}, d ≤ M → ∀ f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M d, (Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency n M) f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M d` | When two disjoint slice-sized subsets can fit in the population, the degree bound does not exceed the slice size, and the given function belongs to that inclusion-degree subspace, Kneser adjacency remains in the same inclusion-degree subspace, for the slice function. |
| `Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency_sub_eigen_mem_lower` | `2 * M ≤ n → ∀ {d : ℕ}, 0 < d → d ≤ M → ∀ f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M d, (Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency n M) f - ((-1) ^ d * ↑((n - M - d).choose (M - d))) • f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.degreeAtMost n M (d - 1)` | When two disjoint slice-sized subsets can fit in the population, the degree is positive, the degree does not exceed the slice size, and the given function has inclusion degree at most that degree, subtracting the classical degree eigenvalue leaves a function one degree lower, for the slice function. |
| `Mathlib.Combinatorics.JohnsonKneser.sliceInner_kneserAdjacency` | `Causalean.Mathlib.Combinatorics.JohnsonKneser.sliceInner ((Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency n M) f) g = Causalean.Mathlib.Combinatorics.JohnsonKneser.sliceInner f ((Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency n M) g)` | For a first slice function and a second slice function, Kneser adjacency is self-adjoint under the uniform slice inner product. |
| `Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency_eigen` | `2 * M ≤ n → ∀ (k : Fin (M + 1)), ∀ f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic n M ↑k, (Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency n M) f = ((-1) ^ ↑k * ↑((n - M - ↑k).choose (M - ↑k))) • f` | When two disjoint slice-sized subsets can fit in the population, the selected harmonic degree, and the given function belongs to that degree's Johnson harmonic subspace, unnormalized Kneser adjacency acts by its classical signed binomial eigenvalue, for the slice function. |
| `Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency_harmonicProjection` | `2 * M ≤ n → ∀ (k : Fin (M + 1)) (f : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M), (Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency n M) ((Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f) = ((-1) ^ ↑k * ↑((n - M - ↑k).choose (M - ↑k))) • (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f` | When two disjoint slice-sized subsets can fit in the population, the selected harmonic degree, and the given slice function, Kneser adjacency acts on its projected harmonic component by the classical signed binomial eigenvalue. |
| `Mathlib.Combinatorics.JohnsonKneser.normalizedKneserAdjacency` | `(n M : ℕ) → Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M →ₗ[ℝ] Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M` | For a population size and a slice size, the normalized Kneser adjacency operator is the unnormalized disjointness sum divided by the number of disjoint neighbors. |
| `Mathlib.Combinatorics.JohnsonKneser.normalizedKneser_eigenvalue_eq` | `2 * M ≤ n → ∀ (k : Fin (M + 1)), (↑((n - M).choose M))⁻¹ * ↑((n - M - ↑k).choose (M - ↑k)) = ↑(M.descFactorial ↑k) / ↑((n - M).descFactorial ↑k)` | When two disjoint slice-sized subsets can fit in the population and the selected harmonic degree, the normalized Kneser eigenvalue magnitude equals the corresponding ratio of falling factorials. |
| `Mathlib.Combinatorics.JohnsonKneser.normalizedKneserAdjacency_eigen` | `2 * M ≤ n → ∀ (k : Fin (M + 1)), ∀ f ∈ Causalean.Mathlib.Combinatorics.JohnsonKneser.johnsonHarmonic n M ↑k, (Causalean.Mathlib.Combinatorics.JohnsonKneser.normalizedKneserAdjacency n M) f = ((-1) ^ ↑k * (↑(M.descFactorial ↑k) / ↑((n - M).descFactorial ↑k))) • f` | When two disjoint slice-sized subsets can fit in the population, the selected harmonic degree, and the given function belongs to that degree's Johnson harmonic subspace, normalized Kneser adjacency acts by the signed falling-factorial eigenvalue, for the slice function. |
| `Mathlib.Combinatorics.JohnsonKneser.normalizedKneserAdjacency_harmonicProjection` | `2 * M ≤ n → ∀ (k : Fin (M + 1)) (f : Causalean.Mathlib.Combinatorics.JohnsonKneser.SliceFn n M), (Causalean.Mathlib.Combinatorics.JohnsonKneser.normalizedKneserAdjacency n M) ((Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f) = ((-1) ^ ↑k * (↑(M.descFactorial ↑k) / ↑((n - M).descFactorial ↑k))) • (Causalean.Mathlib.Combinatorics.JohnsonKneser.harmonicProjection n M k) f` | When two disjoint slice-sized subsets can fit in the population, the selected harmonic degree, and the given slice function, normalized Kneser adjacency acts on its projected harmonic component by the signed falling-factorial eigenvalue. |
<!-- /GEN -->

## Mathlib/LinearAlgebra/FinitePerronFrobeniusPositiveEigenvector — finite positive Perron eigenvectors

This finite-dimensional Perron--Frobenius substrate supplies a strictly positive, unit-norm top eigenvector for a symmetric, entrywise-nonnegative irreducible real matrix. It also exposes interchangeable Rayleigh-value presentations and component restriction/zero-extension bridges for finite graph and network arguments.

### Rayleigh-value interface

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Basic -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec` | `(ι : Type u_2) → [Fintype ι] → Type u_2` | A Euclidean real vector indexed by a finite coordinate type, called a finite real coordinate vector, is given by the Euclidean space on that coordinate type. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec` | `Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι` | The Euclidean vector obtained from a finite real vector by taking the absolute value of every coordinate is given coordinate by coordinate. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm` | `Matrix ι ι ℝ → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι → ℝ` | The quadratic form associated with a finite real matrix and a Euclidean coordinate vector, called its Rayleigh form, is given by the vector-matrix-vector quadratic sum. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue` | `Matrix ι ι ℝ → ℝ` | The greatest quadratic Rayleigh-form value among the Euclidean unit vectors for a finite real matrix, called the Euclidean-sphere top Rayleigh value, is given by a supremum. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.coordinateSphereRayleighValue` | `Matrix ι ι ℝ → ℝ` | The greatest quadratic Rayleigh-form value among the coordinate vectors whose squared coordinates sum to one for a finite real matrix, called the coordinate-sphere top Rayleigh value, is given by a supremum. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.iSupRayleighValue` | `Matrix ι ι ℝ → ℝ` | Mathlib's supremum Rayleigh quotient for a finite real matrix, called the nonzero-vector top Rayleigh value, is given by the matrix's Euclidean linear map. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.coordinateSphereRayleighValue_eq_sphereRayleighValue` | `Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.coordinateSphereRayleighValue A = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A` | With a finite real matrix, the coordinate and Euclidean unit-sphere top Rayleigh values agree. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue_eq_iSupRayleighValue` | `Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.iSupRayleighValue A` | On a nonempty finite coordinate space, a real matrix has its Euclidean unit-sphere top value equal to Mathlib's supremum Rayleigh quotient. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.coordinateSphereRayleighValue_eq_iSupRayleighValue` | `Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.coordinateSphereRayleighValue A = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.iSupRayleighValue A` | On a nonempty finite coordinate space, a real matrix has its coordinate unit-sphere top value equal to Mathlib's supremum Rayleigh quotient. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.exists_unit_isMaxOn_rayleighForm` | `A.IsSymm → ∃ x, ‖x‖ = 1 ∧ IsMaxOn (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A) (Metric.sphere 0 1) x ∧ Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A x = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A` | On a nonempty finite coordinate space, a real symmetric matrix has a unit vector attaining its Euclidean-sphere top Rayleigh value. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.exists_unit_eigenvector_sphereRayleighValue` | `A.IsSymm → ∃ x, ‖x‖ = 1 ∧ A.mulVec x.ofLp = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A • x.ofLp ∧ Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A x = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A` | On a nonempty finite coordinate space, a real symmetric matrix has a unit eigenvector at its Euclidean-sphere top Rayleigh value. |
<!-- /GEN -->

### Absolute-value maximizers

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.AbsoluteValue -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.norm_absVec` | `‖Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x‖ = ‖x‖` | With a Euclidean coordinate vector, coordinatewise absolute value preserves its Euclidean norm. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec_nonneg` | `0 ≤ (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x).ofLp i` | With a Euclidean coordinate vector and a coordinate, the corresponding coordinatewise absolute value is nonnegative. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm_le_absVec` | `(∀ (i j : ι), 0 ≤ A i j) → ∀ (x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι), Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A x ≤ Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x)` | An entrywise nonnegative finite real matrix and a Euclidean coordinate vector satisfy that taking coordinatewise absolute values cannot lower the Rayleigh form. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec_mem_sphere` | `x ∈ Metric.sphere 0 r → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x ∈ Metric.sphere 0 r` | A radius and a Euclidean coordinate vector on the sphere of that radius satisfy that coordinatewise absolute value remains on the same sphere. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm_absVec_eq_of_isMaxOn` | `(∀ (i j : ι), 0 ≤ A i j) → ∀ {x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι}, x ∈ Metric.sphere 0 1 → IsMaxOn (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A) (Metric.sphere 0 1) x → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x) = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A x` | An entrywise nonnegative finite real matrix, a unit-sphere vector, and its Rayleigh-form maximality ensure that taking coordinatewise absolute values preserves the Rayleigh-form value. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec_isMaxOn` | `(∀ (i j : ι), 0 ≤ A i j) → ∀ {x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι}, x ∈ Metric.sphere 0 1 → IsMaxOn (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A) (Metric.sphere 0 1) x → IsMaxOn (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A) (Metric.sphere 0 1) (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x)` | An entrywise nonnegative finite real matrix, a unit-sphere vector, and its Rayleigh-form maximality ensure that coordinatewise absolute value is another unit-sphere maximizer. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec_eigenvector_of_isMaxOn` | `A.IsSymm → (∀ (i j : ι), 0 ≤ A i j) → ∀ {x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι}, x ∈ Metric.sphere 0 1 → IsMaxOn (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A) (Metric.sphere 0 1) x → A.mulVec (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x).ofLp = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A • (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x).ofLp` | On a nonempty finite coordinate space, an entrywise nonnegative symmetric real matrix, a unit-sphere vector, and its Rayleigh-form maximality ensure that the coordinatewise absolute vector is an eigenvector at the top Rayleigh value. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec_preserves_top_eigenvector` | `A.IsSymm → (∀ (i j : ι), 0 ≤ A i j) → ∀ {x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι}, ‖x‖ = 1 → A.mulVec x.ofLp = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A • x.ofLp → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A x = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A → ‖Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x‖ = 1 ∧ (∀ (i : ι), 0 ≤ (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x).ofLp i) ∧ Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x) = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A ∧ A.mulVec (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x).ofLp = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A • (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec x).ofLp` | On a nonempty finite coordinate space, an entrywise nonnegative symmetric real matrix and a normalized top eigenvector ensure that coordinatewise absolute value is a normalized nonnegative top eigenvector with the same top value. |
<!-- /GEN -->

### Irreducible positivity

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Positivity -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zero_coordinate_propagates_across_positive_entry` | `(∀ (i j : ι), 0 ≤ A i j) → ∀ {x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι}, (∀ (i : ι), 0 ≤ x.ofLp i) → ∀ {ρ : ℝ}, A.mulVec x.ofLp = ρ • x.ofLp → ∀ {i j : ι}, x.ofLp i = 0 → 0 < A i j → x.ofLp j = 0` | An entrywise nonnegative matrix, a nonnegative eigenvector, a row coordinate where it vanishes, and a strictly positive matrix entry from that row ensure that the eigenvector also vanishes at the entry’s target coordinate. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.IsIrreducible.eigenvector_pos` | `A.IsIrreducible → ∀ {x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι}, (∀ (i : ι), 0 ≤ x.ofLp i) → x ≠ 0 → ∀ {ρ : ℝ}, A.mulVec x.ofLp = ρ • x.ofLp → ∀ (i : ι), 0 < x.ofLp i` | An irreducible finite matrix and a nonnegative nonzero eigenvector ensure that every coordinate is strictly positive. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.IsIrreducible.unit_eigenvector_pos` | `A.IsIrreducible → ∀ {x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι}, (∀ (i : ι), 0 ≤ x.ofLp i) → ‖x‖ = 1 → ∀ {ρ : ℝ}, A.mulVec x.ofLp = ρ • x.ofLp → ∀ (i : ι), 0 < x.ofLp i` | An irreducible finite matrix and a normalized nonnegative eigenvector ensure that every coordinate is strictly positive. |
<!-- /GEN -->

### Restriction and zero extension

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Restriction -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix` | `Matrix ι ι ℝ → (s : Finset ι) → Matrix ↥s ↥s ℝ` | The principal submatrix of a finite real matrix on a finite set of coordinates, called its restricted matrix, is given by selecting those rows and columns. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictVec` | `(s : Finset ι) → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ↥s` | The Euclidean vector obtained by restricting a finite real vector to a finite coordinate set, called its restricted vector, is given by retaining those coordinates. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec` | `(s : Finset ι) → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ↥s → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ι` | The Euclidean vector obtained by extending a vector on a finite coordinate subtype by zero outside that finite coordinate set, called its zero extension, is given coordinate by coordinate. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendMatrix` | `(s : Finset ι) → Matrix ↥s ↥s ℝ → Matrix ι ι ℝ` | The matrix obtained by extending a matrix on a finite coordinate subtype by zero outside that coordinate set, called its zero extension, is given entry by entry. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictVec_zeroExtendVec` | `Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictVec s (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s x) = x` | A finite coordinate set and a vector on its subtype satisfy that restricting its zero extension recovers the original subtype vector. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.norm_zeroExtendVec` | `‖Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s x‖ = ‖x‖` | A finite coordinate set and a vector on its subtype satisfy that zero extension preserves Euclidean norm. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendMatrix_mulVec_zeroExtendVec` | `(Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendMatrix s B).mulVec (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s x).ofLp = (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s (WithLp.toLp 2 (B.mulVec x.ofLp))).ofLp` | A finite coordinate set, a subtype matrix, and a subtype vector satisfy that applying the zero-extended matrix to the zero-extended vector equals the zero extension of the subtype action. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm_zeroExtendMatrix_zeroExtendVec` | `Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendMatrix s B) (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s x) = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm B x` | A finite coordinate set, a subtype matrix, and a subtype vector satisfy that zero extension preserves their Rayleigh form. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue_zeroExtendMatrix` | `(∀ (i j : ↥s), 0 ≤ B i j) → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendMatrix s B) = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue B` | On a nonempty finite coordinate space, a nonempty finite coordinate set and an entrywise nonnegative subtype matrix satisfy that zero extension preserves its top Rayleigh value. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix_isSymm` | `A.IsSymm → ∀ (s : Finset ι), (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s).IsSymm` | A symmetric finite matrix and a finite coordinate set ensure that the principal restricted matrix remains symmetric. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix_nonneg` | `(∀ (i j : ι), 0 ≤ A i j) → ∀ (s : Finset ι) (i j : ↥s), 0 ≤ Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s i j` | An entrywise nonnegative finite matrix and a finite coordinate set ensure that the principal restricted matrix remains entrywise nonnegative. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix_mulVec_restrictVec_of_zero_off` | `(∀ i ∉ s, x.ofLp i = 0) → (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s).mulVec (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictVec s x).ofLp = (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictVec s (WithLp.toLp 2 (A.mulVec x.ofLp))).ofLp` | A finite matrix, a finite coordinate set, and a vector that vanishes outside the set ensure that restriction commutes with applying the matrix. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.mulVec_zeroExtendVec_of_closed` | `(∀ (i j : ι), i ∉ s → j ∈ s → A i j = 0) → ∀ (x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ↥s), A.mulVec (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s x).ofLp = (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s (WithLp.toLp 2 ((Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s).mulVec x.ofLp))).ofLp` | A finite matrix, a finite coordinate set, and block closure from outside rows into the set ensure that applying the original matrix to a zero extension equals the zero extension of the restricted action. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec_eigenvector_of_closed` | `(∀ (i j : ι), i ∉ s → j ∈ s → A i j = 0) → ∀ {x : Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.EVec ↥s} {ρ : ℝ}, (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s).mulVec x.ofLp = ρ • x.ofLp → A.mulVec (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s x).ofLp = ρ • (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s x).ofLp` | A finite matrix, a finite coordinate set, block closure from outside rows into the set, and a restricted eigen-equation ensure that zero extension satisfies the corresponding global eigen-equation. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm_restrictVec_of_zero_off` | `(∀ i ∉ s, x.ofLp i = 0) → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s) (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictVec s x) = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A x` | A finite matrix, a finite coordinate set, and a vector that vanishes outside that set ensure that restriction preserves its Rayleigh form. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue_restrictMatrix_le` | `Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s) ≤ Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A` | On a nonempty finite coordinate space, a finite matrix and a nonempty finite coordinate set satisfy that the restricted top Rayleigh value is at most the global top Rayleigh value. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue_restrictMatrix_eq_of_supported_maximizer` | `‖x‖ = 1 → (∀ i ∉ s, x.ofLp i = 0) → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A x = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A → Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s) = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A` | On a nonempty finite coordinate space, a finite matrix, a nonempty finite coordinate set, and a global unit maximizer supported on that set ensure that the restricted and global top Rayleigh values agree. |
<!-- /GEN -->

### Perron--Frobenius theorem

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Main -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.finite_positive_perron_eigenvector` | `A.IsSymm → A.IsIrreducible → ∃ v ρ, ‖v‖ = 1 ∧ (∀ (i : ι), 0 < v.ofLp i) ∧ A.mulVec v.ofLp = ρ • v.ofLp ∧ Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.rayleighForm A v = ρ ∧ ρ = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue A ∧ ρ = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.coordinateSphereRayleighValue A ∧ ρ = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.iSupRayleighValue A` | A real symmetric irreducible finite matrix has a strictly positive unit eigenvector whose eigenvalue is simultaneously the coordinate-sphere, Euclidean-sphere, and nonzero-vector top Rayleigh value. |
| `Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.finite_positive_perron_eigenvector_on_restriction` | `A.IsSymm → ∀ (s : Finset ι) [Nonempty ↥s], (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s).IsIrreducible → (∀ (i j : ι), i ∉ s → j ∈ s → A i j = 0) → ∃ v ρ, ‖v‖ = 1 ∧ (∀ (i : ↥s), 0 < v.ofLp i) ∧ (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s).mulVec v.ofLp = ρ • v.ofLp ∧ A.mulVec (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s v).ofLp = ρ • (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.zeroExtendVec s v).ofLp ∧ ρ = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s) ∧ ρ = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.coordinateSphereRayleighValue (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s) ∧ ρ = Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.iSupRayleighValue (Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.restrictMatrix A s)` | A symmetric finite matrix, a nonempty finite coordinate set, an irreducible restricted block, and block closure from outside rows into that set ensure that the block’s strictly positive unit Perron vector zero-extends to a global eigenvector. |
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

<!-- GEN:Causalean.Mathlib.Algorithms.MonotoneWindowDeque -->
_(no documented declarations in Causalean.Mathlib.Algorithms.MonotoneWindowDeque)_
<!-- /GEN -->

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
| `Graph.FiniteDensity.UnitCubeFactorization.instIsFiniteMeasureUnitCubeObservational` | `MeasureTheory.IsFiniteMeasure ((Causalean.Graph.FiniteDensity.unitCubeReference V).withDensity (Causalean.Graph.FiniteDensity.Factorization.observationalDensity B))` | The unit-cube observational density associated with a unit-cube factorization induces a finite measure when combined with the unit-cube reference measure. |
| `Graph.FiniteDensity.UnitCubeFactorization.orderedLocalMarkov_unitCubeReference` | `∀ A ⊆ Causalean.Graph.FiniteDensity.predecessors τ i, G.parents i ⊆ A → ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (Causalean.Graph.FiniteDensity.coordinateProjection A) inferInstance) (Causalean.Graph.FiniteDensity.coordinateConditioning_comap_le A) (fun x => x i) (Causalean.Graph.FiniteDensity.coordinateProjection (Causalean.Graph.FiniteDensity.predecessors τ i \ A)) ((Causalean.Graph.FiniteDensity.unitCubeReference V).withDensity (Causalean.Graph.FiniteDensity.Factorization.observationalDensity B))` | For a unit-cube DAG density factorization, an arbitrary topological ranking, a vertex, a conditioning predecessor set, and proof that it lies among the predecessors and contains every parent, the vertex is conditionally independent of all remaining predecessors given that set under the unit-cube reference measure. |
<!-- /GEN -->

### `Mathlib/CondIndep/ThreeBlockDensity.lean`

The generic three-block density argument is collected with conditional-independence infrastructure because it is independent of DAGs and coordinates.

<!-- GEN:Causalean.Mathlib.CondIndep.ThreeBlockDensity -->
| Decl | Signature | Description |
|---|---|---|
| `condIndepFun_threeBlock_of_density_factors` | `Measurable d → ∀ [inst_9 : MeasureTheory.IsFiniteMeasure ((muY.prod (muZ.prod muC)).withDensity d)] (a : Y × C → ENNReal) (b : Z × C → ENNReal), Measurable a → Measurable b → (d =ᵐ[muY.prod (muZ.prod muC)] fun q => a (q.1, q.2.2) * b (q.2.1, q.2.2)) → ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (fun q => q.2.2) inferInstance) (Measurable.comap_le (Measurable.comp measurable_snd measurable_snd)) (fun q => q.1) (fun q => q.2.1) ((muY.prod (muZ.prod muC)).withDensity d)` | For three coordinate reference measures, a measurable finite joint density, first and second block factors, measurability of those factors, and their almost-everywhere product representation, the first and second coordinate maps are conditionally independent given the third coordinate. |
<!-- /GEN -->

### `Mathlib/CondIndep/DomainTransport/AeRetraction.lean`

This module extends conditional-independence transport from genuine measurable equivalences to
measurable retractions that are inverse only almost everywhere under the corresponding finite
measures. Its primary result transports conditional independence of two measurable random
variables given a third between an ambient space and a non-surjectively embedded full-measure
support.

<!-- GEN:Causalean.Mathlib.CondIndep.DomainTransport.AeRetraction -->
| Decl | Signature | Description |
|---|---|---|
| `eventuallyEq_of_comp_aeRetraction` | `Measurable s → ∀ {μ : MeasureTheory.Measure Ω} {μ' : MeasureTheory.Measure Ω'}, MeasureTheory.Measure.map s μ' = μ → r ∘ s =ᵐ[μ'] id → ∀ {f g : Ω' → A}, f ∘ r =ᵐ[μ] g ∘ r → f =ᵐ[μ'] g` | With a source-to-target map, a measurable return map, the return-map pushforward identity, an almost-everywhere right-inverse identity, and an equality after pullback, the target functions agree almost everywhere. |
| `condExp_comp_of_map_eq` | `Measurable r → ∀ {μ : MeasureTheory.Measure Ω} {μ' : MeasureTheory.Measure Ω'} [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure μ'], MeasureTheory.Measure.map r μ = μ' → ∀ m ≤ mΩ', ∀ {f : Ω' → E}, MeasureTheory.Integrable f μ' → μ[f ∘ r \| MeasurableSpace.comap r m] =ᵐ[μ] μ'[f \| m] ∘ r` | With a measurable source-to-target map, its pushforward identity, a target conditioning σ-algebra contained in the ambient σ-algebra, and an integrable target outcome, conditional expectation commutes almost everywhere with pullback along the map. |
| `condExpInd_preimage_of_map_eq` | `Measurable r → ∀ {μ : MeasureTheory.Measure Ω} {μ' : MeasureTheory.Measure Ω'} [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure μ'], MeasureTheory.Measure.map r μ = μ' → ∀ m ≤ mΩ', ∀ {t : Set Ω'}, MeasurableSet t → μ[(r ⁻¹' t).indicator fun x => 1 \| MeasurableSpace.comap r m] =ᵐ[μ] μ'[t.indicator fun x => 1 \| m] ∘ r` | With a measurable source-to-target map, its pushforward identity, a target conditioning σ-algebra contained in the ambient σ-algebra, and a measurable target event, the event's conditional probability commutes almost everywhere with pullback along the map. |
| `condIndep_comap_of_map_eq` | `MeasureTheory.Measure.map r μ = μ' → ∀ (mX mY mZ : MeasurableSpace Ω'), mX ≤ mΩ' → mY ≤ mΩ' → ∀ (hZ : mZ ≤ mΩ'), ProbabilityTheory.CondIndep mZ mX mY hZ μ' → ProbabilityTheory.CondIndep (MeasurableSpace.comap r mZ) (MeasurableSpace.comap r mX) (MeasurableSpace.comap r mY) (LE.le.trans (MeasurableSpace.comap_mono hZ) (Measurable.comap_le hr)) μ` | With a measurable source-to-target map, its pushforward identity, three target σ-algebras contained in the target ambient σ-algebra, conditional independence on the target pulls back to conditional independence on the source. |
| `condIndep_of_comap_aeRetraction` | `Measurable s → ∀ {μ : MeasureTheory.Measure Ω} {μ' : MeasureTheory.Measure Ω'} [inst_2 : MeasureTheory.IsFiniteMeasure μ] [inst_3 : MeasureTheory.IsFiniteMeasure μ'], MeasureTheory.Measure.map r μ = μ' → MeasureTheory.Measure.map s μ' = μ → r ∘ s =ᵐ[μ'] id → ∀ (mX mY mZ : MeasurableSpace Ω'), mX ≤ mΩ' → mY ≤ mΩ' → ∀ (hZ : mZ ≤ mΩ'), ProbabilityTheory.CondIndep (MeasurableSpace.comap r mZ) (MeasurableSpace.comap r mX) (MeasurableSpace.comap r mY) (LE.le.trans (MeasurableSpace.comap_mono hZ) (Measurable.comap_le hr)) μ → ProbabilityTheory.CondIndep mZ mX mY hZ μ'` | With measurable maps in both directions, their two pushforward identities, an almost-everywhere right inverse, and three target σ-algebras contained in the target ambient σ-algebra, conditional independence of the three pullback σ-algebras implies target conditional independence. |
| `condIndep_comap_aeEquiv_iff` | `Measurable s → ∀ {μ : MeasureTheory.Measure Ω} {μ' : MeasureTheory.Measure Ω'} [inst_2 : MeasureTheory.IsFiniteMeasure μ] [inst_3 : MeasureTheory.IsFiniteMeasure μ'], MeasureTheory.Measure.map r μ = μ' → MeasureTheory.Measure.map s μ' = μ → s ∘ r =ᵐ[μ] id → r ∘ s =ᵐ[μ'] id → ∀ (mX mY mZ : MeasurableSpace Ω'), mX ≤ mΩ' → mY ≤ mΩ' → ∀ (hZ : mZ ≤ mΩ'), ProbabilityTheory.CondIndep (MeasurableSpace.comap r mZ) (MeasurableSpace.comap r mX) (MeasurableSpace.comap r mY) (LE.le.trans (MeasurableSpace.comap_mono hZ) (Measurable.comap_le hr)) μ ↔ ProbabilityTheory.CondIndep mZ mX mY hZ μ'` | With measurable maps in both directions, their two pushforward identities, almost-everywhere inverse identities in both directions, and three target σ-algebras contained in the target ambient σ-algebra, target conditional independence is equivalent to conditional independence of the three pullback σ-algebras. |
| `condIndepFun_comp_aeEquiv_iff` | `Measurable s → ∀ {μ : MeasureTheory.Measure Ω} {μ' : MeasureTheory.Measure Ω'} [inst_5 : MeasureTheory.IsFiniteMeasure μ] [inst_6 : MeasureTheory.IsFiniteMeasure μ'], MeasureTheory.Measure.map r μ = μ' → MeasureTheory.Measure.map s μ' = μ → s ∘ r =ᵐ[μ] id → r ∘ s =ᵐ[μ'] id → ∀ (X : Ω' → 𝒳) (Y : Ω' → 𝒴) (Z : Ω' → 𝒵), Measurable X → Measurable Y → ∀ (hZ : Measurable Z), ProbabilityTheory.CondIndepFun (MeasurableSpace.comap (Z ∘ r) inferInstance) (Measurable.comap_le (Measurable.comp hZ hr)) (X ∘ r) (Y ∘ r) μ ↔ ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ) X Y μ'` | With measurable maps in both directions, their two pushforward identities, almost-everywhere inverse identities in both directions, three target random variables, and their measurability, conditional independence of the first two variables given the third is equivalent to conditional independence of their pullbacks given the pulled-back third variable. |
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

**Why monolithic.**  An iterated single-target form would produce parent sets
that agree with the base graph only *propositionally* at non-targeted vertices,
blocking `rfl`-level reductions in the cross-SCM bridge
`SCM/Do/Rule3.lean:fixSet_evalMap_nonAnc_compat`.
Under the monolithic form, parent sets at non-`.fixed`-targeted vertices
coincide with the base graph's parents *definitionally* (modulo a direct
`splitMono_parents_eq_of_no_fixed_parent` rewrite), which is exactly the
hypothesis of the Rule 3 non-ancestor bridge.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SWIGGraph.splitMonoEdgeRel` | `(_ : SWIGNode N → SWIGNode N → Prop) → Finset N → SWIGNode N → SWIGNode N → Prop` | Edge relation after monolithic split: for each `D ∈ X`, outgoing edges of `.random D` are rerouted to `.fixed D`; all other edges pass through unchanged | Defined |
| `SWIGGraph.splitMonoTopo` | `SWIGGraph N → Finset N → SWIGNode N → ℕ` | Topological order for the monolithic split: `.fixed D` (`D ∈ X`) gets even value `2 · topoOrder (.random D)`; all others get odd values; even/odd separation guarantees injectivity | Defined |
| `SWIGGraph.splitMonoDAG` | `SWIGGraph N → (X : Finset N) → (hIso : ∀ D ∈ X, parents (.fixed D) = ∅) → DAG (SWIGNode N)` | DAG on `SWIGNode N` after monolithic split, built from `splitMonoEdgeRel` and `splitMonoTopo` | Defined |
| `SWIGGraph.splitMono G X hObs hFix` | `SWIGGraph N` | Monolithic multi-target split: applies `splitMonoDAG`; preserves `observed`, `unobserved`; enlarges `fixed` by `X.image SWIGNode.fixed` | Defined |
| `SWIGGraph.splitMono_observed` *(@[simp])* | `(G.splitMono X _ _).observed = G.observed` | Monolithic split preserves the observed node set | `rfl` |
| `SWIGGraph.splitMono_unobserved` *(@[simp])* | `(G.splitMono X _ _).unobserved = G.unobserved` | Monolithic split preserves the unobserved node set | `rfl` |
| `SWIGGraph.splitMono_fixed` *(@[simp])* | `(G.splitMono X _ _).fixed = G.fixed ∪ X.image SWIGNode.fixed` | Fixed set after monolithic split is the original fixed set union the image of `X` under `.fixed` | `rfl` |
| `SWIGGraph.splitMono_parents_char` | `x ∈ (G.splitMono X _ _).dag.parents v ↔ (x ∈ G.dag.parents v ∧ ∀ D ∈ X, x ≠ SWIGNode.random D) ∨ (∃ D ∈ X, x = SWIGNode.fixed D ∧ SWIGNode.random D ∈ G.dag.parents v)` | Characterizes parents in the split graph: either a non-targeted original parent, or a new `.fixed D` replacing `.random D` | **Proved** |
| `SWIGGraph.splitMono_parents_eq_of_no_fixed_parent` | `(∀ D ∈ X, SWIGNode.fixed D ∉ (G.splitMono X _ _).dag.parents v) → (G.splitMono X _ _).dag.parents v = G.dag.parents v` | Parent-set coincidence at non-`.fixed`-targeted vertices; key prerequisite for the Rule 3 non-ancestor `evalMap` bridge | **Proved** |

Reference: Basic Concepts.tex, Definition 8 (multi-target generalized intervention).

---

## 4. `Graph/CComponents.lean` — C-Components (on SWIGGraph)

C-components are defined on `SWIGGraph`, matching Definition 5 from the tex:
"The fixed nodes S play no role in this definition."

### Confounding

| Definition | Signature | Description |
|---|---|---|
| `SWIGGraph.directlyConfounded` | `(v₁ v₂ : SWIGNode N) → Prop` | Share an unobserved parent; decidable |
| `SWIGGraph.bidirectedNeighbors` | `(v : SWIGNode N) → Finset (SWIGNode N)` | All observed variables directly confounded with `v` |
| `SWIGGraph.bidirectedReachable` | `SWIGNode N → SWIGNode N → Prop` (inductive) | Transitive closure of directly confounded |

### C-component computation

| Definition | Signature | Description |
|---|---|---|
| `SWIGGraph.bidirectedBFS` | `(start : SWIGNode N) → Finset (SWIGNode N)` | BFS on bidirected projection |
| `SWIGGraph.cComponentOf` | `(v : SWIGNode N) → Finset (SWIGNode N)` | C-component containing `v` |
| `SWIGGraph.cComponents` | `Array (Finset (SWIGNode N))` (noncomputable) | All C-components (ordered) |
| `SWIGGraph.cComponentSet` | `Finset (Finset (SWIGNode N))` (noncomputable) | All C-components as `observed.image cComponentOf` — the canonical, order-independent partition index used by `c_component_factorization` |

### Partition / reachability results (all proven, axiom-clean)

| Result | Statement | Status |
|---|---|---|
| `bidirectedReachable_symm` / `_trans` / `_head` / `_observed_left` / `_observed_right` | bidirected reachability is an equivalence relation on `observed` | **Proved** |
| `mem_bidirectedBFS_iff_reachable` | `w ∈ cComponentOf start ↔ bidirectedReachable start w` (BFS correctness: the fuel-bounded search computes exactly the bidirected-reachable set) | **Proved** (fuel-saturation closure) |
| `cComponentSet_biUnion` | `cComponentSet.biUnion id = observed` — the c-components cover the observed nodes | **Proved** |
| `cComponentSet_pairwise_disjoint` | distinct c-components are disjoint | **Proved** |
| `cComponentSet_subset_observed`, `cComponentOf_subset_observed`, `mem_cComponentOf_self` | each component ⊆ observed; every observed node is in its own component | **Proved** |

**Usage:**

```lean
-- D and Y are in the same C-component (confounded via U)
example : SWIGNode.random Y ∈ ivSWIGGraph.cComponentOf (SWIGNode.random D) := by native_decide

-- Z is in its own singleton C-component
example : ivSWIGGraph.cComponentOf (SWIGNode.random Z) = {SWIGNode.random Z} := by native_decide
```

---

## 4b. `Graph/MarkovEquiv/` — Markov Equivalence of DAGs (Verma–Pearl)

Formalization of the Verma–Pearl (1990) characterization: two DAGs declare the same
d-separations iff they share a skeleton and the same v-structures. Umbrella:
`Graph/MarkovEquiv.lean`. Reuses the d-separation engine (`Graph/DSep/`) and the global
Markov property (`SCM/Do/GlobalMarkov.lean`).

### `Graph/MarkovEquiv/Defs.lean` — core relations

| Declaration | Description |
|---|---|
| `DAG.IsImmorality G a b c` | v-structure (immorality) `a → b ← c`: edges `a→b`, `c→b` with `a,c` non-adjacent and distinct. Decidable. |
| `SameSkeleton G₁ G₂` | the two DAGs have the same undirected adjacency (`UAdj`). Decidable. |
| `SameImmoralities G₁ G₂` | the two DAGs have the same v-structures. Decidable. |
| `MarkovEquiv G₁ G₂` | the two DAGs declare the same d-separations on pairwise-disjoint triples: `∀ X Y Z, Disjoint X Y → Disjoint X Z → Disjoint Y Z → (G₁.dSep X Y Z ↔ G₂.dSep X Y Z)` (the standard conditional-independence setting). |
| `MarkovEquiv.refl/symm/trans` | `MarkovEquiv` is an equivalence relation. |

### `Graph/MarkovEquiv/Readoff.lean` — easy direction (read off d-sep)

| Declaration | Description |
|---|---|
| `DAG.not_dSeparable_of_uAdj` | adjacent vertices are not d-separated by any conditioning set (the edge is an always-active path). |
| `DAG.dSeparable_of_not_uAdj` | non-adjacent vertices are d-separated by some set (the parents of the topologically later one). |
| `DAG.adjacent_iff_not_dSeparable` | skeleton read-off: `UAdj a b ↔ ¬ ∃ Z, dSep {a} {b} Z`. |
| `DAG.immorality_iff_colliderSep` | collider read-off: for an unshielded triple, `a→b←c` is a v-structure iff `b` is in no separating set of `a,c` (the PC-algorithm rule). |
| `DAG.immorality_iff_colliderSep_disjoint` | endpoint-disjoint collider read-off: same, restricted to separators containing `b` and excluding `a,c` (the form transported across Markov-equivalent graphs). |
| `DAG.dSeparable_disjoint_of_not_uAdj` | non-adjacent distinct vertices are d-separated by a set disjoint from both (parents of the topologically later one). |
| `DAG.not_edge_self`, `DAG.not_uAdj_self` | no self-loops / self-adjacency in a DAG. |
| `sameSkeleton_of_markovEquiv` | Markov equivalence ⇒ same skeleton. |
| `sameImmoralities_of_markovEquiv` | Markov equivalence ⇒ same v-structures. |
| `sameSkeleton_sameImmoralities_of_markovEquiv` | easy direction of Verma–Pearl (both at once). |

### `Graph/MarkovEquiv/Moralization.lean` — moral graph + moralization criterion

| Declaration | Description |
|---|---|
| `DAG.MoralAdj G S u v` | moral adjacency inside a ground set `S`: distinct `u,v ∈ S` that are skeleton-adjacent (`UAdj`) or share a common child inside `S` ("married parents"). |
| `DAG.MoralStep G S Z u v` | one moral step inside `S` with both endpoints outside the conditioning set `Z`. |
| `DAG.MoralConn G S Z u v` | moral connectivity: a (reflexive-transitive) chain of moral steps inside `S` avoiding `Z`. |
| `DAG.MoralSep G X Y Z` | moral separation: no `x ∈ X` is moral-connected to any `y ∈ Y` inside `An(X∪Y∪Z)` while avoiding `Z`. |
| `DAG.moralAdj_symm` | moral adjacency is symmetric. |
| `DAG.dSep_iff_moralSep` | **the criterion** (Lauritzen–Dawid–Larsen–Speed): for pairwise-disjoint `X,Y,Z`, d-separation equals moral separation in the ancestral set. |
| `moralAdj_congr` | moral adjacency is a skeleton + v-structure invariant for any fixed ground set `S`. |
| `moralStep_congr`, `moralConn_congr` | moral steps / connectivity agree across same-skeleton + same-immorality DAGs, **for a fixed ground set**. |

### `Graph/MarkovEquiv/Transfer.lean` — hard direction (via covered-edge reversals)

| Declaration | Description |
|---|---|
| `markovEquiv_of_sameSkeleton_sameImmoralities` | same skeleton + same v-structures ⇒ Markov equivalent. The proof uses the AMP covered-edge route: same-skeleton/same-immorality DAGs differ by covered-edge reversals, and each reversal preserves every d-separation. |

### `Graph/MarkovEquiv.lean` — umbrella + flagship

| Declaration | Description |
|---|---|
| `markovEquiv_iff_sameSkeleton_sameImmoralities` | **Flagship (Verma–Pearl).** Two DAGs are Markov equivalent iff they have the same skeleton and the same v-structures. Both directions are proved through the read-off and covered-edge reversal routes. |

### `Graph/MarkovEquiv/Distributional.lean` — distributional layer

| Declaration | Description |
|---|---|
| `SCM.IsGlobalIMap G M μ` | the measure `μ` is a global I-map of DAG `G`: every d-separation of `G` (on disjoint `X,Y,Z`) is a conditional independence of `μ`. |
| `SCM.IsFaithful G M μ` | converse: every conditional independence of `μ` reflects a d-separation of `G`. |
| `SCM.DistMarkovEquiv Ω G₁ G₂` | the two DAGs are global I-maps of exactly the same distributions (over value spaces `Ω`). |
| `SCM.isGlobalIMap_dag_self` | the bridge, restated: every SCM is a global I-map of its own DAG (= `full_globalMarkov`). |
| `SCM.distMarkovEquiv_of_markovEquiv` | easy half: graph-level Markov equivalence ⇒ distributional Markov equivalence. The abandoned faithfulness-existence converse is no longer part of the public module. |

---

## 5. `SCM/Model/EdgeType.lean` — Edge Type Hierarchy

### Inductive: `MonotonicityKind`

```
nonDecreasing | nonIncreasing | strictlyIncreasing | strictlyDecreasing
```

### Inductive: `EdgeType`

```
nonparametric | monotonic (kind : MonotonicityKind) | linear | parametric
```

### Refinement relation

| Definition | Signature | Description |
|---|---|---|
| `EdgeType.refinesBool` | `EdgeType → EdgeType → Bool` | Computable refinement check |
| `EdgeType.refines` | `EdgeType → EdgeType → Prop` | `e₁.refinesBool e₂ = true` |
| `EdgeType.decRefines` | `Decidable (e₁.refines e₂)` | Decidability instance |

### Structure: `EdgeTypeAssignment G`

| Field | Type | Description |
|---|---|---|
| `edgeType` | `V → V → EdgeType` | Type of each edge (meaningful when `G.edge u v`) |

---

## 6. `SCM/Model/SCM.lean` — Generalized Structural Causal Model (Definition `def:scm`)

### Structure: `SCM N Ω`

A generalized structural causal model (gSCM) extending `SWIGGraph N` with
deterministic structural functions per observed node and one probability
measure per latent root. Randomness lives only in the latent roots; the
joint / observational kernels are derived via the evaluation map (see
`SCM/Model/Evaluation.lean`, `SCM/Model/Kernel.lean`).

#### Value-space infrastructure (file-local, shared with the rest of the SCM stack)

| Definition | Signature | Description |
|---|---|---|
| `ValuesOn I Ω` | `Finset M → (M → Type*) → Type*` | Dependent product of value spaces over a finite index set |
| `valuesProjection hJI` | `ValuesOn I Ω → ValuesOn J Ω` | Restrict an indexed assignment to a subset `J ⊆ I` |
| `coordinateFamily I` | `∀ i : {i // i ∈ I}, ValuesOn I Ω → Ω i.val` | Coordinate family on `ValuesOn I Ω` |
| `valuesEquivOfEq h` | `ValuesOn I Ω ≃ᵐ ValuesOn J Ω` (where `h : I = J`) | `MeasurableEquiv` canonical transport along an index-`Finset` equality; `toFun` is `valuesProjection (le_of_eq h.symm)` so call sites can rewrite the projection into the equiv by `rfl` |
| `measurePreserving_valuesEquivOfEq h μ` | `MeasurePreserving (valuesEquivOfEq h) (Measure.pi μ) (Measure.pi μ')` | Companion: `Measure.pi` transports along `valuesEquivOfEq`, with target per-coord measure `μ' j = μ ⟨j.val, h ▸ j.property⟩`.  Proved via `subst h`; collapses the two `Measure.pi`'s to the same source after the substitution |

#### Fields (beyond the `SWIGGraph N` parent)

| Field | Type | Description |
|---|---|---|
| `edgeTypes` | `EdgeTypeAssignment dag` | Edge type assignment, orthogonal to semantics |
| `iota_valueSpace` | `∀ s ∈ fixed, swigΩ Ω s = swigΩ Ω (iotaMap s)` | Matching value spaces `X_d = X_{ι(d)}` |
| `structFun v` | `(∀ w ∈ parents v, swigΩ Ω w) → swigΩ Ω v` | Deterministic structural function per observed node |
| `structFun_measurable` | `∀ v, Measurable (structFun v)` | Each structural map is measurable |
| `latentDist L` | `Measure (swigΩ Ω L)` | One probability measure per latent root `L ∈ U` |
| `isProbability_latent` | `∀ L, IsProbabilityMeasure (latentDist L)` | Total mass 1 on each latent |

#### Derived latent product measure

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.latentProduct` | `Measure (LatentValues M)` | Product measure over all latent roots, `Measure.pi (fun u => latentDist u)` | *(sorry — TODO(evaluation))* |
| `instProbabilityLatentProduct` | `IsProbabilityMeasure latentProduct` | Total-mass-1 instance for `latentProduct` | *(sorry — TODO(evaluation))* |

#### Type aliases and basic definitions

| Name | Expands to / Signature | Description |
|---|---|---|
| `FixedValues M` | `ValuesOn M.fixed (swigΩ Ω)` | Values of intervention nodes |
| `ObservedValues M` | `ValuesOn M.observed (swigΩ Ω)` | Values of observed nodes |
| `LatentValues M` | `ValuesOn M.unobserved (swigΩ Ω)` | Values of latent (unobserved) nodes |
| `UnobservedValues M` | alias of `LatentValues M` | Deprecated alias preserved for compatibility |
| `RandomValues M` | `ValuesOn M.randomVars (swigΩ Ω)` | Values over `V ∪ L` |
| `randomVars M` | `M.observed ∪ M.unobserved` | Index set of non-fixed nodes |
| `isStandard M` | `Prop` | `M.fixed = ∅` — no intervention |
| `not_unobs_of_obs` | `n ∈ observed → n ∉ unobserved` | Disjointness helper |

#### Topological-order utilities

| Name | Signature | Description |
|---|---|---|
| `topoLinearOrder M` | `LinearOrder (SWIGNode N)` | Canonical linear order lifted from `dag.topoOrder` (noncomputable) |
| `observedAt M i` | `Fin observed.card → {v // v ∈ observed}` | `i`-th observed node in canonical topological order |
| `observedIndex M v` | `{v // v ∈ observed} → Fin observed.card` | Canonical index of an observed node |
| `observedAt_observedIndex` | Round-trip equality | `(M.observedAt (M.observedIndex v)).val = v.val` |
| `observed_parent_index_lt` | `edge p (observedAt ⟨n, _⟩) → observedIndex p < ⟨n, _⟩` | Observed parents appear strictly earlier in the prefix |

#### Structural equivalence

| Name | Signature | Description |
|---|---|---|
| `SCM.Equiv M₁ M₂` | `Prop` | Conjunction of `SWIGGraph.Equivalent` on the graph layer, edgewise agreement on `edgeTypes`, and `HEq` on `structFun` / `latentDist` |
| `Equiv.refl` / `.symm` / `.trans` | Equivalence closure | Refl and symm are explicit; trans chains the graph-equivalence |
| `instSetoidSCM` | `Setoid (SCM N Ω)` | Registered setoid for `SCM.Equiv` |

---

## 6a. `SCM/Model/Evaluation.lean` — Evaluation Map (Definition `def:scm-eval`)

Evaluation map `φ_M : FixedValues M × LatentValues M → RandomValues M` computed
by strong recursion along `M.topoLinearOrder` via the helper `evalObservedAux`
(observed nodes) plus a direct latent-root projection. The recursion at each
observed index applies `M.structFun` to a parent tuple assembled by the helper
`parentMap`, which classifies each parent via `M.dag_edges_classified` into
fixed / latent / observed-recursion branches.

`parentMap`, `parentMap_{unobserved,fixed,observed}`, `evalObservedAux`,
`evalObservedAux_eq`, `evalMap_observed`, and `evalMap_unobserved` are exposed
as **non-private** (formerly private) so that `Induced.lean`'s bridge lemma
`induce_evalMap_compat` can reuse them without duplication.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.parentMap` | `(s, ℓ, hn : n < M.observed.card, prev : ∀ m < n, …) → ∀ w ∈ parents (observedAt ⟨n,hn⟩), swigΩ Ω w.val` | One recursion step: given a strong-induction hypothesis `prev` supplying values at every strictly earlier observed index, returns the parent-value tuple to feed into `M.structFun` at the `n`-th observed node. Each parent `w` is classified via `dag_edges_classified` into unobserved (read from `ℓ`), fixed (read from `s`), or observed (recurse through `prev` at the parent's topological index, strictly `< n` by `observed_parent_index_lt`) | **Defined** |
| `SCM.parentMap_unobserved` | `w.val ∈ M.unobserved → parentMap … w = ℓ ⟨w.val, huo⟩` | Branch-unfold lemma: rewrites `parentMap … w` to the latent value `ℓ ⟨w.val, huo⟩` under the hypothesis that `w.val ∈ M.unobserved`. Used coordinate-wise in every downstream structural induction | **Proved** via `dif_pos` |
| `SCM.parentMap_fixed` | `w.val ∉ M.unobserved → w.val ∈ M.fixed → parentMap … w = s ⟨w.val, hfix⟩` | Branch-unfold lemma: rewrites `parentMap … w` to the fixed value `s ⟨w.val, hfix⟩` on the fixed branch. Requires both the negation of the unobserved branch and fixed-membership | **Proved** via `dif_neg`/`dif_pos` |
| `SCM.parentMap_observed` | `w.val ∉ M.unobserved → w.val ∉ M.fixed → w.val ∈ M.observed → parentMap … w = (observedAt_observedIndex) ▸ prev (observedIndex w).val …` | Branch-unfold lemma for the observed-recursion branch: rewrites `parentMap … w` to the transported `prev` value at `w`'s topological index. The `▸` cast moves `swigΩ Ω (observedAt (observedIndex w)).val` to `swigΩ Ω w.val` | **Proved** via `dif_neg`/`dif_neg` |
| `SCM.evalObservedAux` | `(s, ℓ, n : ℕ) → ∀ hn : n < M.observed.card, swigΩ Ω (observedAt ⟨n,hn⟩).val` | Strong-recursive workhorse indexed by the *natural number* `n` (where strong recursion is available) rather than by a Subtype. Returns the value of the `n`-th observed node as `structFun (observedAt ⟨n,hn⟩)` applied to the tuple assembled by `parentMap` from earlier observed values | **Defined** via `Nat.strongRecOn'` |
| `SCM.evalObservedAux_eq` | `evalObservedAux M s ℓ n hn = structFun (observedAt ⟨n,hn⟩) (fun w => parentMap M s ℓ hn (fun m _ hm => evalObservedAux M s ℓ m hm) w)` | Canonical β-reduced unfold equation for `evalObservedAux` at a given `n`. Every proof that does structural induction over the topological order (`evalObservedAux_measurable`, `evalObservedAux_agree_anc`, `evalObservedAux_eq_structFunAt`) starts with a rewrite by this lemma | **Proved** via `Nat.strongRecOn'_beta` |
| `SCM.evalMap_observed` | `w.val ∈ M.observed → evalMap s ℓ w = (observedAt_observedIndex) ▸ evalObservedAux M s ℓ (observedIndex w).val …` | Unfolds `evalMap s ℓ w` on the *observed* branch to a transported `evalObservedAux` value at `observedIndex w`. The `▸` cast along `observedAt_observedIndex : (observedAt (observedIndex w)).val = w.val` brings the type `swigΩ Ω (observedAt (observedIndex w)).val` back to `swigΩ Ω w.val` | **Proved** via `dif_pos` |
| `SCM.evalMap_unobserved` | `w.val ∈ M.unobserved → evalMap s ℓ w = ℓ ⟨w.val, huo⟩` | Unfolds `evalMap s ℓ w` on the *latent* branch to `ℓ ⟨w.val, huo⟩`. Uses `not_obs_of_unobs` to discharge the observed-branch hypothesis of `evalMap`'s definitional `dif_neg` | **Proved** via `dif_neg` |
| `SCM.evalMap` | `FixedValues M → LatentValues M → RandomValues M` | The top-level evaluation map. Pointwise over `w : {w // w ∈ M.randomVars}`: observed branch calls `evalObservedAux` at `observedIndex w` (with `▸` cast); latent branch projects `ℓ` at `w` | **Proved** |
| `SCM.evalMap_measurable` | `Measurable (Function.uncurry M.evalMap)` | Joint measurability of `evalMap` in `(s, ℓ)`, needed to define `jointKernel` in `Kernel.lean`. Proven by structural induction on the observed topological index using the private helper `evalObservedAux_measurable`; relies on `structFun_measurable` and the three `parentMap_*` unfold lemmas | **Proved** |
| `parentDispatch` *(private)* | `(v : {v // v ∈ M.observed}) → (∀ w ∈ parents v.val, swigΩ Ω w.val)` | Named extraction of the three-way if-else parent tuple. Avoids inlining the chain in the helpers below | — |
| `evalObservedAux_eq_structFunAt` *(private)* | `evalObservedAux M s ℓ j.val j.isLt = M.structFun (M.observedAt j) (parentDispatch M s ℓ (M.observedAt j))` for a *free* `j : Fin M.observed.card` | Cast-free intermediate used on the way to `evalMap_observed_unfold`: states `evalObservedAux = structFun ∘ parentDispatch` at a *free* `Fin` index `j`, so no dependent-motive `▸` cast blocks the rewrite | **Proved** — observed-parent branch closes by `rfl` since both `parentMap_observed` and `evalMap_observed` produce the *same* `▸`-form |
| `evalObservedAux_cast_eq_structFunAt` *(private)* | `hcast ▸ evalObservedAux M s ℓ k.val k.isLt = M.structFun (M.observedAt j) (parentDispatch …)` given `(hkj : k = j)` | Cast-navigation helper: lifts the free-index equation above to a pair `(j, k)` of Fin indices with `k = j`, through a `.val`-level cast `hcast` | **Proved.** Uses `subst k` to eliminate the Fin mismatch, then `Subsingleton.elim` to replace the reflexive cast proof with `rfl`, collapsing the `▸` |
| `SCM.evalMap_observed_unfold` | `M.evalMap s ℓ ⟨v.val, _⟩ = M.structFun v (fun w => if-else dispatch with recursive `M.evalMap` on observed parents)` for `v : {v // v ∈ M.observed}` | Cast-free "recursive form" of `M.evalMap` at observed nodes, stated directly in terms of `M.evalMap` on parents rather than `evalObservedAux`. Consumed by `Induced.induce_evalMap_compat` as a black box | **Proved (Layer 4).** Uses a `suffices` with `subst hw` to eliminate the circular `v ↔ M.observedIndex v` dependency, then the cast-navigation helper above |
| `SCM.ancestralFactorization` | `∀ (T : Finset (SWIGNode N)), T ⊆ M.observed → (s, s', ℓ, ℓ' agree on fixed/latent ancestors of T via `DAG.isAncestor`) → ∀ v ∈ T, evalMap s ℓ v = evalMap s' ℓ' v` | Congruence form of `lem:scm-ancestral-factor`: `evalMap` at any `v ∈ T` depends on `(s, ℓ)` only through the fixed/latent ancestors of `T`. Uses the inductive `DAG.isAncestor` directly (the Finset `DAG.ancestorsSet` is sorry-tainted via `decIsAncestor`) | **Proved (Layer 4).** Strong recursion via the private helper `evalObservedAux_agree_anc` on the topological index, chaining ancestor witnesses through `isAncestor.edge` + `isAncestor_trans` at each parent branch |
| `SCM.observedIndex_observedAt` | `M.observedIndex (M.observedAt k) = k` for `k : Fin M.observed.card` | Round-trip lemma companion to `observedAt_observedIndex`; needed to collapse `observedIndex` after destructuring through the topological enumeration | **Proved (Layer 4)** via the `orderIsoOfFin` round-trip |
| `SCM.evalMap_topo_indep` | `True` | Placeholder for `prop:scm-evalmap` (independence of `evalMap` from the choice of topological extension). Downstream (`GlobalMarkov`, `DoCalculus`) only depends on the canonical `evalMap` tied to `M.topoLinearOrder`, so the refactor is safely deferred | *(deferred, Layer 5+)* — requires first refactoring `evalMap` to take an explicit linear extension of `M.dag` |

*Factorization lemmas (§5–§6) are in `EvalFactorization.lean`; latent-restricted factorization (§7) is in `EvalLatent.lean`; cross-SCM transport (§8) is in `EquivKernel.lean`.*

---

## 6a'. `SCM/Model/EvalFactorization.lean` — Parent and Ancestor Factorization

Imports `Evaluation.lean`. Provides two families of factorization theorems for `evalMap`:
* §5 — **parent factorization**: the value at an observed node depends on latents only through parent-restricted random coordinates. Consumed by `LocalMarkov`.
* §6 — **ancestor factorization** (existence form): upgrades `ancestralFactorization` to a two-argument curried `g` form needed by `CondIndepFun` machinery in `GlobalMarkov`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.evalMap_factors_through_parents` | `∀ v ∈ M.observed, ∃ g : ValuesOn (parents v ∩ randomVars) (swigΩ Ω) → swigΩ Ω v, Measurable g ∧ ∀ ℓ, evalMap s ℓ ⟨v,_⟩ = g (valuesProjection _ (evalMap s ℓ))` | Parent factorization: `(evalMap s ℓ) v` is a measurable function of parent-restricted random coordinates. Witness `g` applies `structFun v` to parents read from `s` (fixed) or the projection (random). Consumed by `LocalMarkov` | **Proved** |
| `SCM.latentAncestorsOfNode` | `SCM N Ω → SWIGNode N → Finset (SWIGNode N)` | `{u ∈ M.unobserved ∣ u = v ∨ M.dag.isAncestor u v}`, using `Classical.decPred` to avoid `decIsAncestor` | **Defined** |
| `SCM.fixedAncestorsOfNode` | `SCM N Ω → SWIGNode N → Finset (SWIGNode N)` | `{d ∈ M.fixed ∣ d = v ∨ M.dag.isAncestor d v}`, analogous to `latentAncestorsOfNode` | **Defined** |
| `SCM.mem_latentAncestorsOfNode` | `u ∈ M.latentAncestorsOfNode v ↔ u ∈ M.unobserved ∧ (u = v ∨ isAncestor u v)` | Membership characterisation for `latentAncestorsOfNode` | **Proved** |
| `SCM.mem_fixedAncestorsOfNode` | `d ∈ M.fixedAncestorsOfNode v ↔ d ∈ M.fixed ∧ (d = v ∨ isAncestor d v)` | Membership characterisation for `fixedAncestorsOfNode` | **Proved** |
| `SCM.latentAncestorsOfNode_subset` | `M.latentAncestorsOfNode v ⊆ M.unobserved` | Subset lemma | **Proved** |
| `SCM.fixedAncestorsOfNode_subset` | `M.fixedAncestorsOfNode v ⊆ M.fixed` | Subset lemma | **Proved** |
| `SCM.evalMap_factors_through_ancestors` | `[∀ n, Nonempty (Ω n)] → ∀ v ∈ M.observed, ∃ g : ValuesOn (fixedAncestorsOfNode v) → ValuesOn (latentAncestorsOfNode v) → swigΩ Ω v, Measurable (uncurry g) ∧ ∀ s ℓ, evalMap s ℓ ⟨v,_⟩ = g (proj s) (proj ℓ)` | Ancestor factorization (existence form): two-argument curried witness `g` over fixed-ancestor and latent-ancestor projections. Built via extend-and-evalMap; pointwise equation via `ancestralFactorization` at `T := {v}`. Consumed by `GlobalMarkov` | **Proved** |

---

## 6a''. `SCM/Model/EvalLatent.lean` — Latent-Restricted Factorization

Imports `Evaluation.lean`. Provides §7: for a latent root `a` and a non-descendant set `T`, the projection of `evalMap s` to `T` factors through all latent coordinates *except* `a`. Used by `GlobalMarkov.full_local_markov_latent` to establish independence between the `{a}`-projection and the `T`-projection of `evalMap s`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.evalMap_factors_excluding_latent` | `∀ (a : SWIGNode N) (ha : a ∈ M.unobserved) (T ⊆ randomVars), (∀ v ∈ T, ¬isAncestor a v ∧ v ≠ a) → ∃ g : (∀ i ∈ univ.erase ⟨a,ha⟩, swigΩ Ω i.val.val) → ValuesOn T, Measurable g ∧ ∀ ℓ, valuesProjection hT (evalMap s ℓ) = g (fun i => ℓ i.val)` | Latent-restricted factorization: `valuesProjection hT ∘ evalMap s` factors through latent coordinates excluding `a`. Build: measurable `extend` fills in a default at `a`, copies elsewhere; for observed `v ∈ T` close via `ancestralFactorization` (no `a`-ancestor), for unobserved `v ∈ T` via `evalMap_unobserved` | **Proved** |

---

## 6a''''. `SCM/Model/CutsetLatent.lean` — Latent cutset and structural override factorization

Imports `EvalOverrideC.lean`. Defines the latent cutset `C_W` (latent roots reaching a target `Y` along a directed path whose interior avoids an override block `C`) and proves the keystone structural factorization for the continuous-backdoor witness kernel: the override evaluation `evalMap_overrideC` with override block `C` depends on the latent assignment only through its values on the cutset. No d-separation is needed — latents outside the cutset reach `Y` only through the short-circuited block `C`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `DAG.isAncestorAvoiding` | `DAG V → Finset V → V → V → Prop` (inductive) | A directed path from `u` to `v` whose strictly interior nodes all avoid `C`; built by extending at the target end (`edge`, `trans`) | **Defined** |
| `DAG.isAncestorAvoiding.toIsAncestor` | `isAncestorAvoiding C u v → isAncestor u v` | Forgets interior-avoidance: an avoiding path is an ordinary ancestor | **Proved** |
| `DAG.isAncestorAvoiding.cons` | `edge u w → w ∉ C → isAncestorAvoiding C w v → isAncestorAvoiding C u v` | Prepend an edge at the source end (new interior node `w` avoids `C`) | **Proved** |
| `DAG.isAncestorAvoiding.exists_path` | `isAncestorAvoiding C u v → ∃ q, len ≥ 2 ∧ head = u ∧ last = v ∧ (directed edges) ∧ (interior nodes ∉ C)` | Materialises a concrete forward-directed path list with interior nodes avoiding `C` | **Proved** |
| `SCM.cutsetLatent` | `SCM N Ω → Finset (SWIGNode N) → Finset (SWIGNode N) → Finset (SWIGNode N)` | `C_W := {u ∈ unobserved ∣ ∃ y ∈ Y, u = y ∨ isAncestorAvoiding C u y}` (latent roots driving `Y` while avoiding the override block `C`) | **Defined** |
| `SCM.mem_cutsetLatent` | `u ∈ cutsetLatent Y C ↔ u ∈ unobserved ∧ ∃ y ∈ Y, u = y ∨ isAncestorAvoiding C u y` | Membership characterisation | **Proved** |
| `SCM.cutsetLatent_subset` | `cutsetLatent Y C ⊆ M.unobserved` | Subset lemma | **Proved** |
| `SCM.evalMap_overrideC_agree_cutset` | `valuesProjection (cutsetLatent_subset) ℓ₁ = valuesProjection (cutsetLatent_subset) ℓ₂ → evalMap_overrideC hY hC s c ℓ₁ = evalMap_overrideC hY hC s c ℓ₂` | **Keystone (A):** the override evaluation on `Y` depends on the latent vector only through its cutset projection. Strong recursion on the topological index, classifying each parent (latent in cutset / fixed / in `C` / observed-recurse) | **Proved** |
| `SCM.exists_evalMap_overrideC_factors_cutset` | `[∀ n, Nonempty (Ω n)] → ∃ h : ValuesOn (cutsetLatent Y C) → ValuesOn Y, Measurable h ∧ ∀ ℓ, evalMap_overrideC hY hC s c ℓ = h (valuesProjection (cutsetLatent_subset) ℓ)` | Genuine factorization form of (A): a single measurable map of the cutset projection. Built by extend-and-evaluate + the keystone agreement | **Proved** |

---

## 6a'''''. `SCM/Do/CutsetDSep.lean` — Concatenation d-separation for the latent cutset

Imports `CutsetLatent.lean` and `GlobalMarkov.lean`. Transfers d-separation from a target `Y` to the latent cutset that drives it: if `Y ⊥ Zr ∣ (W ∪ F)` then `cutsetLatent Y (Zr ∪ W) ⊥ Zr ∣ (W ∪ F)`. The proof concatenates an active `Zr → c` path with the directed cutset arm `c → … → Y` at the latent fork `c`; the seam is a fork (so the glued path is active) and the arm's interior avoids `W` (via the cutset) and `F` (interior nodes have parents, so they are not fixed roots), contradicting the assumed separation.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.cutsetLatent_dSep_of_dSep` | `(W ⊆ observed) → (F ⊆ fixed) → M.dag.dSep Y Zr (W ∪ F) → M.dag.dSep (cutsetLatent Y (Zr ∪ W)) Zr (W ∪ F)` | **Concatenation d-sep (B):** d-separation transfers from `Y` to its latent cutset. Active-path + directed-arm fork concatenation via `DAG.bbReachable_extend_directed_arm`, contradicting `dSep Y Zr (W∪F)` | **Proved** |
| `SCM.cutsetLatent_dSep_of_fixSet_dSep` | `(W ⊆ observed) → (∀ D∈Z, ∀ w∈W, ¬ ancestor (random D) w) → (fixSet Z).dag.dSep Y Zr (W ∪ (fixSet Z).fixed) → M.dag.dSep (cutsetLatent Y (Zr ∪ W)) Zr (W ∪ M.fixed)` | **Cross-model concatenation d-sep:** post-intervention separation of `Y` from `Zr` in `fixSet Z`, plus backdoor criterion (i) for `W`, yields base-graph latent-cutset separation. A minimal base-graph active `Zr ⤳ Y` path is built (cutset node `c` is a latent root/fork; minimality + the root-fork forward-run argument rule out every treatment out-edge), then transported edge-by-edge into `fixSet Z` | **Proved** |

---

## 6a''''''. `Graph/DSep/OrderedLocalSG.lean` (addendum) — active+directed-arm join

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `DAG.bbReachable_extend_directed_arm` | `IsActivePath Z pa (a→c) → (forward-directed q : c→b, interior ∉ Z) → c ∉ Z → b ∈ bbReachableVertices Z {a}` | Public wrapper extending an active path by a directed arm at a non-collider (fork/chain) seam, gluing via the file-private `chain_join_active`. Used by `cutsetLatent_dSep_of_dSep` | **Proved** |

---

## 6a'''. `SCM/Model/CounterfactualLemmas.lean` — Pathwise CF identities for the PO bridge

Imports `Evaluation.lean` and `InterventionSet.lean`. Provides one-step observed-node unfold lemmas for do-intervened SCMs, plus two pathwise pushforward identities used by `PO/Bridge/FromSCM.lean` to discharge `POSystem.ofSCM_consistency`. The pushforward identities correspond to natural-language propositions in `doc/Basic Concepts.tex` (lines 475–487) and are proved by pathwise induction along the topological order in `Evaluation.lean`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.fixMono_structFun_apply` *(@[simp])* | `(M.fixMono X hObs hFix).structFun v ξ = M.structFun ⟨v.val, _⟩ (fixMonoParentMap M.toSWIGGraph X hObs hFix v.val ξ)` | Exposes the definitional structural equation of a monolithic intervention: the post-intervention node uses the original structural equation with parent values reindexed through the do-parent map | `rfl` |
| `SCM.fixSet_structFun_apply` *(@[simp])* | `(M.fixSet X hObs hFix).structFun v ξ = M.structFun ⟨v.val, _⟩ (fixMonoParentMap M.toSWIGGraph X hObs hFix v.val ξ)` | `fixSet` wrapper for the same structural-equation exposure, used by consumers that work through the public intervention interface | `rfl` |
| `SCM.evalMap_fixSet_observed_apply` | for `v ∈ M.observed`, one observed evaluation step of `(M.fixSet X _ _)` equals `M.structFun v` applied to the `fixMonoParentMap`-reindexed recursive parent tuple | Packaged one-step SCM→do bridge: combines `evalMap_observed_unfold` with `fixSet_structFun_apply`, so downstream proofs can expose the original structural equation without unfolding `fixSet`/`fixMono` manually | **Proved** |
| `SCM.evalMap_fixSet_factual_eq` | for `M`, `X ⊆ N`, `s`, `sx`, `ℓ`, `v ∈ M.observed`, `v ∉ X` (pointwise): `(∀ v ∈ M.fixed, sx v = s v) → (∀ D ∈ X, M.evalMap s ℓ ⟨.random D, _⟩ = sx ⟨.fixed D, _⟩) → (M.fixSet X _ _).evalMap sx ℓ ⟨v, _⟩ = M.evalMap s ℓ ⟨v, _⟩` | prop:scm-cf-consistency: on the event the natural value of `X` equals the intervention assignment, evaluating `M.fixSet X` agrees pathwise with evaluating `M` on every observed node disjoint from `X` | **Proved** |
| `SCM.evalMap_fixSet_union_eq` | for `M`, disjoint `X₁`, `X₂`, `s`, `sx₁`, `sxU`, `ℓ`, `v ∈ M.observed`, `v ∉ X₁ ∪ X₂` (pointwise): with old/new compatibility hypotheses + intermediate factual: `(M.fixSet (X₁ ∪ X₂) _ _).evalMap sxU ℓ ⟨v, _⟩ = (M.fixSet X₁ _ _).evalMap sx₁ ℓ ⟨v, _⟩` | prop:scm-cf-commute: intervening on `X₁ ∪ X₂` matches first intervening on `X₁` then on `X₂`, provided the natural value of `X₂` after the `X₁` intervention already equals the `X₂` assignment | **Proved** |

Reference: `Basic Concepts.tex`, prop:scm-cf-consistency (L475–480), prop:scm-cf-commute (L482–487).

---

## 6b. `SCM/Model/Kernel.lean` — Joint and observational kernels (core)

Given a gSCM `M`, the joint kernel sends each fixed-value assignment `s` to
the pushforward of `M.latentProduct` along `fun ℓ ↦ M.evalMap s ℓ`. It is
built as `(Kernel.const _ M.latentProduct ⊗ₖ Kernel.deterministic (uncurry evalMap) …).map Prod.snd` — i.e. the `(ℓ, evalMap s ℓ)` joint law, projected to
the second factor. The observational kernel is then the `randomToObserved`
pushforward of `jointKernel`.

**This file is intentionally minimal:** do-calculus Rule 2 / Rule 3 kernel
statements and their value-space helpers live in `SCM/Do/Rule2.lean`
and `SCM/Do/Rule3.lean` (see §6b1–§6b2).

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.jointKernel` | `Kernel (FixedValues M) (RandomValues M)` | Kernel mapping each fixed-value assignment to the law of `evalMap s` pushed forward through `latentProduct` | noncomputable |
| `SCM.randomToObserved` | `RandomValues M → ObservedValues M` | Projects a full random assignment to its observed-only coordinates | Defined |
| `SCM.measurable_randomToObserved` | `Measurable randomToObserved` | Measurability of the observed-projection map | **Proved** |
| `SCM.jointKernel_apply_eq` | `M.jointKernel s = M.latentProduct.map (fun ℓ => M.evalMap s ℓ)` | Collapses the `compProd`-of-`const`-and-`deterministic` definition to a direct `Measure.map` | **Proved (Layer 4)** |
| `SCM.obsKernel` | `Kernel (FixedValues M) (ObservedValues M)` | Observational kernel: pushforward of `jointKernel` along the observed projection | noncomputable |
| `SCM.jointKernel_map_commute` | `M.obsKernel = (const latentProduct ⊗ₖ deterministic (uncurry evalMap) _).map (randomToObserved ∘ Prod.snd)` | Rewrites `obsKernel` as a single-step push-and-project form via `map_comp_right` | **Proved (Layer 4)** |

Reference: Basic Concepts.tex, Definition `def:scm-joint`; `rem:scm-docalculus-lean` bullet 3 for the Step B escalation.

> **Archive note.** The old kernel-primitive sections `8a. Causal/Kernel/PoSet.lean`, `8b. Causal/Kernel/KernelOps.lean`, and `8e. Causal/Kernel/CrossModel.lean` have been removed. Their contents — iterated Po fold, kernel projection / marginal utilities, cross-model `compProd` analyses — live in `archive/Causal/Kernel/` for historical reference and will be recovered against the SCM primitives in a later pass.

---

## 6b'. `SCM/Model/EquivKernel.lean` — HEq transport of kernels across `SCM.Equiv`

All `SCM.Equiv`-related transport lemmas, from the fundamental `evalMap`-level agreement (§8) through the kernel-level HEq wrappers. Imports `Kernel.lean` (which transitively imports `Evaluation.lean`).

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.structFun_apply_eq_of_equiv` *(private)* | `SWIGGraph.Equivalent M₁ M₂ → HEq structFun₁ structFun₂ → (parent tuples agree pointwise) → M₁.structFun ⟨v,_⟩ ξ₁ = M₂.structFun ⟨v,_⟩ ξ₂` | HEq-application equality for `structFun` across `Equiv`-related SCMs. Uses `dcongr_heq` + `Function.hfunext` + `Subtype.heq_iff_coe_eq` + `Equivalent.parents_eq` | **Proved** |
| `SCM.evalMap_eq_of_equiv` | `Equiv M₁ M₂ → (s, ℓ) agree on Finsets → M₁.evalMap s₁ ℓ₁ ⟨w, _⟩ = M₂.evalMap s₂ ℓ₂ ⟨w, _⟩` | Cross-SCM pointwise equality of `evalMap`. Strong induction on M₁-topological index, unfolding via `evalMap_observed_unfold` on both sides, closing via `structFun_apply_eq_of_equiv` + IH | **Proved** |
| `SCM.Equiv.heq_latentProduct` | `Equiv M₁ M₂ → HEq M₁.latentProduct M₂.latentProduct` | Latent product measures match after subst of `unobserved` Finset equality and collapsing HEq `latentDist` to Eq | **Proved** |
| `SCM.Equiv.heq_jointKernel` | `Equiv M₁ M₂ → HEq M₁.jointKernel M₂.jointKernel` | Joint kernels match via `Kernel.ext` + `jointKernel_apply_eq` + pointwise `evalMap_eq_of_equiv` via `funext` | **Proved** |
| `SCM.Equiv.heq_obsKernel` | `Equiv M₁ M₂ → HEq M₁.obsKernel M₂.obsKernel` | `obsKernel = jointKernel.map randomToObserved`; HEq via `heq_jointKernel` + HEq of `randomToObserved` | **Proved** |
| `SCM.Equiv.heq_obsCondKernel` | `Equiv M₁ M₂ + shared Y, CC Finsets → HEq obsCondKernels` | Kernel-native conditional: `obsCondKernel = (obsCondPairKernel).condKernel`. HEq via destructure + `subst` on SWIG-graph equality + latent-index equality; after `subst`, the two `letI`-local `IsFiniteKernel` witnesses elaborate against identical data, so `congr 1` handles instance transport and `rw [h_ok_eq]` closes the `Kernel.condKernel` argument | **Proved** |

---

## 6b0. `SCM/Factored/*.lean` — Recursive Markov factorization of `jointKernel`

Sequential-`compProd` reconstruction of `jointKernel` along the topological order of observed nodes, realizing `P(V, U ∣ S) = P(U) · ∏ P(V_i ∣ Pa(V_i))` with each step a deterministic `Dirac(f_{V_i}(Pa(V_i)))`. Block 3 of the roadmap for `fullCondIndep_singleton_of_dSep`; the observed-node step is deterministic, so step kernels are `Kernel.deterministic` (not `condDistrib`).

Seven files under `Causalean/SCM/Factored/`:

### `PrefixState.lean` — prefix value types

| Declaration | Signature / meaning | Description | Status |
|---|---|---|---|
| `SCM.ObservedPrefixValues n hn` | `Type _` — recursive product of values at the first `n` observed nodes in topo order | Value type for the observed prefix; base = `PUnit`, step = previous prefix × next node's value | Defined |
| `SCM.OrderedLatentPrefixValues n hn` | `LatentValues M × ObservedPrefixValues M n hn` | Full state at prefix length `n`: all latents plus the first `n` observed values | `abbrev` |
| `SCM.observedPrefixValue hn ξ i` | `swigΩ Ω (observedAt ⟨i.1, _⟩).val` | Read slot `i : Fin n` from a prefix state | Defined |
| `SCM.measurable_observedPrefixValue` | `Measurable` of the reader | Measurability per slot | **Proved** |
| `SCM.extendOrderedLatentPrefix hn` | `OrderedLatentPrefixValues n _ × swigΩ Ω v_n.val → OrderedLatentPrefixValues (n+1) hn` | Append the next observed value to a state | Defined |
| `SCM.measurable_extendOrderedLatentPrefix` | `Measurable (extendOrderedLatentPrefix _)` | Measurability | **Proved** |

### `ParentLookup.lean` — parent-value reader

| Declaration | Signature / meaning | Description | Status |
|---|---|---|---|
| `SCM.parentValuesFromPrefix hn` | `(FixedValues × OrderedLatentPrefixValues n _) → (∀ p ∈ parents v_n, swigΩ Ω p.val)` | Looks up every parent of `v_n = observedAt ⟨n, hn⟩` from the appropriate component: fixed parents from `s`, latent parents from `ℓ`, observed parents from the prefix via `observedPrefixValue` at index `< n` (by `observed_parent_index_lt`) | Defined |
| `SCM.measurable_parentValuesFromPrefix` | `Measurable (parentValuesFromPrefix _)` | Compositional measurability | **Proved** |

### `StepKernel.lean` — deterministic step kernel

| Declaration | Signature / meaning | Description | Status |
|---|---|---|---|
| `SCM.stepFun hn` | `(FixedValues × OrderedLatentPrefixValues n _) → swigΩ Ω v_n.val` | `structFun v_n ∘ parentValuesFromPrefix hn` — the structural equation applied to parent values read from the state | Defined |
| `SCM.measurable_stepFun` | `Measurable (stepFun _)` | Composition of `structFun_measurable` with `measurable_parentValuesFromPrefix` | **Proved** |
| `SCM.stepKernel hn` | `Kernel (FixedValues × OrderedLatentPrefixValues n _) (swigΩ Ω v_n.val)` | `Kernel.deterministic (stepFun hn) _` — emits the deterministic value of `v_n` given its parents | Defined |
| `SCM.isMarkov_stepKernel` | `IsMarkovKernel (stepKernel hn)` | Instance; deterministic kernels are Markov | **Proved** |

### `PrefixKernel.lean` — recursive assembly

| Declaration | Signature / meaning | Description | Status |
|---|---|---|---|
| `SCM.latentKernelOnFixed` | `Kernel (FixedValues M) (LatentValues M)` | `Kernel.const _ latentProduct` — latents as a Markov kernel ignoring fixed input | Defined |
| `SCM.isMarkov_latentKernelOnFixed` | instance | Markov | **Proved** |
| `SCM.jointKernelPrefixZero` | `Kernel (FixedValues M) (OrderedLatentPrefixValues M 0 _)` | Base prefix: pushes `latentKernelOnFixed` through `ℓ ↦ (ℓ, PUnit.unit)` | Defined |
| `SCM.isMarkov_jointKernelPrefixZero` | instance | Markov | **Proved** |
| `SCM.jointKernelPrefix n hn` | `Kernel (FixedValues M) (OrderedLatentPrefixValues M n hn)` | Recursive: `0 → jointKernelPrefixZero`; `k+1 → ((jointKernelPrefix k _) ⊗ₖ stepKernel hn).map (extendOrderedLatentPrefix hn)` — the Markov factorization assembled step by step | Defined |
| `SCM.isMarkov_jointKernelPrefix` | instance | Markov at every `n` by induction | **Proved** |

### `EvalMapCorrespond.lean` — prefix ↔ `evalMap` bridge (block 3.5)

| Declaration | Signature / meaning | Description | Status |
|---|---|---|---|
| `SCM.partialEvalMap n hn s ℓ` | `OrderedLatentPrefixValues M n hn` | Deterministic partial evaluator mirroring `jointKernelPrefix`: `0 → (ℓ, PUnit.unit)`; `k+1 → extendOrderedLatentPrefix hn (prev, stepFun hn (s, prev))`. This is the function whose `Dirac`-pushforward is the prefix kernel | Defined |
| `SCM.measurable_partialEvalMap` | `Measurable (fun sℓ => partialEvalMap n hn sℓ.1 sℓ.2)` | Induction on `n` using `measurable_stepFun` and `measurable_extendOrderedLatentPrefix` | **Proved** |
| `SCM.partialEvalMap_latent` | `(partialEvalMap n hn s ℓ).1 = ℓ` | Latent component is preserved by every step | **Proved** |
| `SCM.partialEvalMap_observedPrefixValue` | `observedPrefixValue hn (partialEvalMap n hn s ℓ).2 i = evalObservedAux s ℓ i.1 _` | Bridge to the existing `evalObservedAux`: reading slot `i` of the prefix reproduces the recursive evaluator (proof by structural recursion on `n` with `Fin.lastCases`; last case matches `stepFun` to `evalObservedAux_eq` via per-parent cast reconciliation) | **Proved** |
| `SCM.jointKernelPrefix_apply_eq` | `(jointKernelPrefix n hn) s = latentProduct.map (partialEvalMap n hn s)` | Core factorization: prefix kernel = pushforward of `partialEvalMap`; induction on `n` using the local helper `compProd_deterministic_apply` + `Measure.map_map` | **Proved** |

### `Factorization.lean` — final theorem (block 3.6)

| Declaration | Signature / meaning | Description | Status |
|---|---|---|---|
| `SCM.orderedLatentPrefixFullToRandom` | `OrderedLatentPrefixValues M observed.card _ → RandomValues M` | Reindex the full prefix state back to `RandomValues`: observed coords via `observedPrefixValue` + `cast` through `observedAt_observedIndex`; unobserved coords from the `LatentValues` component | Defined |
| `SCM.measurable_orderedLatentPrefixFullToRandom` | `Measurable` of the reindex | Per-coordinate measurability assembled via `measurable_pi_lambda` | **Proved** |
| `SCM.partialEvalMap_full_eq` | `orderedLatentPrefixFullToRandom (partialEvalMap observed.card _ s ℓ) = evalMap s ℓ` | Coordinate-wise equality: observed coords match via `partialEvalMap_observedPrefixValue`; unobserved coords match via `partialEvalMap_latent` | **Proved** |
| `SCM.jointKernel_factored` | `jointKernel s = ((jointKernelPrefix observed.card _) s).map orderedLatentPrefixFullToRandom` | Pointwise factorization: combines `jointKernel_apply_eq`, `partialEvalMap_full_eq`, `Measure.map_map`, `jointKernelPrefix_apply_eq` | **Proved** |
| `SCM.jointKernel_eq_factored_kernel` | `jointKernel = (jointKernelPrefix observed.card _).map orderedLatentPrefixFullToRandom` | Kernel-level restatement via `Kernel.ext` and `Kernel.map_apply` | **Proved** |

### `ObsChainKernel.lean` — observational chain-rule product

| Declaration | Signature / meaning | Description | Status |
|---|---|---|---|
| `SCM.prefixNodes n` | `Finset (SWIGNode N)` | First `n` observed nodes in the canonical topological order, characterized by `observedIndex < n` | Defined |
| `SCM.observedPredecessors_observedAt` | `M.toSWIGGraph.observedPredecessors (observedAt n) = prefixNodes n` | Tian's full-history predecessor set agrees with the first `n` observed nodes | **Proved** |
| `SCM.obsStepCondKernel hn` | `Kernel (FixedValues M × ValuesOn (prefixNodes n)) (swigΩ Ω v_n)` | One-node conditional kernel `P(V_n | V_0, …, V_{n-1})`, built from `obsCondKernel {v_n} (prefixNodes n)` and mapped out of the singleton value tuple | Defined; Markov/finite instances proved |
| `SCM.obsChainKernel n hn` | `Kernel (FixedValues M) (ValuesOn (prefixNodes n))` | Recursive chain-rule kernel: base Dirac on the empty prefix; successor uses `compProd` with `obsStepCondKernel` and maps through prefix extension | Defined; Markov instance proved |
| `SCM.qFactorProduct` | `Kernel (FixedValues M) (ObservedValues M)` | Full-length observational chain-rule product, reindexed along `prefixNodes observed.card = observed` | Defined |
| `SCM.obsKernel_map_prefixNodes` / `SCM.obsKernel_eq_qFactorProduct` | Prefix projection equality; `M.obsKernel s = M.qFactorProduct s` | Real kernel equality for the observational chain rule, proved by prefix induction using disintegration of `obsCondPairKernel` and transport through the prefix-union equivalence | **Proved** |

**Status of block 3.** The structural `jointKernel` factorization files (3.1–3.6) and the observational chain-rule product in `ObsChainKernel.lean` are closed fully. Block 4 (ordered Markov) consumes `jointKernel_eq_factored_kernel`.

Reference: Basic Concepts.tex, Lemma `lem:scm-ancestral-factor` and the recursive definition around `def:scm-eval`.

---

## 6b1. `SCM/Do/Rule2.lean` — Rule 2 value-space plumbing (aggregator)

`Rule2.lean` is now a **plumbing aggregator**: it re-exports the value-space
/ global-Markov / overlap helpers (`RectIdentity`, `ObsMarkov`,
`ID.Overlap`) consumed by the Rule 2 a.e. statement and downstream
identification.  The kernel-native Rule 2 *statement* itself is the
posterior witness-kernel a.e. theorem `obsCondKernel_fixSet_eq_ae_witness` in
`Rule2AE.lean` (surfaced as `do_rule2_kernel` in `DoCalculus.lean`).

The earlier pointwise/`fillZrW` form `obsCondKernel_fixSet_eq` and its
rectangle-identity core `obsKernel_fixSet_rect_eq` were **retired**: they
pinned `obsCondKernel` on the `μ_C`-null `{Z.random = ζ_s}` slice, which is
ill-posed for continuous treatment (see §6b1b).  The Rule-2-specific
value-space helpers (`zFixedAsRandom`, `valuesUnionMk`, `fillZrW`, …) live
in `SCM/Do/Rule2Kernel/` (`Helpers.lean`, `InterSingleton.lean`,
`LevelsetCompat.lean`, `WMarginal.lean`) and are documented below.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.zFixedAsRandom z` | `ValuesOn (Z.image .fixed) → ValuesOn (Z.image .random)` | Reindexes `.fixed D`-keyed values to `.random D` keys via the shared value space `swigΩ Ω (.fixed D) = Ω D` | Defined |
| `SCM.valuesUnionMk a b` | `ValuesOn A → ValuesOn B → ValuesOn (A ∪ B)` | Piecewise union of two `ValuesOn` slices, with `A` taking priority; defined via `dite` | Defined |
| `SCM.valuesUnionMk_apply_left` / `valuesUnionMk_apply_right` *(@[simp])* | `valuesUnionMk a b ⟨v, hv⟩ = a/b ⟨v, _⟩` under `v ∈ A` / `v ∉ A` | `valuesUnionMk a b` projects to `a` on `A` and to `b` on `B \ A` | **Proved** (`dif_pos`/`dif_neg`) |
| `SCM.measurable_valuesUnionMk_right a` | `Measurable (fun b => valuesUnionMk a b)` | Measurability of `fun b => valuesUnionMk a b` | **Proved** |
| `SCM.valuesUnionEquiv hDisj` | `ValuesOn (A ∪ B) ≃ᵐ ValuesOn A × ValuesOn B` (when `Disjoint A B`) | Canonical measurable equivalence splitting a value on a disjoint union into its two slices; forward is `(valuesProjection subset_union_left, valuesProjection subset_union_right)`, inverse is `valuesUnionMk`. Disjointness is used only for the `left_inv` on the `B`-slot. | **Proved** |
| `SCM.measurable_zFixedAsRandom` | `Measurable zFixedAsRandom` | Measurability of `zFixedAsRandom` | **Proved** |
| `SCM.fillZrW M' Z … W s'` | `ValuesOn W → ValuesOn (Z.image .random ∪ W)` | Rule 2 filler (single-intervention form): inserts the `do(Z)` fixed-node values of `M'` (re-keyed to `.random Z` via `zFixedAsRandom`) into a `W`-indexed tuple | Defined |
| `SCM.measurable_fillZrW M' Z … W s'` | `Measurable (M'.fillZrW Z … W s')` | Measurability of `fillZrW` | **Proved** |
| `SCM.fixSet_evalMap_levelset_compat M' Z … s' ℓ hLevelSet hv` | On the M'-level set (`M'.evalMap (fixSetProj s') ℓ_M' ⟨.random D, _⟩ = s' ⟨.fixed D, _⟩ ∀ D ∈ Z`): `(M'.fixSet Z).evalMap s' ℓ ⟨v, _⟩ = M'.evalMap (fixSetProj s') ℓ_M' ⟨v, _⟩` for every `v ∈ (M'.fixSet Z).observed` | M'-direction cross-SCM `evalMap` bridge (Claim A). Strong recursion on `(M'.fixSet Z).observedIndex`; at the new `u ∈ Z` parent case (via `fixMonoParentMap_apply_random`) `hLevelSet` collapses M's recursive call at `.random u` to `z_u`, matching `(M'.fixSet Z).fixed` at `u` | **Proved** |
| `SCM.fixSet_evalMap_levelset_compat_M2 M' Z … s' ℓ hLS_M2 hv` | On the `(M'.fixSet Z)`-level set: same conclusion as `fixSet_evalMap_levelset_compat` | Other-direction cross-SCM `evalMap` bridge (Claim B). Strong recursion on `M'.observedIndex` (not `(M'.fixSet Z)`'s — the latter's DAG lacks the `.random D → v` edges for `D ∈ Z` since they are rewired, but `M'`'s retains them); at `u ∈ Z` parent: IH at `.random u` combined with `hLS_M2` derives `M'` at `.random u = z_u` | **Proved** |
| `SCM.obsKernel_inter_singleton_Zrand_eq M' Z … W hZrW hDisj_ZrW s' w hS` | `(M'.fixSet Z).obsKernel s' (S ∩ π_{Z.rand∪W}⁻¹ {fillZrW s' w}) = M'.obsKernel (fixSetProj s') (S ∩ π_{Z.rand∪W}⁻¹ {fillZrW s' w})` for any measurable `S ⊆ M'.ObservedValues` | **Z.random-level-set joint kernel agreement** (single-intervention form). Core lemma for `hC1`: on the event `π_{Z.rand ∪ W} = fillZrW s' w`, the `do(Z)`-intervened and base obsKernels agree on any additional measurable `S`-condition. Proof: unfold `obsKernel` to `latentProduct.map (rando ∘ evalMap)`, bridge via `fixSet_latentProduct_compat`; preimage sets agree via Claims A and B | **Proved** (no d-sep used) |
| `SCM.obsKernel_disintegrate_rect M Y CC hY hCC s hD hB` | `M.obsKernel s (π_CC⁻¹ D ∩ π_Y⁻¹ B) = ∫⁻ c in D, obsCondKernel Y CC (s, c) B d((M.obsKernel s).map π_CC)` | Generic M1 disintegration in rectangle form (`InterSingleton.lean`). Direct application of Mathlib's `ProbabilityTheory.setLIntegral_condKernel_eq_measure_prod` to `M.obsCondPairKernel Y CC`, combined with `Kernel.fst_map_prod`. | **Proved** |

---

## 6b1b. `SCM/Do/Rule2Kernel/Structural/*.lean` + `WitnessBridge.lean` — continuous-`Z` cross-SCM bridge

The **posterior witness-kernel proof** for continuous-treatment Rule 2 (sorry-free).  The earlier
structural-kernel route (`obsCondKernel_struct` — the prior-pushforward
representative) was **retired**: it pushed the *prior* latent law forward and so
did not equal the W-confounded posterior conditional.  The current proof instead
builds a *posterior* witness kernel by conditioning the cut-set latent block on
the treatment and pushing it through the structural map; `WitnessBridge.lean`
assembles it and `Rule2AE.lean` exposes the cross-SCM bridge.  The
`Structural/*.lean` files now contribute only the pointwise `evalMap_overrideC`
agreement lemmas consumed by the posterior witness-kernel bridge.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.evalMap_overrideC_dropZr_on_fillZrW M' Z … Y W … s ℓ w` | pointwise: in the post-intervention model, adding the filled `Z.random` coordinates to the override assignment does not change the `Y` output | Post-intervention `evalMap_overrideC` equality for the `fillZrW` assignment (`StructPointwise.lean`). | **Proved** |
| `SCM.evalMap_overrideC_fixSet_compat_on_fillZrW M' Z … W … s w ℓ` | pointwise: the original and post-intervention SCMs agree on the overridden observed evaluation at the same `fillZrW` assignment | Cross-SCM `evalMap_overrideC` compatibility for filled treatment assignments (`StructCrossSCM.lean`). | **Proved** |
| `SCM.cutset_factor_pointwise M' …` | the cut-set latent factorization data for the witness kernel | Pointwise factorization of the override evaluation through the cut-set latent block (`WitnessBridge.lean`). | **Proved** |
| `SCM.obsSide_eq_witness` / `SCM.obsCondKernel_union_eq_witness M' …` | `M1.obsCondKernel Y (Zr∪W)` equals the posterior witness kernel, a.e. | Obs-side identification of the base conditional with the witness kernel (`WitnessBridge.lean`). | **Proved** (sorry-free) |
| `SCM.doSide_eq_witness M' Z … Y W … s0 t …` | `∀ᵐ w ∂μW, M2.obsCondKernel Y W (fixSetExtend s0 t, w) = (witness kernel) w` | Do-side per-slice identification with the *same* posterior witness kernel; M2 witness chain + cross-SCM connect aligned on `μW` by Rule 3 (`WitnessBridge.lean`). | **Proved** (sorry-free) |
| `SCM.obsCondKernel_fixSet_M1_eq_ae_product M' Z … s0 hPositivity_ae` | `∀ᵐ p ∂(νZ ⊗ₘ const μW), M2.obsCondKernel Y W (fixSetExtend s0 p.1, p.2) = M1.obsCondKernel Y (Zr∪W) (s0, valuesUnionMk p.1 p.2)` | Product assembly: LHS=witness (`doSide_eq_witness`), RHS=witness (`obsCondKernel_union_eq_witness`@M1) transported onto the product via `hPositivity_ae`. Consumed by `condDistrib_fixSet_cross_SCM_bridge`. | **Proved** (sorry-free) |
| `SCM.condDistrib_fixSet_cross_SCM_bridge M' Z … s0 hPositivity_ae` | `∀ᵐ p ∂(νZ ⊗ₘ const μW), M2.obsCondKernel Y W (fixSetExtend s0 p.1, p.2) = condDistrib π_Y π_{Zr∪W} (M'.obsKernel s0) (valuesUnionMk p.1 p.2)` | **Continuous-`Z` cross-SCM condDistrib bridge** (`Rule2AE.lean`). Chains the do-side reduction with the obs-side AC transport. | **Proved** (sorry-free) |
| `SCM.obsCondKernel_fixSet_eq_ae_witness M' Z … s0 hOverlap hPositivity_ae` | `∀ᵐ p ∂(νZ ⊗ₘ const μW), M2.obsCondKernel Y W (fixSetExtend s0 p.1, p.2) = M1.obsCondKernel Y (Zr∪W) (s0, valuesUnionMk p.1 p.2)` | **Rule 2, kernel-native witness form (the canonical statement).** A.e. over the supported product marginal — sound for continuous treatment (never pins `obsCondKernel` on a null slice). Surfaced as `do_rule2_kernel`. | **Proved** (sorry-free) |

---

## 6b2. `SCM/Do/Rule3.lean` — Rule 3 bridges and marginal equality

Imports `SCM/Model/Kernel.lean`.  Supplies the latent-product and `evalMap`
compatibility lemmas used in the proof of `condDistrib_intervention_ancestral_eq`,
and hosts that theorem itself.  All three declarations are stated in the
**single-intervention form** on a generic SCM `M'` with one extra do-target
set `Z` — Pearl's two-layer `do(X); do(Z)` reading is recovered at the call
site by instantiating `M' := M.fixSet X …`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.fixSet_latentProduct_compat M' Z hZ_obs hZ_fixed` | `(M'.fixSet Z _ _).latentProduct.map (valuesProjection (fixSet_unobserved).ge) = M'.latentProduct` | Single-intervention latent-product transport: pushing `(M'.fixSet Z).latentProduct` through `valuesProjection` along `fixSet_unobserved` recovers `M'.latentProduct`. Proof via `measurePreserving_valuesEquivOfEq` + `fixSet_latentDist` (both measures are literally the same `Measure.pi` on the same per-coordinate measures). | **Proved** |
| `SCM.fixSet_evalMap_nonAnc_compat M' Z hZ_obs hZ_fixed s' ℓ hv hNoDesc` | `(M'.fixSet Z _ _).evalMap s' ℓ ⟨v,_⟩ = M'.evalMap (fixSetProj s') (valuesProjection (fixSet_unobserved).ge ℓ) ⟨v,_⟩` | Cross-SCM `evalMap` bridge: at an observed `v` with no `SWIGNode.fixed z` (`z ∈ Z`) as ancestor in `(M'.fixSet Z).dag`, the `(M'.fixSet Z)` evaluation agrees with `M'`'s evaluation after projecting the fixed-value argument via `fixSetProj` and transporting the latent argument along `fixSet_unobserved`. Strong recursion on `(M'.fixSet Z).observedIndex`; parent-set coincidence via `fixSet_parents_eq_of_no_fixed_parent`; `fixMonoParentMap` collapses at every parent under the no-fixed-parent hypothesis. | **Proved** |
| `SCM.condDistrib_intervention_ancestral_eq M' Z hZ_obs hZ_fixed T hT hNoDesc s'` | `Measure.map` equality: `T`-marginal of `(M'.fixSet Z _ _).obsKernel s'` equals `T`-marginal of `M'.obsKernel (fixSetProj s')` | `T`-marginal equality of `(M'.fixSet Z).obsKernel` vs `M'.obsKernel` when no `z ∈ Z` has `SWIGNode.fixed z` an ancestor of any `v ∈ T` in `(M'.fixSet Z).dag`. Closes by unfolding `obsKernel` to `latentProduct.map (evalMap ≫ randomToObserved ≫ π)`, bridging the latent source via `fixSet_latentProduct_compat`, and discharging pointwise via `fixSet_evalMap_nonAnc_compat`. | **Proved** |

---

## 7a. `SCM/Model/InterventionMono.lean` — Monolithic multi-target do (`fixMono`)

**Monolithic** multi-target SWIG-split intervention on a gSCM, parallel to the graph-level `SWIGGraph.splitMono`.  This is the SCM-level `do` operation; `fixSet X` with a singleton `X = {D}` recovers a single-target intervention.

Graph layer is `SWIGGraph.splitMono`; `latentDist` and `isProbability_latent` inherited from `M`; `structFun` built from a single monolithic parent reindex `fixMonoParentMap` (no list iteration).

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.fixMonoParentMap G X hObs hFix v ξ` | `∀ w : {w // w ∈ G.dag.parents v}, swigΩ Ω w.val` | Monolithic parent reindexer: reads `.fixed D` for each `.random D ∈ X`, copies all other coordinates; public (consumed by `Rule3.lean`) | Defined |
| `SCM.fixMonoParentMap_apply_fixed` | `fixMonoParentMap … ⟨.fixed d, hw⟩ = ξ ⟨.fixed d, …⟩` | Unfolds `fixMonoParentMap` at a `.fixed d` input | `rfl` |
| `SCM.fixMonoParentMap_apply_random_notMem` | `u ∉ X → fixMonoParentMap … ⟨.random u, hw⟩ = ξ ⟨.random u, …⟩` | Unfolds `fixMonoParentMap` at `.random u` with `u ∉ X` | **Proved** |
| `SCM.fixMonoParentMap_apply_random` | `D ∈ X → fixMonoParentMap … ⟨.random D, h⟩ = ξ ⟨.fixed D, …⟩` | Unfolds `fixMonoParentMap` at `.random D` with `D ∈ X`: reads from `.fixed D` | **Proved** |
| `SCM.measurable_fixMonoParentMap` | `Measurable (fixMonoParentMap G X hObs hFix v)` | Measurability of the monolithic parent reindexer | **Proved** |
| `SCM.fixMono M X hObs hFix` | `SCM N Ω` | Monolithic multi-target generalized do: applies `splitMono` on the graph; `latentDist := M.latentDist`; `structFun` reindexed via `fixMonoParentMap` | noncomputable |
| `SCM.fixMono_observed` *(@[simp])* | `(M.fixMono X _ _).observed = M.observed` | `fixMono` preserves the observed node set | `rfl` |
| `SCM.fixMono_unobserved` *(@[simp])* | `(M.fixMono X _ _).unobserved = M.unobserved` | `fixMono` preserves the unobserved node set | `rfl` |
| `SCM.fixMono_fixed` *(@[simp])* | `(M.fixMono X _ _).fixed = M.fixed ∪ X.image SWIGNode.fixed` | Fixed set after `fixMono` is the original fixed set union `X.image SWIGNode.fixed` | `rfl` |
| `SCM.fixMono_latentDist` *(@[simp])* | `(M.fixMono X _ _).latentDist u = M.latentDist u` | `fixMono` inherits `latentDist` unchanged | `rfl` |
| `SCM.fixMono_fixed_subset` | `M.fixed ⊆ (M.fixMono X _ _).fixed` | Original fixed set is a subset of the post-`fixMono` fixed set | **Proved** |
| `SCM.fixMono_image_fixed_subset` | `X.image SWIGNode.fixed ⊆ (M.fixMono X _ _).fixed` | `X.image SWIGNode.fixed` is a subset of the post-`fixMono` fixed set | **Proved** |
| `SCM.fixMono_parents_eq_of_no_fixed_parent` | `(∀ D ∈ X, .fixed D ∉ (M.fixMono X _ _).dag.parents v) → (M.fixMono X _ _).dag.parents v = M.dag.parents v` | Parent-set coincidence at non-`X`-targeted vertices; delegates to `splitMono_parents_eq_of_no_fixed_parent`; key for Rule 3 | **Proved** |

Reference: Basic Concepts.tex, Definition 8 (multi-target generalized intervention); `rem:scm-do-standard-lean`.

---

## 7a2. `SCM/Model/InterventionSet.lean` — Public API (`fixSet`, `fixSetProj`, `fixSetZSlice`)

Thin public-API wrapper: `fixSet` is a definitional alias for `fixMono`, plus the `FixedValues` projection `fixSetProj` consumed by single-intervention `DoCalculus.do_rule2_kernel` / `do_rule3`.

* `fixSetProj : (M.fixSet X _ _).FixedValues → M.FixedValues` — projects away the newly-added `X`-fixed slice; used by `do_rule2_kernel` / `do_rule3` to project a `(M'.fixSet Z).FixedValues` back down to `M'.FixedValues`;
* `fixSetZSlice : ((M.fixSet X).fixSet Z).FixedValues → ValuesOn (Z.image .fixed) (swigΩ Ω)` — extracts the `do(Z)` slice from a two-layer `FixedValues` (retained for downstream use).

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.fixSet M X hObs hFix` | `SCM N Ω` | Standard (Pearl) multi-target do: definitional alias for `fixMono` | noncomputable |
| `SCM.fixSet_observed` *(@[simp])* | `(M.fixSet X _ _).observed = M.observed` | `fixSet` preserves the observed node set | `rfl` |
| `SCM.fixSet_unobserved` *(@[simp])* | `(M.fixSet X _ _).unobserved = M.unobserved` | `fixSet` preserves the unobserved node set | `rfl` |
| `SCM.fixSet_fixed` *(@[simp])* | `(M.fixSet X _ _).fixed = M.fixed ∪ X.image SWIGNode.fixed` | Fixed set after `fixSet` is the original fixed set union `X.image SWIGNode.fixed` | `rfl` |
| `SCM.fixSet_latentDist` *(@[simp])* | `(M.fixSet X _ _).latentDist u = M.latentDist u` | `fixSet` inherits `latentDist` unchanged | `rfl` |
| `SCM.fixSet_fixed_subset` | `M.fixed ⊆ (M.fixSet X _ _).fixed` | Original fixed set is a subset of the post-`fixSet` fixed set | **Proved** |
| `SCM.fixSet_image_fixed_subset` | `X.image SWIGNode.fixed ⊆ (M.fixSet X _ _).fixed` | `X.image SWIGNode.fixed` is a subset of the post-`fixSet` fixed set | **Proved** |
| `SCM.fixed_mem_fixSet` | `D ∈ X → SWIGNode.fixed D ∈ (M.fixSet X _ _).fixed` | `SWIGNode.fixed D` is in the post-`fixSet` fixed set when `D ∈ X` | **Proved** |
| `SCM.fixSet_parents_eq_of_no_fixed_parent` | `(∀ D ∈ X, .fixed D ∉ (M.fixSet X _ _).dag.parents v) → (M.fixSet X _ _).dag.parents v = M.dag.parents v` | Parent-set coincidence at non-`X`-targeted vertices; key for Rule 3 non-ancestor bridge | **Proved** |
| `SCM.fixSet_empty_parents` | `(M.fixSet ∅ _ _).dag.parents v = M.dag.parents v` | Empty-set specialization of `fixSet_parents_eq_of_no_fixed_parent` (vacuous hypothesis); used by `fixSet_empty_equiv` and downstream single-intervention bridges | **Proved** |
| `SCM.fixSet_empty_edge` | `(M.fixSet ∅ _ _).dag.edge u v ↔ M.dag.edge u v` | Edge-level coincidence at `X = ∅` (splitMonoEdgeRel reduces when `X = ∅`) | **Proved** |
| `SCM.fixSet_empty_equiv` | `SCM.Equiv (M.fixSet ∅ _ _) M` | `fixSet ∅` is structurally equivalent to `M` (SWIG graph edges, fixed/observed/unobserved, edge types, `HEq` of `structFun` and `latentDist`). The literal equality `M.fixSet ∅ _ _ = M` is **not** provable because `splitMonoTopo` at `X = ∅` rewrites node topoOrders; `SCM.Equiv` ignores topoOrder and is the right invariant for d-sep + kernel semantics. Proof uses the `swigIntervention_comm` recipe: `Function.hfunext` over observed + parent-tuple subtypes, reducing `HEq` to `Eq` via `Equivalent.parents_eq` | **Proved** |
| `SCM.fixSetProj M X _ _` | `(M.fixSet X _ _).FixedValues → M.FixedValues` | Projects `(M.fixSet X).FixedValues` down to `M.FixedValues` by restricting to the original fixed nodes | noncomputable |
| `SCM.measurable_fixSetProj` | `Measurable (M.fixSetProj X _ _)` | Measurability of `fixSetProj` | **Proved** |
| `SCM.fixSetZSlice M X Z …` | `((M.fixSet X).fixSet Z).FixedValues → ValuesOn (Z.image SWIGNode.fixed) (swigΩ Ω)` | Extracts the `do(Z)` fixed-node slice from a double-intervention `FixedValues`; consumed by Rule 2 | noncomputable |
| `SCM.measurable_fixSetZSlice` | `Measurable (M.fixSetZSlice X Z _ _ _ _)` | Measurability of `fixSetZSlice` | **Proved** |

Reference: Basic Concepts.tex, Definition 8 (multi-target generalized intervention); `rem:scm-do-standard-lean`.

---

## 7a3. `SCM/Model/InterventionAncestry.lean` — Ancestry bridges for `fixSet`

Bridges between `isAncestor` in the post-intervention DAG `(M.fixSet X).dag`
and the base `M.toSWIGGraph.dag`.  Consumed by
`SCM/ID/Backdoor.lean` to translate the backdoor criterion's
non-descendant condition (condition (i), stated on the original graph) into
the Rule 3 hypothesis (stated on the post-intervention graph, in terms of
`.fixed D` roots).

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `DAG.not_isAncestor_of_root'` | `(∀ u, ¬ G.edge u r) → ∀ u, ¬ G.isAncestor u r` | A vertex with no incoming edges has no proper ancestors | **Proved** |
| `SCM.fixSet_isAncestor_fixed_forward` | `D ∈ X → (M.fixSet X _ _).dag.isAncestor (.fixed D) v → M.toSWIGGraph.dag.isAncestor (.random D) v` | Forward direction: a `.fixed D`-ancestor in the split DAG lifts to a `.random D`-ancestor in the base DAG. Interior vertices of the split path cannot be `.random d` (`d ∈ X`, no outgoing in split) nor `.fixed d` (`d ∈ X`, isolated in the base); all other edges lift `1:1` | **Proved** |

**Note on the iff form.** The backward direction is **false in general**:
if `M.dag` contains `random D → random D' → v` with `D, D' ∈ X`, `D ≠ D'`,
then `G.isAncestor (random D) v` holds but no corresponding `.fixed D → v`
path exists in the split DAG (because `random D'` has no outgoing edges
after splitting). The forward direction is all that's needed for the
backdoor argument (contrapositive of criterion (i)).

---

## 7b. `SCM/Model/Induced.lean` — Induced sub-SCM (Definition `def:scm-induced-sub`)

Full implementation of the induced sub-SCM construction. Imports
`SCM/Model/Kernel.lean` so that the Layer 4 marginal-compatibility statement
can reference `obsKernel` directly.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.isAncestrallyClosedSCM M R` | `Prop` — conjunction of (a) observed-ancestor closure and (b) pairing closure under `iotaMap` | SCM-level ancestral closure: strictly stronger than graph-level `isAncestrallyClosed` | Defined |
| `induce_parents_eq_of_ancClosed` *(private)* | Under `isAncestrallyClosedSCM`, `(M.toSWIGGraph.induce R).dag.parents v = M.dag.parents v` for every `v ∈ (M.toSWIGGraph.induce R).observed` | Under ancestral closure, parent sets of induced-SCM observed nodes equal those in `M` | **Proved** |
| `SCM.induce M R hR` | `SCM N Ω` | Induced sub-SCM on `R ⊆ observed`: restricts the graph, inherits structural functions and latent distribution | **Proved** |
| `SCM.induce_evalMap_compat` | `∀ {v} (hvI : v ∈ (M.induce R hR).randomVars) (hvM : v ∈ M.randomVars), (M.induce R hR).evalMap (sTilde \| _) ℓ ⟨v, hvI⟩ = M.evalMap sTilde ℓ ⟨v, hvM⟩` | `evalMap` of the induced SCM at any `v ∈ (M.induce R).randomVars` agrees pointwise with `M.evalMap` | **Proved (Layer 4)** |
| `SCM.induce_marginal_compat M R hR sTilde` | `(M.induce R hR).obsKernel (sTilde \| (M.induce R hR).fixed) = (M.obsKernel sTilde).map (valuesProjection : ObservedValues M → ObservedValues (M.induce R hR))` | `obsKernel` of the induced SCM is the `valuesProjection` pushforward of `M.obsKernel` | **Proved (Layer 4)** |

References: Basic Concepts.tex, Definitions `def:scm-anc-closed`, `def:scm-induced-sub`; Proposition `prop:scm-induced-marginal`.

---

## 8c. `SCM/Do/SemiGraphoid.lean` — Semi-Graphoid Axioms

Semi-graphoid axioms on observational conditional independence for a gSCM,
stated against an arbitrary finite measure `μ` on `ObservedValues M` using
Mathlib's `ProbabilityTheory.CondIndepFun` (via `valuesProjection` and
`comap_valuesProjection_le`).  The canonical choice downstream is
`Causalean.SCM.obsKernel M s` at `s : M.FixedValues`.  Weak union and contraction
are SCM-level wrappers around graph-independent projection lemmas in
`Mathlib/CondIndep/SemiGraphoid.lean`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `SCM.ObsCondIndep M X Y Z hX hY hZ μ` | `Prop` over `μ : Measure (ObservedValues M)` | Observational conditional independence `X ⊥ Y \| Z` as `CondIndepFun` on the projected σ-algebras | Defined (requires `StandardBorelSpace M.ObservedValues`, `[IsFiniteMeasure μ]`) |
| `SCM.valuesProjection_comp` | composition identity for nested `valuesProjection` | Used in `obsCondIndep_subset_right` | **Proved** |
| `SCM.comap_valuesProjection_mono` | monotonicity of `comap (valuesProjection …)` in the projected index set | Generic projection σ-algebra helper for CI plumbing on finite products | **Proved** |
| `Causalean.condIndep_valuesProjection_symm` | projection-form `CondIndepFun` symmetry | Graph-independent symmetry helper over `ValuesOn I` projections | **Proved** |
| `Causalean.condIndep_valuesProjection_subset_right` | projection-form subset-right | Graph-independent subset-right helper over `ValuesOn I` projections | **Proved** |
| `Causalean.condIndep_valuesProjection_decomposition` | projection-form decomposition | Graph-independent decomposition helper over `ValuesOn I` projections | **Proved** |
| `Causalean.condIndep_valuesProjection_weak_union_axiom` | projection-form weak union | Graph-independent weak-union wrapper around `Mathlib/CondIndep/SemiGraphoid.lean` | **Proved** |
| `Causalean.condIndep_valuesProjection_contraction_axiom` | projection-form contraction | Graph-independent contraction wrapper around `Mathlib/CondIndep/SemiGraphoid.lean` | **Proved** |
| `obsCondIndep_symm` | symmetry in `X` and `Y` | Delegates to `CondIndepFun.symm` | **Proved** |
| `obsCondIndep_subset_right` | `Y' ⊆ Y` inherits CI from `X ⊥ Y \| Z` | SCM-level wrapper via `Causalean.condIndep_valuesProjection_subset_right` | **Proved** |
| `obsCondIndep_decomposition` | `X ⊥ (Y ∪ W) \| Z → X ⊥ Y \| Z` | SCM-level wrapper via `Causalean.condIndep_valuesProjection_decomposition` | **Proved** |
| `obsCondIndep_weak_union` | `X ⊥ (Y ∪ W) \| Z → X ⊥ Y \| (Z ∪ W)` | SCM-level wrapper via `Causalean.condIndep_valuesProjection_weak_union_axiom` | **Proved** |
| `obsCondIndep_contraction` | standard contraction axiom | SCM-level wrapper via `Causalean.condIndep_valuesProjection_contraction_axiom` | **Proved** |

The hard measure-theoretic obligations are factored into
`Mathlib/CondIndep.lean`; this file now exposes the SCM-facing wrappers and
keeps all graph-independent CI obligations in one place.

---

## 8d. `SCM/Do/{FullCondIndep, LocalMarkov, GlobalMarkov, ObsMarkov}.lean` — Global Markov Property (split)

The central bridge between d-separation and observational conditional
independence. Uses d-separation in the **full graph** (including latent
nodes) to derive CI at the observational level.  Originally one file;
split in this session into four focused modules:

* **`FullCondIndep.lean`** — `FullCondIndep` definition + semi-graphoid axioms + congruence helper.
* **`LocalMarkov.lean`** — `condIndepFun_of_map` bridge + `full_local_markov` (observed) + `full_local_markov_latent` (unobserved).
* **`GlobalMarkov.lean`** — `fullCondIndep_singleton_of_dSep` auxiliary + `full_globalMarkov` Verma–Pearl induction.
* **`ObsMarkov.lean`** — `obs_condIndep_of_full` projection + `globalMarkov` + `globalMarkov_with_fixed`.

Imports flow `FullCondIndep → LocalMarkov → GlobalMarkov → ObsMarkov`.

### `FullCondIndep.lean`

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `FullCondIndep` | CI on `RandomValues M` (full joint distribution including latents) | Conditional independence on the full joint distribution `jointKernel M s`, including latent variables | Definition |
| `fullCondIndep_symm` / `fullCondIndep_subset_right` / `fullCondIndep_decomposition` | Semi-graphoid lemmas for `FullCondIndep` | Thin wrappers around generic projection-form CI lemmas from `SemiGraphoid.lean` | **Proved** |
| `fullCondIndep_weak_union` / `fullCondIndep_contraction` | Semi-graphoid axioms | Also wrappers around the shared projection-form CI layer | **Proved** (depends on Mathlib stubs) |
| `fullCondIndep_congr_left` | `FullCondIndep M X Y Z … μ → X = X' → FullCondIndep M X' Y Z … μ` | Transport `FullCondIndep` along a Finset equality on the first argument; used in the Verma–Pearl induction to convert `{a} ∪ A'` to `insert a A'` | **Proved** (`subst heq`) |

### `LocalMarkov.lean`

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `observed_subset_randomVars` | `M.observed ⊆ M.randomVars` | Trivial containment of observed in `M.randomVars = observed ∪ unobserved` | **Proved** |
| `condIndepFun_of_map` | Pushforward bridge: `CondIndepFun` under `ν` → under `ν.map φ` | Transfers `CondIndepFun` through a measurable pushforward via `condDistrib` characterization | **Proved** |
| `full_local_markov` | `FullCondIndep M {v} (NonDesc v ∩ randomVars) (Pa v ∩ randomVars) ... (jointKernel M s)` for `v ∈ M.observed` | Local Markov on the full joint: under `jointKernel M s`, each observed `v` is conditionally independent of its non-descendants given all parents (including latent ones). Proved via `evalMap_factors_through_parents` (LatentValues-level CI built from `condIndepFun_of_measurable_left`, then transported to `RandomValues` via `condIndepFun_of_map`) | **Proved** |
| `full_local_markov_latent` | `FullCondIndep M {a} (NonDesc a ∩ randomVars) ∅ ... (jointKernel M s)` for `a ∈ M.unobserved` | Latent-root analogue of `full_local_markov`: since latents have no parents, the conditioning set collapses to `∅` and we get *unconditional* independence of `{a}` from its non-descendants. Proved in four phases: (A) identify `jointKernel s = latentProduct.map (evalMap s)`; (B)–(C) collapse the `∅`-indexed conditioning σ-algebra to `⊥` via `comap_eq_bot_of_subsingleton` and reduce to `IndepFun … (jointKernel s)` via `condIndepFun_bot_of_indepFun`; (D) pushforward bridge `indepFun_of_map` to `latentProduct`-level `IndepFun`; (E) factor the LHS as a measurable wrap of the latent coord at `⟨a, ha⟩` (via `evalMap_unobserved`) and the RHS as a measurable function of latents *excluding* `⟨a, ha⟩` (via `evalMap_factors_excluding_latent`), then close via `indepFun_pi_of_disjoint` + `IndepFun.comp` at `S = {⟨a,ha⟩}`, `T = univ.erase ⟨a,ha⟩` | **Proved** |

### `GlobalMarkov.lean`

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `fullCondIndep_singleton_of_dSep` | `Disjoint {a} Y → dSep {a} Y W → FullCondIndep M {a} Y W ... (jointKernel M s)` | Singleton-source d-sep ⟹ full CI, now with the necessary non-overlap assumption `a ∉ Y`. The body is refactored around three named SCM/product-space bridges: a latent-overlap lemma `latentAncestorsOfSet_inter_subset_of_dSep_with_fixed`, a raw-base factorization `evalMap_valuesProjection_factors_through_latentAncestorsOfSet`, and the corrected latent-base/residual factorization `evalMap_valuesProjection_factors_through_latent_base_and_residual`. The previously stronger claim factoring through the realized `W`-values was false in general and has been removed. The remaining blockers are the two factorization helpers together with the generic product-space CI bridge `condIndepFun_of_shared_base_valuesProjection_pi` | **sorry** (isolated to named helpers) |
| `full_globalMarkov` | `Disjoint X Y → dSep X Y Z → FullCondIndep M X Y Z ... (jointKernel M s)` | Verma–Pearl induction. The disjointness hypothesis rules out the degenerate `X ∩ Y ≠ ∅` case, which is not excluded by the current Bayes-ball `dSep` definition. Body sorry-free; transitively depends on `fullCondIndep_singleton_of_dSep` (step ii) and `fullCondIndep_contraction` (step iii) | **Proved** (modulo named auxiliaries) |

### `ObsMarkov.lean`

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `obs_condIndep_of_full` | `FullCondIndep ... (jointKernel s) → ObsCondIndep ... (obsKernel s)` for `X,Y,Z ⊆ observed` | Lifts `FullCondIndep` to `ObsCondIndep` via `randomToObserved` and `condIndepFun_of_map` | **Proved** |
| `globalMarkov` | `Disjoint X Y → dSep X Y Z → ObsCondIndep M X Y Z ... (M.obsKernel s)` for `X,Y,Z ⊆ observed` | `full_globalMarkov` then `obs_condIndep_of_full`; inherits the necessary `Disjoint X Y` side condition from the full theorem | **Proved** (modulo `fullCondIndep_singleton_of_dSep` + `fullCondIndep_contraction`) |
| `globalMarkov_with_fixed` | `Disjoint X Y → dSep X Y (Z_obs ∪ Z_fix) → ObsCondIndep M X Y Z_obs ... (M.obsKernel s)` for `Z_fix ⊆ M.fixed` | Global Markov allowing fixed nodes in the d-sep condition; consumed by `do_rule1`; proved modulo the singleton-source full theorem | **Proved** (modulo `fullCondIndep_singleton_of_dSep_with_fixed`) |

**Corrected in Session 2:** The old `local_markov` (conditioning on
`Pa(v) ∩ V` only) was incorrect for gSCMs with shared latent confounders.
Replaced with `full_local_markov` conditioning on all parents `Pa(v)`
including latent ones, at the full distribution `jointKernel M s`. The
observational `globalMarkov` is *intended* to follow via `obs_condIndep_of_full`
once `full_globalMarkov` is complete.

---

## 8f. `SCM/Do/DoCalculus.lean` — do-Calculus (Pearl 1995 / MST 2019)

The three rules of do-calculus stated in **single-intervention form**
against the SCM observational kernel: every rule takes a generic SCM
`M'` and, for Rules 2 and 3, at most one extra intervention target
`Z : Finset N` applied on top.  Pearl's classical two-layer form
`do(X); do(Z)` is recovered purely as an accounting identity at the
call site by instantiating `M' := M.fixSet X …` — once `M'` is chosen,
the rule's conclusion is the same as Pearl's, with no outer-`X` layer
in the statement itself.

d-Separation is taken directly on the split SWIG graph of the relevant
SCM (`M'.dag` for Rule 1, `(M'.fixSet Z).dag` for Rule 2/3) — the
classical Pearl mutilation graphs `G_{\overline X}`, `G_{\underline Z}`
are **not** used; the former collapses into split-with-conditioning-on
the fixed nodes, the latter into split-of-`Z` (whose `random_Z` has no
outgoing).

**Pearl → split translation.**  Pearl's d-sep conditioning set
`W ∪ X` in `G_{\overline X}` becomes `W ∪ M'.fixed` in the single-
intervention setup: the fixed nodes are kernel parameters (constants)
under `obsKernel s`, so conditioning on them is free.  Callers who
want Pearl's two-layer reading pick `M' := M.fixSet X`; then
`M'.fixed ⊇ X.image .fixed` absorbs the outer-`do(X)` conditioning.

| Declaration | Shape | d-sep / non-ancestor condition | Description | Status |
|---|---|---|---|---|
| `SCM.do_rule1 M' Y Z W … hdSep s` | CI on `M'` | `dSep Y Z (W ∪ M'.fixed)` in `M'.dag`; pairwise disjointness of `Y`, `Z`, `W` | **Rule 1 (single-SCM form):** a d-sep premise on the base SCM `M'` implies `ObsCondIndep M' Y Z W` against `M'.obsKernel s`. Pearl's two-layer `(Y ⊥ Z \| W, X)_{G_{\overline X}}` is obtained by taking `M' := M.fixSet X`. | **sorry** — one-line delegation to `M'.globalMarkov_with_fixed`, which is still `sorry` |
| `SCM.do_rule2_kernel M' Z … Y W … hdSep hWNonDesc hWNonDescM1 s0 hOverlap hPositivity_ae` | a.e.-over-product equality of `obsCondKernel` values | `dSep Y (Z.image .random) (W ∪ (M'.fixSet Z).fixed)` in `(M'.fixSet Z).dag`; disjointness; `hWNonDesc`/`hWNonDescM1` (W not downstream of the intervention); `hOverlap : Rule2JointOverlap`; `hPositivity_ae` (product `νZ ⊗ μW ≪ μ_{Zr∪W}`) | **Rule 2 (action/observation exchange, single-SCM, kernel-native, witness form):** for `(νZ ⊗ₘ μW)`-a.e. treatment/conditioning pair `(t, w)`, the `Y | W`-conditional of the model intervened at `t` equals the `Y | (Z.rand ∪ W)`-conditional of `M'` at `valuesUnionMk t w`. **A.e. over the supported product marginal** — sound for continuous `Z` (never pins `obsCondKernel` on a `μ_C`-null slice; the old pointwise/`fillZrW` form `obsCondKernel_fixSet_eq` was retired for exactly that defect). Pearl's two-layer `G_{\overline X, \underline Z}` reading is recovered via `M' := M.fixSet X`. Delegates to `SCM.obsCondKernel_fixSet_eq_ae_witness`. | **Proved** (sorry-free) |
| `SCM.do_rule3 M' Z hZ_obs hZ_fixed Y W … hNoDesc s'` | `(Y ∪ W)`-marginal equality | `hNoDesc : ∀ v ∈ Y ∪ W, ∀ d ∈ Z, ¬ (M'.fixSet Z).dag.isAncestor (.fixed d) v` (plus unused `_hdSep` reserved for the full Rule 3) | **Rule 3 (insertion/deletion of actions, Rule 3\* form):** `(Y ∪ W)`-marginal of `(M'.fixSet Z).obsKernel s'` equals `(Y ∪ W)`-marginal of `M'.obsKernel (fixSetProj s')`. A single hypothesis covers both the marginal and the conditional forms (dividing by equal `W`-marginals recovers the conditional). Pearl's two-layer `G(x,z)` reading is recovered via `M' := M.fixSet X`. | **Proved** — delegates to `SCM.condDistrib_intervention_ancestral_eq` in `SCM/Do/Rule3.lean` |

**Conditional Rule 3** (`SCM/Do/Rule3Conditional.lean`).  The conditional
form `p(Y | do(z), W) = p(Y | W)` promised by the `do_rule3` row above is
formalized as `do_rule3_conditional`, in the honest a.e. `obsCondKernel`
form (the conditional counterpart of `do_rule2_kernel`).  It needs **no**
positivity/ratio infrastructure: `condDistrib` depends only on the joint
pushforward `μ.map (X, Y)`, and Rule 3\* makes the two `(W, Y)` joints
literally equal, so the conditionals coincide (there is no do-side pinning,
unlike Rule 2).  The core disintegration fact is `condDistrib_eq_of_map_prod_eq`;
the literal (non-a.e.) `condDistrib` form is `do_rule3_conditional_condDistrib`.

**Single-intervention vs. two-layer framing.**  The previous formulation
hard-wired a `(M, X, hX_obs, hX_fixed, Z, …)` shape, doubling up
every `hZ_obs`/`hZ_fixed`-style hypothesis and requiring the user to
reason about the *double-intervention* SCM `(M.fixSet X).fixSet Z`
directly.  The single-intervention shape cleanly separates "the SCM
we're reasoning on" (`M'`) from "the intervention we're comparing
against" (`Z`).  All structural content about `do(X)` lives in the
caller's choice of `M'` — the rule statements never mention `X`.

**Conclusions are mathematically the same:**

* Rule 1: `(Y ⊥ Z | W)` against `M'.obsKernel s`, extending the
  conditioning set by `M'.fixed` at the d-sep level for free (fixed
  nodes are constants under `obsKernel s`).
* Rule 2: `P(y | z, w)_{M'} = P(y | do(z), w)_{M'.fixSet Z}` — stated as
  an `=ᵐ` equality of `obsCondKernel` kernels after aligning the
  `(Z.random ∪ W)`-indexed LHS with the `W`-indexed RHS via `fillZrW`.
  Kernel-native (via Mathlib's `ProbabilityTheory.Kernel.condKernel`);
  carries `[StandardBorelSpace (ValuesOn Y (swigΩ Ω))]`,
  `[Nonempty …]`, `[IsFiniteMeasure (obsKernel …)]`, and
  `[CountableOrCountablyGenerated …]` typeclasses.
* Rule 3: `P(y, w)_{M'.fixSet Z} = P(y, w)_{M'}` — the `(Y ∪ W)`-marginal
  equality (Option B in the design note).  Simpler than the tex's
  conditional-on-`W` form but strictly implies it under the
  non-ancestry hypothesis `hNoDesc` (which covers `Y ∪ W`, not just
  `Y`).  Works for the backdoor step 3 (`Z = X_treatment`, `Y = Z_backdoor`, `W = ∅`).

**Deleted in the SCM migration:** `condDistrib_ci_invariant`,
`obs_sub_transport`, `po_rule1/2/3` (kernel-primitive Po-calculus
theorems, archived).  The earlier two-layer-only helper file
`SCM/Do/RuleSingle.lean` is also deleted — the single-intervention
shape subsumes the single-target specialization it was carrying.

References: Basic Concepts.tex, Proposition `prop:scm-docalculus`;
Pearl (2009), *Causality*, Chapter 3; Malinsky, Shpitser & Tchetgen
Tchetgen (2019).

---

## 8g. `Graph/Induce.lean` — Induced Subgraph of a SWIG Graph

Defines `SWIGGraph.induce`, the graph-level restriction to an observed
subset `R` (Basic Concepts.tex Definition 2.11). Since the April 2026
unification, the induced graph is itself a `SWIGGraph` — the old
`SubSWIGGraph` sibling structure has been deleted. This works because
the weakened `dag_edges_classified` invariant (replacing the stronger
`obs_unobs_cover_random`) is trivially preserved under edge removal.

### Restricted DAG and induce

| Definition | Signature | Description |
|---|---|---|
| `SWIGGraph.inducedEdge` | `Finset (SWIGNode N) → SWIGNode N → SWIGNode N → Prop` | `G.dag.edge u v ∧ u ∈ active ∧ v ∈ active` |
| `SWIGGraph.inducedDag` | `Finset (SWIGNode N) → DAG (SWIGNode N)` | Restricted DAG reusing `G.dag.topoOrder` |
| `SWIGGraph.induce` | `SWIGGraph N → Finset (SWIGNode N) → SWIGGraph N` | Restrict `observed` to `R ∩ observed`; drop `fixed` whose `iotaMap` image was removed; filter edges to the new active set |

### Helper lemmas

| Lemma | Statement |
|---|---|
| `inducedDag_edge_iff` | `(G.inducedDag A).edge u v ↔ G.dag.edge u v ∧ u ∈ A ∧ v ∈ A` |
| `inducedDag_parents_subset` | `(G.inducedDag A).parents v ⊆ G.dag.parents v` |
| `inducedDag_children_subset` | `(G.inducedDag A).children u ⊆ G.dag.children u` |

### Notes

- All invariants of `SWIGGraph` (including `fixed_outside_fixed_isolated`
  and `all_children_in_observed`) are re-established by `induce`; the
  proof lives entirely inside `Induce.lean` with no `sorry`s.
- Graph operations (`parents`, `children`, `descendants`, `cComponentOf`,
  `bidirectedBFS`, `directlyConfounded`) are inherited directly from
  `SWIGGraph`/`CComponents.lean` without duplication.

---

## 8h. `PO/` — Potential Outcome Framework

Namespace: `Causalean.PO`.  The potential-outcome framework is organized by
role: `PO/Core/` for graph-free regimes, systems, variables, and
counterfactual distributions; `PO/Assumptions/` for consistency and
counterfactual-independence assumptions; `PO/Conditioning/` for conditional
expectation workhorses; `PO/Bridge/` for restriction and SCM-to-PO bridges; and
`PO/Analysis/` for regression, residualization, and quantile tools.
Spec: `Basic Concepts.tex` §8 lines 812–1263 (def:po-system through
prop:po-consistency).

Current status is skeleton: types and statements are in place; proofs are
`sorry` where noted below.  See each file's spec-label tags for the
corresponding definition/proposition in the .tex.

### `PO/Core/Regime.lean` — Intervention regimes

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `Regime V X` | `structure { target : Finset V, assign : ∀ v : V, v ∈ target → X v }` | Pair `(X, x)` of a target set and an assignment on it | **Defined** |
| `Regime.empty` | `Regime V X` | Empty regime `r_∅` | **Defined** |
| `Regime.Disjoint r₁ r₂` | `Prop` | Disjoint target sets | **Defined** |
| `Regime.sqcup r₁ r₂ h` | `Regime V X` | Disjoint union `r₁ ⊔ r₂` | **Defined** |
| `Regime.empty_disjoint_right` / `_left` | — | `empty` is disjoint from every regime | **Proved** |
| `Regime.sqcup_target` *(@[simp])* | `(r₁.sqcup r₂ h).target = r₁.target ∪ r₂.target` | Target of the disjoint union | `rfl` |
| `Regime.single v x` | `Regime V X` | Singleton regime `({v}, v ↦ x)`; the building block for `{Z ← z}`, `{D ← d}` style one-node interventions | **Defined** |
| `Regime.single_target` *(@[simp])* | `(single v x).target = {v}` | Target of a singleton regime is `{v}` | `rfl` |
| `Regime.single_assign_self` | `(single v x).assign v (mem_singleton_self _) = x` | Evaluating the singleton assignment at `v` returns the supplied value | `rfl` |
| `Regime.single_disjoint_single` | `v ≠ w → (single v x).Disjoint (single w y)` | Two singleton regimes on distinct nodes are disjoint | **Proved** |
| `Regime.single_disjoint_of_not_mem` | `v ∉ r.target → (single v x).Disjoint r` | Left-disjointness of a singleton with any regime missing `v` | **Proved** |
| `Regime.disjoint_single_of_not_mem` | `v ∉ r.target → r.Disjoint (single v x)` | Right-disjointness counterpart; used to chain `sqcup` of several singletons | **Proved** |
| `Regime.listLookup` | `(l : List ((v : V) × X v)) → (v : V) → v ∈ l.map Sigma.fst → X v` | Recursive lookup of the value associated with `v` in a dependent list of `(variable, value)` pairs; defined without `Nodup` so the recursion is definitional | **Defined** |
| `Regime.ofList` | `(l : List ((v : V) × X v)) → (l.map Sigma.fst).Nodup → Regime V X` | Build a regime from a list of `(variable, value)` pairs with nodup keys; target is the toFinset of the keys, assignment via `listLookup`. Used to construct multi-stage DTR regimes uniformly | **Defined** |
| `Regime.ofList_target` *(@[simp])* | `(ofList l h).target = (l.map Sigma.fst).toFinset` | Target of `ofList` is the toFinset of its keys | `rfl` |
| `Regime.ofList_nil` *(@[simp])* | `ofList [] h = empty` | The empty-list builder reduces to `Regime.empty` | **Proved** |
| `Regime.ofList_cons_target` *(@[simp])* | `(ofList (⟨v,x⟩ :: rest) h).target = insert v (rest.map Sigma.fst).toFinset` | Target of a cons unfolds as an `insert` | **Proved** |
| `Regime.listLookup_cons_self` | `listLookup (⟨v,x⟩ :: rest) v hv = x` | Looking up the head key returns the head value | **Proved** |
| `Regime.listLookup_cons_of_ne` | `v ≠ w → listLookup (⟨w,x⟩ :: rest) v hv = listLookup rest v hv'` | Lookup skips a non-matching head and recurses into the tail | **Proved** |

Reference: `Basic Concepts.tex`, def:po-system.

### `PO/Core/System.lean` — Bare PO system and PO operator

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POSystem` | `structure { V, X, Ω, μ, eval, measurable_eval }` | Bare PO system of def:po-system | **Defined** |
| `POSystem.component P r v` | `P.Ω → P.X v` | Per-coordinate potential-outcome variable `v(r)` | **Defined** |
| `POSystem.measurable_component` | `Measurable (P.component r v)` | — | **Proved** |
| `POSystem.poVariable P r Y` | `P.Ω → ValuesOn Y P.X` | Subset-valued `Y(r)` | **Defined** |
| `POSystem.measurable_poVariable` | `Measurable (P.poVariable r Y)` | — | **Proved** |
| `POSystem.poOperator P r Y` | `Measure (ValuesOn Y P.X)` | `Po^P_r(Y) := (Y(r))_# μ` | **Defined** |
| `instance …poOperator… IsProbabilityMeasure` | — | `poOperator` is a probability measure | **Proved** |

Reference: `Basic Concepts.tex`, def:po-operator.

### `PO/Core/Counterfactual.lean` — Cross-world distribution

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POSystem.crossWorldEval P qs` | `P.Ω → ∀ i : Fin qs.length, ValuesOn (qs[i].2) P.X` | Tuple of `Y_i(r_i)(ω)` | **Defined** |
| `POSystem.measurable_crossWorldEval` | — | — | **Proved** |
| `POSystem.counterfactualDist P qs` | `Measure (∀ i, ValuesOn (qs[i].2) P.X)` | Pushforward of `μ` under `crossWorldEval` | **Defined** |
| `instance …counterfactualDist… IsProbabilityMeasure` | — | — | **Proved** |
| `POSystem.counterfactualDist_marginal` | single-coord marginal = `poOperator` | rem:po-reading | **Proved** |

Reference: `Basic Concepts.tex`, def:po-counterfactual, rem:po-reading.

### `PO/Assumptions/Consistency.lean` — Consistency axiom

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POSystem.FactualAgrees P r ω` | `Prop` | Factual value of `r.target` matches `r.assign` at `ω` | **Defined** |
| `POSystem.IntermediateAgrees P r₁ r₂ ω` | `Prop` | Post-`r₁` value of `r₂.target` matches `r₂.assign` | **Defined** |
| `POSystem.Consistency P` | `structure { factual, composition }` | Two-clause consistency predicate | **Defined** |

Reference: `Basic Concepts.tex`, def:po-consistency.

Also adds, in `PO/Core/Regime.lean`:

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `Regime.sqcup_assign_pos` | `v ∈ r₁.target → (r₁.sqcup r₂ h).assign v hv = r₁.assign v _` | Compute `sqcup` assignment on the left side | **Proved** |
| `Regime.sqcup_assign_neg` | `v ∉ r₁.target → v ∈ r₂.target → (r₁.sqcup r₂ h).assign v hv = r₂.assign v _` | Compute `sqcup` assignment on the right side | **Proved** |
| `Regime.ext` | `r₁.target = r₂.target → (∀ v h₁ h₂, r₁.assign v h₁ = r₂.assign v h₂) → r₁ = r₂` | Extensionality for `Regime` (subst-based, both membership proofs supplied) | **Proved** |

### `PO/Bridge/Induce.lean` — Sub-PO system (def:po-restrict)

Implements the *restricted sub-system* `P|_R` (def:po-restrict): given a PO
system `P` and `R : Finset P.V`, build a PO system whose variable type is
`↥R`, with the same probability space `(Ω, μ)` and `eval` inherited from
`P` by lifting the sub-regime back to the ambient `P.V`.  Subtype indexing
automatically enforces the spec clause that regimes target only `R`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POSystem.liftRegime P R r'` | `Regime ↥R (fun v => P.X v.val) → Regime P.V P.X` | Lift a sub-regime to the ambient regime type via `Subtype.val` embedding | **Defined** |
| `POSystem.liftRegime_target` *(@[simp])* | `(P.liftRegime R r').target = r'.target.map ⟨Subtype.val, _⟩` | Target reduction | `rfl` |
| `POSystem.liftRegime_assign` | `(P.liftRegime R r').assign w.val hv = r'.assign w hw` | Reading the lifted assignment at a known sub-regime member returns the original sub-assignment | **Proved** |
| `POSystem.liftRegime_empty` *(@[simp])* | `P.liftRegime R Regime.empty = Regime.empty` | Empty-regime preservation | **Proved** |
| `POSystem.restrict P R` | `POSystem` | The sub-PO system `P|_R` of def:po-restrict | **Defined** |
| `POSystem.restrict_V` / `_X` / `_Ω` / `_μ` *(@[simp])* | structural reductions | `↥R` / `P.X v.val` / `P.Ω` / `P.μ` | `rfl` |
| `POSystem.restrict_eval` *(@[simp])* | `(P.restrict R).eval r' ω v = P.eval (P.liftRegime R r') ω v.val` | Eval reduction via lift | `rfl` |
| `POSystem.restrict_component` *(@[simp])* | per-coord agreement with `P.component` after subtype coercion | — | `rfl` |
| `POSystem.liftRegime_disjoint` | `r₁'.Disjoint r₂' → (P.liftRegime R r₁').Disjoint (P.liftRegime R r₂')` | Disjointness lifts (subtype-injectivity) | **Proved** |
| `POSystem.liftRegime_sqcup_target` | `(P.liftRegime R (r₁'.sqcup r₂' h)).target = (P.liftRegime R r₁').target ∪ (P.liftRegime R r₂').target` | Lift commutes with `sqcup` on targets | **Proved** |
| `POSystem.liftRegime_sqcup` | `P.liftRegime R (r₁'.sqcup r₂' h) = (P.liftRegime R r₁').sqcup (P.liftRegime R r₂') (P.liftRegime_disjoint R h)` | Lift commutes with `sqcup` (full regime equality, via `Regime.ext` and `sqcup_assign_pos`/`_neg`) | **Proved** |
| `POSystem.restrict_consistency` | `P.Consistency → (P.restrict R).Consistency` | Consistency propagates to the sub-system; both clauses reduce to the ambient ones via `restrict_eval` and the lift lemmas | **Proved** |

Reference: `Basic Concepts.tex`, def:po-restrict, rem:po-restrict.

### `PO/Bridge/FromSCM.lean` — SCM → PO bridge

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `ObsIdx M` | `{v : SWIGNode N // v ∈ M.observed ∧ ∀ n, v = .random n → .fixed n ∉ M.fixed}` | Observed-node index type for the induced PO; refined to exclude already-intervened nodes so PO regimes are statically well-formed | **Defined** |
| `obsValue M v` | `Type` | Per-variable value space `swigΩ Ω v.val` | **Defined** |
| `regimeTargetN M r` | `Finset N` | Underlying `Finset N` for a regime of observed nodes | **Defined** |
| `regimeTargetN_obs` | `∀ D ∈ regimeTargetN M r, .random D ∈ M.observed` | `fixSet`-obligation: regime targets are observed | **Proved** |
| `regimeTargetN_notFixed` | `∀ D ∈ regimeTargetN M r, .fixed D ∉ M.fixed` | `fixSet`-obligation: regime targets aren't already intervened (from `ObsIdx` refinement) | **Proved** |
| `combinedFixed M s r` | `SCM.FixedValues (M.fixSet (regimeTargetN M r) …)` | Combined background + regime fixed assignment `s ⊔ x`; pinned by uniqueness via a single `Classical.choose` of `v' ∈ r.target` with `.fixed (obsName v') = v.val` | **Proved** |
| `combinedFixed_exists` *(private)* | `v.val ∉ M.fixed → ∃ v' ∈ r.target, .fixed (obsName M v') = v.val` | Existence helper for the `Classical.choose` in `combinedFixed`'s else-branch | **Proved** |
| `inducedEval M s r ℓ` | `∀ v : ObsIdx M, obsValue M v` | World-eval map of the induced PO system: project `(M.fixSet …).evalMap (combinedFixed M s r) ℓ` onto observed | **Proved** |
| `inducedEval_measurable` | `Measurable (inducedEval M s r)` | Composition of `evalMap_measurable` with `measurable_pi_apply` | **Proved** |
| `POSystem.ofSCM M s` | `POSystem` | Induced PO system `PO(M; s)` of def:po-from-scm | **Proved** |
| `obsName M v` / `obsName_spec` | `ObsIdx M → N` / `v.val = .random (obsName M v)` | Reads the underlying `N`-name of an observed `ObsIdx` element via `Classical.choose` on `observed_is_random` | **Proved** |
| `obsName_injective` | `Function.Injective (obsName M)` | Globally injective: same `obsName` ⇒ same `.val` ⇒ same `ObsIdx` | **Proved** |
| `combinedFixed_old` | `combinedFixed M s r ⟨v, mem_union_left _ hv⟩ = s ⟨v, hv⟩` | `combinedFixed` agrees with `s` on pre-existing fixed coords | **Proved** |
| `combinedFixed_new` | `combinedFixed M s r ⟨.fixed D, …⟩ = cast … (r.assign v' hv'tgt)` | `combinedFixed` reads regime intervention values on new coords; uniqueness pins the internal `Classical.choose` to `v'`, the cast collapses via `cast_heq` + `proof_irrel_heq` | **Proved** |
| `regimeTargetN_mem_val` | `D ∈ regimeTargetN M r → ∃ v' ∈ r.target, v'.val = .random D` | Inverse of `regimeTargetN`: recover the regime variable from a target name | **Proved** |
| `obsIdx_val_injective` | `v.val = w.val → v = w` | Injectivity of the `ObsIdx` coercion | **Proved** |
| `sqcup_assign_left` / `sqcup_assign_right` | `(r₁.sqcup r₂ h).assign v _ = r₁.assign v _` (resp. r₂) | `Regime.sqcup` agrees with the appropriate side on its target | **Proved** |
| `inducedEval_empty_eq_evalMap` | `inducedEval M s Regime.empty ℓ v = M.evalMap s ℓ ⟨v.val, _⟩` | Empty-regime reduction to the bare SCM `evalMap` | **Proved** |
| `regimeTargetN_empty` | `regimeTargetN M Regime.empty = ∅` | `simp` lemma | **Proved** |
| `evalMap_fixSet_transport` *(private)* | Transport `(M.fixSet X₁ _ _).evalMap` across set equality `X₁ = X₂` (via `subst` + `evalMap_eq_of_equiv` with `Equiv.refl`) | Bridges `M.fixSet (regimeTargetN M (r₁.sqcup r₂))` and `M.fixSet (regimeTargetN M r₁ ∪ regimeTargetN M r₂)` for the composition proof | **Proved** |
| `POSystem.ofSCM_consistency` | `(POSystem.ofSCM M s).Consistency` | Induced system satisfies consistency, prop:po-consistency. **factual** closes against `SCM.evalMap_fixSet_factual_eq`; **composition** transports via `evalMap_fixSet_transport` then closes against `SCM.evalMap_fixSet_union_eq` | **Proved** (modulo upstream `evalMap_fixSet_factual_eq` / `evalMap_fixSet_union_eq` `sorry`s in `CounterfactualLemmas.lean`) |

Reference: `Basic Concepts.tex`, def:po-from-scm, rem:po-induced, prop:po-consistency, rem:po-vs-do.

### `PO/Core/Variable.lean` — PO variables and regimed variables

Abstracts the `S.hXbool.measurable.comp ((measurable_pi_apply _).comp (P.measurable_eval _))`
chain used throughout IV/LATE-style proofs.  A `POVar P α` bundles a node
`v : P.V` with a measurable equivalence `P.X v ≃ᵐ α`, so factual and
counterfactual realisations land in a fixed measurable type.  `RegimedVar`
further attaches a regime and exposes a uniform `value : P.Ω → α`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POVar P α` | `structure { v : P.V, equiv : P.X v ≃ᵐ α }` | PO system variable identified with a fixed measurable value type `α` | **Defined** |
| `POVar.cf a r` | `P.Ω → α` | Counterfactual value `a` under regime `r`: `ω ↦ a.equiv (P.eval r ω a.v)` | **Defined** |
| `POVar.factual a` | `P.Ω → α` | Factual value `a.cf Regime.empty` | **Defined** |
| `POVar.measurable_cf` | `Measurable (a.cf r)` | One-liner measurability of the counterfactual map | **Proved** |
| `POVar.measurable_factual` | `Measurable a.factual` | Specialisation of `measurable_cf` to the empty regime | **Proved** |
| `POVar.event a x` | `Set P.Ω` | Preimage `a.factual ⁻¹' {x}` — the event `{a = x}` | **Defined** |
| `POVar.measurableSet_event` | `MeasurableSet (a.event x)` | Measurability of the factual event (needs `MeasurableSingletonClass α`) | **Proved** |
| `POVar.cfUnder a w y` | `P.Ω → α` | Counterfactual `a` under the single-node intervention `{w ← y}`, i.e. `a.cf (Regime.single w.v (w.equiv.symm y))`; replaces hand-rolled `DofZ z`, `YofD d` patterns | **Defined** |
| `POVar.measurable_cfUnder` | `Measurable (a.cfUnder w y)` | Measurability of the single-intervention counterfactual | **Proved** |
| `RegimedVar P α` | `structure { var : POVar P α, regime : Regime P.V P.X }` | PO variable bundled with an intervention regime | **Defined** |
| `RegimedVar.value` | `P.Ω → α` | `rv.var.cf rv.regime` — uniform evaluator used by `IndepCF` and `POCFBundle.jointValue` | **Defined** |
| `RegimedVar.measurable_value` | `Measurable rv.value` | Measurability of the uniform evaluator | **Proved** |
| `RegimedVar.ofFactual a` | `RegimedVar P α` | Factual bundling `⟨a, Regime.empty⟩` — the standard shape for "factual Z is independent of the cf bundle" | **Defined** |
| `RegimedVar.ofSingle a w x` | `RegimedVar P α` | Bundling under the single-node intervention `{w ← x}` — shortcut for `dUnderZ`/`yUnderD` style variables | **Defined** |
| `POVar.indicator a x` | `P.Ω → ℝ` | Real-valued indicator `1_{a = x}` (defined as `(a.event x).indicator 1`); subsumes per-system `indD`/`indA`/`indM` boilerplate | **Defined** |
| `POVar.indicator_eq_event_indicator` | `a.indicator x = (a.event x).indicator (fun _ => 1)` | Set-indicator form (definitional `rfl`) | **Proved** |
| `POVar.indicator_apply_eq_one` | `a.factual ω = x → a.indicator x ω = 1` | Pointwise value on `{a = x}` | **Proved** |
| `POVar.indicator_apply_eq_zero` | `a.factual ω ≠ x → a.indicator x ω = 0` | Pointwise value off `{a = x}` | **Proved** |
| `POVar.measurable_indicator` | `Measurable (a.indicator x)` | Measurability of the indicator | **Proved** |
| `POVar.stronglyMeasurable_indicator_comap` | `StronglyMeasurable[comap a.factual _] (a.indicator x)` | Strong measurability w.r.t. the `a.factual` σ-algebra | **Proved** |
| `POVar.integrable_indicator` | `[IsFiniteMeasure P.μ] → Integrable (a.indicator x) P.μ` | Indicator is bounded by 1, hence integrable | **Proved** |
| `POVar.indicator_eq_one_or_zero` | `a.indicator x ω = 1 ∨ a.indicator x ω = 0` | Binary value | **Proved** |
| `POVar.indicator_add_indicator_not` | `a.indicator true ω + a.indicator false ω = 1` | Binary-treatment complementarity (`POVar P Bool`) | **Proved** |

### `PO/Assumptions/ConsistencyLemmas.lean` — Pointwise consistency for `POVar`

Generalises the two pointwise consistency specialisations of `LATE.lean`
(`DofZ_eq_factualD_on_zEvent`, `factualY_eq_YofD_factualD`) to arbitrary
`POVar` pairs on distinct nodes.  Each lemma discharges the `Consistency.factual`
clause by reducing it to a singleton-regime agreement check.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POSystem.factualAgrees_empty` | `∀ ω, P.FactualAgrees Regime.empty ω` | Trivial base case: every `ω` factually agrees with the empty regime (target is `∅`) | **Proved** |
| `POSystem.factualAgrees_sqcup` | `{r₁ r₂ : Regime}`, `h : r₁.Disjoint r₂`, `P.FactualAgrees r₁ ω` → `P.FactualAgrees r₂ ω` → `P.FactualAgrees (r₁.sqcup r₂ h) ω` | Combinator: `FactualAgrees` for a disjoint union reduces componentwise. Lets theorem files assemble multi-target consistency hypotheses from per-variable pieces without hand-rolling a `Finset.mem_union` case split | **Proved** |
| `POVar.factualAgrees_single` | `(a : POVar P α) (x : α)`, `a.factual ω = x` → `P.FactualAgrees (Regime.single a.v (a.equiv.symm x)) ω` | Combinator: turns a factual equality `a.factual ω = x` into `FactualAgrees` for the singleton regime `{a.v ← a.equiv.symm x}`. Base case for building compound `FactualAgrees` via `factualAgrees_sqcup` | **Proved** |
| `POVar.cf_eq_factual_on_event` | `hC : P.Consistency`, `a w : POVar`, `a.v ≠ w.v`, `ω ∈ w.event y` → `a.cfUnder w y ω = a.factual ω` | Consistency of `a` under `{w ← y}`: on the event `{w = y}`, the `w`-intervened counterfactual of `a` equals the factual | **Proved** |
| `POVar.factual_eq_cfUnder_self_selected` | `hC : P.Consistency`, `a w : POVar`, `a.v ≠ w.v`, `∀ ω` → `a.factual ω = a.cfUnder w (w.factual ω) ω` | Pointwise: the factual equals the counterfactual under `{w ← factual w(ω)}` — the identity used to rewrite factual outcomes in terms of cf outcomes on the natural treatment choice | **Proved** |
| `POVar.factual_mul_indicator_eq_cfUnder_mul_indicator` | `hC : P.Consistency`, `a : POVar P ℝ`, `w : POVar P β`, `a.v ≠ w.v` → `(fun ω ↦ a.factual ω * 1_{w=y} ω) = (fun ω ↦ a.cfUnder w y ω * 1_{w=y} ω)` | Integrated form of consistency: multiplying by the indicator `1_{w=y}` lets factual and cf values be freely interchanged; workhorse of backdoor-style Step-1 rewrites | **Proved** |
| `POVar.factual_mul_indicator_eq_cfUnder_mul_indicator_fn` | `hC`, `y : POVar P ℝ`, `w : POVar P β`, `[MeasurableSingletonClass β]`, `y.v ≠ w.v` → `(fun ω ↦ y.factual ω * w.indicator x ω) = (fun ω ↦ y.cfUnder w x ω * w.indicator x ω)` | Pointwise-function variant matching the new `POVar.indicator` shape; one-line reduction to the `Set.indicator` form above. Used by backdoor/Manski/frontdoor/DTR Step-1 rewrites | **Proved** |
| `POVar.cf_eq_factual_of_factualAgrees` | `hC : P.Consistency`, `a : POVar P α`, `r : Regime`, `a.v ∉ r.target`, `P.FactualAgrees r ω` → `a.cf r ω = a.factual ω` | **Multi-target** consistency: pointwise, `a`'s counterfactual under any regime `r` (not naming `a.v`) coincides with its factual at every `ω` that factually agrees with `r`. Generalises `cf_eq_factual_on_event` from singleton to arbitrary regimes | **Proved** |
| `POVar.factual_mul_indicator_eq_cf_mul_indicator` | `hC : P.Consistency`, `a : POVar P ℝ`, `r : Regime`, `a.v ∉ r.target`, `E : Set P.Ω`, `(∀ ω ∈ E, P.FactualAgrees r ω)` → `(fun ω ↦ a.factual ω * 1_E ω) = (fun ω ↦ a.cf r ω * 1_E ω)` | **Multi-target** integrated consistency: on any event `E` of full factual agreement with `r`, the factual outcome and the multi-target counterfactual outcome are interchangeable inside `a · 1_E`. Generalises `factual_mul_indicator_eq_cfUnder_mul_indicator` to arbitrary regimes; consumed directly by `cdtr_backdoor` Step 1 | **Proved** |
| `POVar.eventCondExp_cfUnder_eq_factual_on_event` | `hC : P.Consistency`, `y : POVar P ℝ`, `a : POVar P β`, `y.v ≠ a.v` → `eventCondExp μ (a.event a₀) (y.cfUnder a a₀) = eventCondExp μ (a.event a₀) y.factual` | Consistency-on-event for `eventCondExp`: on the stratum `{a = a₀}`, the `{a ← a₀}`-counterfactual and the factual have the same event-level conditional mean. Shared rewrite in `Manski/{MTR,MTS}` and (via the `Fintype` total law below) the integrated MIV bounds; lives in `EventCondExp.lean` alongside the other `eventCondExp` tooling | **Proved** |

### `PO/Assumptions/IndepCF.lean` — Independence of PO counterfactual bundles

Named shapes for `IndepFun` / `CondIndepFun` over a heterogeneous bundle of
regimed PO variables.  Replaces bespoke product-tuple encodings such as the
`cfTuple` pattern in `PO/ID/Exact/LATE.lean`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POCFBundle P` | `structure { n : ℕ, type : Fin n → Type*, inst : ∀ i, MeasurableSpace (type i), vars : ∀ i, RegimedVar P (type i) }` | Heterogeneous finite-length bundle of regimed PO variables over a fixed PO system | **Defined** |
| `POCFBundle.instMeasurableSpaceType` | `MeasurableSpace (B.type i)` | Per-component measurable-space instance derived from the `inst` field (for typeclass inference) | **Instance** |
| `POCFBundle.jointValue B` | `P.Ω → (∀ i : Fin B.n, B.type i)` | Joint evaluator returning the dependent tuple of cf values | **Defined** |
| `POCFBundle.measurable_jointValue` | `Measurable B.jointValue` | Measurability of the joint evaluator (via `measurable_pi_lambda`) | **Proved** |
| `POCFBundle.nil P` | `POCFBundle P` | Empty bundle (length 0) | **Defined** |
| `POCFBundle.cons a B` | `POCFBundle P` | Prepend a `RegimedVar` to a bundle (length `B.n + 1`); used to build the `(D(1), D(0), Y(1), Y(0))` bundle in LATE | **Defined** |
| `POSystem.IndepCF` | `RegimedVar P α → POCFBundle P → Measure P.Ω → Prop` | `IndepFun a.value B.jointValue μ` — uniform shape for "regimed variable ⟂ bundle" | **Defined** |
| `POSystem.CondIndepCF` | `RegimedVar P α → POCFBundle P → RegimedVar P γ → Measure P.Ω → Prop` | Conditional independence of `a` from `B` given σ(`c.value`); requires `StandardBorelSpace P.Ω` | **Defined** |
| `IndepCF.toIndepFun` / `IndepCF.ofIndepFun` | `P.IndepCF a B μ ↔ IndepFun a.value B.jointValue μ` | Trivial bridges between `IndepCF` and the underlying `IndepFun` | **Proved** (`id`) |
| `CondIndepCF.toCondIndepFun` | `P.CondIndepCF a B c μ → CondIndepFun (comap c.value _) _ a.value B.jointValue μ` | Unfolding bridge to Mathlib's `CondIndepFun` with the comap σ-algebra | **Proved** (`id`) |
| `POSystem.condIndepCF_congr_cond` | `comap c.value = comap c'.value → P.CondIndepCF a B c μ → P.CondIndepCF a B c' μ` | Transports conditional independence across conditioning variables that generate the same σ-algebra | **Proved** |
| `IndepCF.project` | `P.IndepCF a B μ → Measurable ψ → IndepFun a.value (ψ ∘ B.jointValue) μ` | Push `IndepCF` through an arbitrary measurable projection `ψ : (∀ i, B.type i) → β` — replaces open-coded `.comp measurable_id` dances in ATE/LATE | **Proved** |
| `IndepCF.component` | `P.IndepCF a B μ → (i : Fin B.n) → IndepFun a.value (fun ω ↦ B.jointValue ω i) μ` | Specialisation of `project` to single-coordinate extraction (e.g. pick out `Y(d)` from a joint cf bundle) | **Proved** |
| `CondIndepCF.project` | `P.CondIndepCF a B c μ → Measurable ψ → CondIndepFun (comap c.value _) _ a.value (ψ ∘ B.jointValue) μ` | Analogue of `IndepCF.project` at the conditional-independence level | **Proved** |
| `CondIndepCF.component` | `P.CondIndepCF a B c μ → (i : Fin B.n) → CondIndepFun (comap c.value _) _ a.value (fun ω ↦ B.jointValue ω i) μ` | Analogue of `IndepCF.component` at the conditional-independence level | **Proved** |

### `PO/Conditioning/Bundle.lean` — Bundle-conditioned conditional expectation

Lifts the single-`POVar` conditioning machinery in `CondExpTooling.lean` to a
`POCFBundle`, i.e. conditioning on the *joint* cf-value map of a tuple of
regimed variables.  The conditioning σ-algebra `B.sigma` is
`MeasurableSpace.comap B.jointValue inferInstance`.  Used by the multi-stage
DTR / sequential-backdoor identification arguments (`PO/ID/Exact/DTR/`)
where the conditioning σ-algebra is generated by a *bundle* of covariates rather
than a single one; mirrors all the lemmas of `POVar.condExpGiven` /
`POVar.condExpRatio` at the bundle level.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POCFBundle.sigma B` | `MeasurableSpace P.Ω` | `MeasurableSpace.comap B.jointValue inferInstance` — the σ-algebra generated by the bundle's joint cf-value map | **Defined** |
| `POCFBundle.sigma_le` | `B.sigma ≤ inferInstance` | `B.sigma` is a sub-σ-algebra of the ambient σ-algebra on `P.Ω` | **Proved** |
| `POCFBundle.condExpGiven B g μ` | `POCFBundle P → (P.Ω → ℝ) → Measure P.Ω → (P.Ω → ℝ)` | `μ[g \| B.sigma]` — Mathlib `condExp` on the bundle's comap σ-algebra (bundle analogue of `POVar.condExpGiven`) | **Defined** |
| `POCFBundle.stronglyMeasurable_condExpGiven_comap` | `StronglyMeasurable[B.sigma] (B.condExpGiven g μ)` | `condExpGiven g` is strongly measurable w.r.t. the sub-σ-algebra `B.sigma` | **Proved** |
| `POCFBundle.stronglyMeasurable_condExpGiven` | `StronglyMeasurable (B.condExpGiven g μ)` | `condExpGiven g` is strongly measurable w.r.t. the ambient σ-algebra | **Proved** |
| `POCFBundle.integrable_condExpGiven` | `Integrable (B.condExpGiven g μ) μ` | `condExpGiven g` is integrable | **Proved** |
| `POCFBundle.condExpGiven_tower_of_le` | `m ≤ B.sigma → [SigmaFinite (μ.trim _)] → μ[B.condExpGiven g μ \| m] =ᵐ[μ] μ[g \| m]` | Tower property against an arbitrary smaller sub-σ-algebra `m ≤ B.sigma`; bundle analogue of `POVar.condExpGiven_tower_of_le` | **Proved** |
| `POCFBundle.condExpGiven_mul_of_stronglyMeasurable_left` | `StronglyMeasurable[B.sigma] f → Integrable (f*g) μ → Integrable g μ → B.condExpGiven (f*g) μ =ᵐ[μ] f * B.condExpGiven g μ` | Pull-out-left: a `B.sigma`-measurable factor pulls outside `μ[·\|B.sigma]` | **Proved** |
| `POCFBundle.condExpGiven_mul_of_stronglyMeasurable_right` | Symmetric right-pull-out | Pull-out-right form of the same identity | **Proved** |
| `POCFBundle.condExpGiven_indicator_mul` | `MeasurableSet[B.sigma] s → … → B.condExpGiven (1_s * g) μ =ᵐ[μ] 1_s * B.condExpGiven g μ` | Specialisation of pull-out-left to indicators of `B.sigma`-measurable sets | **Proved** |
| `POCFBundle.condExpGiven_congr_ae` | `f =ᵐ[μ] g → B.condExpGiven f μ =ᵐ[μ] B.condExpGiven g μ` | a.e. congruence: equal-a.e. integrands give equal-a.e. bundle conditional expectations | **Proved** |
| `POCFBundle.condExpRatio B g h μ` | `POCFBundle P → (P.Ω → ℝ) → (P.Ω → ℝ) → Measure P.Ω → (P.Ω → ℝ)` | Pointwise ratio `B.condExpGiven g μ / B.condExpGiven h μ` — bundle analogue of `POVar.condExpRatio`, used to package the inner/outer adjusted regressions in DTR | **Defined** |
| `POCFBundle.measurable_condExpRatio` | `Measurable (B.condExpRatio g h μ)` | Pointwise-division measurability of `condExpRatio` | **Proved** |
| `POCFBundle.stronglyMeasurable_condExpRatio` | `StronglyMeasurable (B.condExpRatio g h μ)` | Strong measurability of `condExpRatio` | **Proved** |
| `POCFBundle.condExpRatio_eq_of_mul` | `B.condExpGiven g μ =ᵐ B.condExpGiven h μ * target → (∀ᵐ ω, B.condExpGiven h μ ω ≠ 0) → B.condExpRatio g h μ =ᵐ[μ] target` | Product→ratio characterisation; the exact shape consumed by `cdtr_backdoor` | **Proved** |
| `POSystem.CondIndepCFBundle` | `RegimedVar P α → POCFBundle P → POCFBundle P → Measure P.Ω → Prop` | Bundle-conditioned conditional independence: `CondIndepFun C.sigma C.sigma_le a.value B.jointValue μ` — bundle analogue of `POSystem.CondIndepCF`; requires `StandardBorelSpace P.Ω` | **Defined** |
| `CondIndepCFBundle.toCondIndepFun` | `P.CondIndepCFBundle a B C μ → CondIndepFun C.sigma C.sigma_le a.value B.jointValue μ` | Trivial unfolding bridge to Mathlib's `CondIndepFun` against `C.sigma` | **Proved** (`id`) |
| `CondIndepCFBundle.project` | `P.CondIndepCFBundle a B C μ → Measurable ψ → CondIndepFun C.sigma C.sigma_le a.value (ψ ∘ B.jointValue) μ` | Push `CondIndepCFBundle` through an arbitrary measurable projection of the bundle joint value — analogue of `CondIndepCF.project` for bundle-conditioned CI | **Proved** |

### `PO/Conditioning/EventCondExp.lean` — Event-level conditional expectation and drop-of-conditioning

Thin wrapper around `∫_A g ∂μ / (μ A).toReal` paired with a **drop-of-conditioning**
lemma: when the event-defining variable is `IndepCF` of a bundle `B`,
conditioning on a `value = x` event has no effect on `∫ h ∘ B.jointValue`.
Both multiplied and quotient forms are provided.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `eventCondExp μ A g` | `ℝ`, defined as `(∫ ω in A, g ω ∂μ) / (μ A).toReal` | Event-level conditional expectation, packaging the hand-rolled `condExpDZ` / `condExpYZ` idiom as a standalone operator | **Defined** |
| `eventCondExp_mul_measure_toReal` | `[IsFiniteMeasure μ]`, `A : Set Ω`, `f : Ω → ℝ` → `eventCondExp μ A f * (μ A).toReal = ∫ ω in A, f ω ∂μ` | Quotient-to-set-integral conversion (including the zero-measure case, where both sides collapse to `0`). Domain-agnostic; consumed by the Fintype total law below and by the Manski MTR/MTS set-integral manipulations | **Proved** |
| `integral_eq_sum_measure_mul_eventCondExp` | `[Fintype ι]`, `[IsFiniteMeasure μ]`, `A : ι → Set Ω` measurable / pairwise disjoint / covering `univ`, `f` integrable → `∫ f = ∑ i, (μ (A i)).toReal * eventCondExp μ (A i) f` | **Finite-partition total law.** Instantiates at `ι := Bool` for `Manski/{MTR,MTS}` binary decompositions and at `ι := α` (discrete IV value space) for the integrated MIV bounds. Domain-agnostic — an upstream-ready identity | **Proved** |
| `eventCondExp_eq_sum_condProb_mul_eventCondExp` | `[Fintype ι]`, `[IsFiniteMeasure μ]`, `A` measurable, `C : ι → Set Ω` measurable / pairwise disjoint / covering `univ`, `f` integrable → `eventCondExp μ A f = ∑ i, (μ (A ∩ C i)).toReal / (μ A).toReal * eventCondExp μ (A ∩ C i) f` | **Conditional finite-partition total law (law of iterated expectations).** `E[f∣A] = ∑ i P(C i∣A)·E[f∣A ∩ C i]`. The measure-theoretic core of the finite→population bridge for cell-indexed estimands: a finite covariate-weighted average of within-cell means equals the population conditional expectation `E[f∣G=g]` when the weights are the conditional cell probabilities. Domain-agnostic | **Proved** |
| `eventCondExp_congr_ae` | `f =ᵐ[μ] g → eventCondExp μ A f = eventCondExp μ A g` | a.e.-equal integrands give equal `eventCondExp`; shared congruence used across DID / Manski consistency rewrites | **Proved** |
| `eventCondExp_congr_on` | `MeasurableSet A → (∀ ω ∈ A, f ω = g ω) → eventCondExp μ A f = eventCondExp μ A g` | Equal-on-`A` integrands give equal `eventCondExp`; specialisation of the a.e. version to a pointwise identity on a measurable set | **Proved** |
| `eventCondExp_mono_ae` | `IntegrableOn f A μ → IntegrableOn g A μ → f ≤ᵐ[μ] g → eventCondExp μ A f ≤ eventCondExp μ A g` | Monotonicity of `eventCondExp` under an a.e. inequality of integrable functions; workhorse of the Manski stratum-sandwich bounds | **Proved** |
| `eventCondExp_add` | `IntegrableOn g₁ A μ`, `IntegrableOn g₂ A μ` → `eventCondExp μ A (g₁ + g₂) = eventCondExp μ A g₁ + eventCondExp μ A g₂` | Additivity | **Proved** |
| `eventCondExp_sub` | Analogous subtraction identity | Subtraction | **Proved** |
| `eventCondExp_smul` | `eventCondExp μ A (c • g) = c * eventCondExp μ A g` | Scalar linearity | **Proved** |
| `eventCondExp_of_ae_eq_IndepFun` | `IndepFun z B μ`, measurable `z`, `B`, `h`, `factualF =ᵐ[μ.restrict (z ⁻¹' {x})] h ∘ B`, `0 < (μ (z ⁻¹' {x})).toReal` → `eventCondExp μ (z ⁻¹' {x}) factualF = ∫ h (B ω) ∂μ` | Plain-`IndepFun` consistency-on-cell + drop-of-conditioning helper, reusable when the event variable is not packaged as a `POVar`; used by Angrist-Imbens factual Wald reductions | **Proved** |
| `POSystem.integral_restrict_value_eq_mul_of_IndepCF` | `P.IndepCF rv B μ`, `Measurable h` → `∫ ω in rv.value ⁻¹' {x}, h (B.jointValue ω) ∂μ = (μ (rv.value ⁻¹' {x})).toReal * ∫ ω, h (B.jointValue ω) ∂μ` | Drop-of-conditioning (multiplied form): the core identity, direct application of `IndepFun.integral_restrict_preimage_eq_mul` | **Proved** |
| `POSystem.integral_event_eq_mul_of_IndepCF` | Same identity with `A = a.event x` for factual `POVar a` | Specialisation to the factual event `{a = x}` | **Proved** |
| `POSystem.eventCondExp_eq_integral_of_IndepCF` | Under `IndepCF` and `μ A ∉ {0, ⊤}`, `eventCondExp μ (rv.value ⁻¹' {x}) (h ∘ B.jointValue) = ∫ h ∘ B.jointValue ∂μ` | Quotient form of drop-of-conditioning | **Proved** |
| `POSystem.eventCondExp_event_eq_integral_of_IndepCF` | Quotient form specialised to `a.event x` | Specialisation used directly in `late_wald`-style derivations | **Proved** |
| `POSystem.eventCondExp_of_consistency_IndepCF` | `P.IndepCF (ofFactual a) B μ`, `Measurable h`, `(∀ ω ∈ a.event x, factualF ω = h (B.jointValue ω))`, `μ (a.event x) ∉ {0, ⊤}` → `eventCondExp μ (a.event x) factualF = ∫ h (B.jointValue ω) ∂μ` | Workhorse combo: consistency-on-event rewrite + drop-of-conditioning in one call; collapses the repeated `hCE` blocks of `first_stage_identity` / `reduced_form_identity` | **Proved** |

### `PO/Conditioning/EventCondExpBundle.lean` — bundle analogue of `eventCondExp_of_consistency_IndepCF`

Lifts the single-period `EventCondExp` workhorse to the bundle-conditional setting (`P.CondIndepCFBundle a B C`) used by the Dynamic LATE bridges.  Per-stage workhorse: under bundle-conditional independence + consistency-on-event, the bundle conditional expectation of `factualF · 1_{a=x}` factors into the conditional expectation of `h ∘ B.jointValue` times the conditional expectation of `1_{a=x}`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POCFBundle.condExpGiven_mul_of_consistency_CondIndepCFBundle` | `P.CondIndepCFBundle (ofFactual a) B C μ`, `Measurable h`, `(factualF · 1_{a=x}) =ᵐ (h ∘ B.jointValue) · 1_{a=x}` → `C.condExpGiven (factualF · 1_{a=x}) =ᵐ C.condExpGiven (h ∘ B.jointValue) · C.condExpGiven (1_{a=x})` | Product form of the bundle workhorse.  Proof reduces to `Causalean.condExp_mul_of_condIndep` with `f := a.factual`, `g := B.jointValue`, `u y := ({x} : Set α).indicator 1`, `v := h`, exploiting `(RegimedVar.ofFactual a).value = a.factual` (rfl). | **Proved** |
| `POCFBundle.condExpRatio_of_consistency_CondIndepCFBundle` | Same hypotheses + `∀ᵐ ω, C.condExpGiven (1_{a=x}) ω ≠ 0` → `C.condExpRatio (factualF · 1_{a=x}) (1_{a=x}) =ᵐ C.condExpGiven (h ∘ B.jointValue)` | Ratio form, derived from the product form via `condExpRatio_eq_of_mul`. | **Proved** |

### `PO/Conditioning/CondExpTooling.lean` — σ-algebra-based conditional expectation

Thin wrapper around `MeasureTheory.condExp` keyed by the factual map of a
`POVar`.  Continuous-`X` companion to the event-based `eventCondExp` in
`EventCondExp.lean`; used by the backdoor ATE argument under the PO
framework, where the conditioning covariate may be continuous and the
integrand has the shape `Y(d)·1{D=d}` or `1{D=d}`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POVar.condExpGiven c g μ` | `POVar P γ → (P.Ω → ℝ) → Measure P.Ω → (P.Ω → ℝ)` | `μ[g \| σ(c.factual)]` — Mathlib `condExp` on the comap σ-algebra generated by `c.factual` | **Defined** |
| `POVar.comap_factual_le` | `MeasurableSpace.comap c.factual inferInstance ≤ mΩ` | The conditioning σ-algebra `σ(c.factual)` is a sub-σ-algebra of the ambient one on `P.Ω` | **Proved** |
| `POVar.condExpGiven_add` | `Integrable f μ → Integrable g μ → c.condExpGiven (f+g) μ =ᵐ[μ] c.condExpGiven f μ + c.condExpGiven g μ` | Additivity of `condExpGiven` (a.e.) | **Proved** |
| `POVar.condExpGiven_sub` | Analogous subtraction identity | Subtraction linearity of `condExpGiven` (a.e.) | **Proved** |
| `POVar.condExpGiven_smul` | `c.condExpGiven (k • g) μ =ᵐ[μ] k • c.condExpGiven g μ` | Scalar homogeneity of `condExpGiven` (a.e.) | **Proved** |
| `POVar.stronglyMeasurable_condExpGiven_comap` | `StronglyMeasurable[σ(c.factual)] (c.condExpGiven g μ)` | `condExpGiven g` is strongly measurable w.r.t. the sub-σ-algebra `σ(c.factual)` | **Proved** |
| `POVar.stronglyMeasurable_condExpGiven` | `StronglyMeasurable (c.condExpGiven g μ)` | `condExpGiven g` is strongly measurable w.r.t. the ambient σ-algebra | **Proved** |
| `POVar.integrable_condExpGiven` | `Integrable (c.condExpGiven g μ) μ` | `condExpGiven g` is integrable | **Proved** |
| `POVar.integrable_mul_indicator` | `Integrable f P.μ → Measurable f → Integrable (fun ω => f ω * a.indicator x ω) P.μ` | Multiplication by a factual `{0,1}`-valued `POVar` indicator preserves integrability; removes repeated bounded-indicator proofs in ATE, DTR, and Manski arguments | **Proved** |
| `POVar.condExpGiven_mul_of_stronglyMeasurable_left` | `StronglyMeasurable[σ(c.factual)] f → Integrable (f*g) μ → Integrable g μ → c.condExpGiven (f*g) μ =ᵐ[μ] f * c.condExpGiven g μ` | Pull-out-left: a `σ(c.factual)`-measurable factor pulls outside `μ[·\|σ(c.factual)]` | **Proved** |
| `POVar.condExpGiven_mul_of_stronglyMeasurable_right` | Symmetric right-pull-out | Pull-out-right form of the same identity | **Proved** |
| `POVar.condExpGiven_indicator_mul` | `MeasurableSet[σ(c.factual)] s → … → c.condExpGiven (1_s * g) μ =ᵐ[μ] 1_s * c.condExpGiven g μ` | Specialisation of pull-out-left to indicators of `σ(c.factual)`-measurable sets | **Proved** |
| `POVar.condExpGiven_tower_of_le` | `m ≤ σ(c.factual) → [SigmaFinite (μ.trim …)] → μ[c.condExpGiven g μ \| m] =ᵐ[μ] μ[g \| m]` | Tower property against an arbitrary smaller sub-σ-algebra `m ≤ σ(c.factual)` | **Proved** |
| `POVar.condExpGiven_tower` | Between two POVars with `σ(c₁.factual) ≤ σ(c₂.factual)`: `c₁.condExpGiven (c₂.condExpGiven g μ) μ =ᵐ[μ] c₁.condExpGiven g μ` | Two-POVar tower property | **Proved** |
| `POVar.condExpRatio c g h μ` | `POVar P γ → (P.Ω → ℝ) → (P.Ω → ℝ) → Measure P.Ω → (P.Ω → ℝ)` | Pointwise ratio `c.condExpGiven g μ / c.condExpGiven h μ` — the adjusted-regression functional used in backdoor ATE | **Defined** |
| `POVar.measurable_condExpRatio` | `Measurable (c.condExpRatio g h μ)` | Pointwise-division measurability of `condExpRatio` | **Proved** |
| `POVar.stronglyMeasurable_condExpRatio` | `StronglyMeasurable (c.condExpRatio g h μ)` | Strong measurability of `condExpRatio` | **Proved** |
| `POVar.condExpRatio_eq_of_mul` | `c.condExpGiven g μ =ᵐ c.condExpGiven h μ * target → (∀ᵐ ω, c.condExpGiven h μ ω ≠ 0) → c.condExpRatio g h μ =ᵐ[μ] target` | Product→ratio characterisation; the exact shape consumed by `cate_backdoor` Step 4 | **Proved** |
| `POVar.integral_sub_eq_integral_sub_of_condExpGiven_ae_eq` | `Integrable f μ`, `Integrable g μ`, `c.condExpGiven f μ =ᵐ f'`, `c.condExpGiven g μ =ᵐ g'` → `∫ (f - g) ∂μ = ∫ (f' - g') ∂μ` | CATE-to-ATE integrator: lifts an a.e. identity of conditional expectations to an identity of unconditional integrals of differences; closes `ate_backdoor` in one line | **Proved** |

---

### `PO/Analysis/Quantile.lean` — Distribution, cdf, and quantile of a real potential outcome

Distributional reading of a real-valued potential outcome: for a real `POVar a`
and regime `r`, the counterfactual `a.cf r : P.Ω → ℝ` has a law, cdf, and
quantile. Gives meaning to "the `τ`-quantile of `Y(d)`"; input to the QTE
(`PO/ID/Exact/QTE/QuantileEffect.lean`). Builds on `Stat/Quantile/Quantile.lean`.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POVar.cfLaw a r μ` | `Measure ℝ` | Law of the potential outcome `a(r)`: `μ.map (a.cf r)`. | **Defined** |
| `POVar.instIsProbabilityMeasureCfLaw` | instance | `cfLaw` is a probability measure when `μ` is. | **Proved** |
| `POVar.cfCDF a r μ` | `StieltjesFunction ℝ` | Distributional potential outcome `F_{a(r)} = cdf (a.cfLaw r μ)`. | **Defined** |
| `POVar.cfQuantile a r μ τ` | `ℝ` | `τ`-quantile of `a(r)`: `Stat.quantile (a.cfLaw r μ) τ`. | **Defined** |
| `POVar.cfCDF_eq_measureReal` | `a.cfCDF r μ y = (a.cfLaw r μ).real (Iic y)` | The cdf at `y` is `P(a(r) ≤ y)`. | **Proved** |
| `POVar.cfUnderLaw a w y μ` | `Measure ℝ` | Law of `a` under single intervention `{w ← y}` (the `Y(d)` shape). | **Defined** |
| `POVar.cfUnderQuantile a w y μ τ` | `ℝ` | `τ`-quantile of `a` under `{w ← y}` — the `τ`-quantile of `Y(d)`. | **Defined** |
| `POVar.cfUnderQuantile_eq` | `= Stat.quantile (a.cfUnderLaw w y μ) τ` | Unfolds `cfUnderQuantile` to the law-quantile. | `rfl` |

## 9. `SCM/ID/Identifiable.lean` — Identifiability

Namespace: `Causalean.SCM.ID`.

### Identifiability definitions

Identifiability is phrased in terms of **measure-theoretic observational
equivalence** against the SCM observational kernel: `obsEquiv M₁ M₂` is
`HEq` of `Causalean.SCM.obsKernel M₁` and `Causalean.SCM.obsKernel M₂` (the `HEq`
is necessary because `obsKernel` has dependent domain/codomain via
`FixedValues M` and `ObservedValues M`).

| Definition | Signature | Description |
|---|---|---|
| `CausalQuery` | `SCM N Ω → α` | Functional of a gSCM (ATE, LATE, interventional law, etc.) |
| `obsEquiv` | `SCM N Ω → SCM N Ω → Prop` | `HEq (SCM.obsKernel M₁) (SCM.obsKernel M₂)` |
| `Identifiable` | `SWIGGraph N → CausalQuery N Ω α → Prop` | Same SWIG graph (`M.toSWIGGraph = G`, pinning observed/latent/fixed + edges) + `obsEquiv` ⟹ same query value. Faithful to `def:scm-identifiability` (model class shares a SWIG graph, not merely a DAG) |
| `NonIdentifiable` | `SWIGGraph N → CausalQuery N Ω α → Prop` | Negation of `Identifiable` |
| `IdentifiableUnder` | `SWIGGraph N → Af → As → CausalQuery N Ω α → Prop` | Identifiable given functional (`Af`) and structural (`As`) assumption predicates over `SCM N Ω`, within the model class sharing SWIG graph `G` |

### Theorems

| Theorem | Statement | Description |
|---|---|---|
| `nonIdentifiable_iff` | Non-identifiability iff there exist two models with the same SWIG graph and `obsEquiv` but different query values | Equivalence characterization of non-identifiability |
| `identifiable_eq_identifiableUnder_true` | Identifiability without assumptions is the special case `Af = As = fun _ => True` | Links unconditional identifiability to `IdentifiableUnder` with trivial assumptions |
| `identifiableUnder_mono` | Stronger assumptions `(Af₂, As₂)` that imply `(Af₁, As₁)` preserve identifiability | Monotonicity: identifiability under weaker assumptions follows from identifiability under stronger ones |

---

## 9a. `SCM/ID/Overlap.lean` — Rule 2 / backdoor overlap predicate

The kernel-level absolute-continuity overlap predicate consumed by the
kernel-native do-calculus Rule 2 and the backdoor / frontdoor identification
theorems.  (The quantitative small-value/weak-overlap rate analysis — polynomial
lower-tail inverse moments — is developed separately under `Stat/PolynomialTail/`.)

| Definition | Signature | Description | Status |
|---|---|---|---|
| `Rule2JointOverlap M' Z hZ_obs hZ_fixed W hZrW s'` | `Prop` | **Canonical Rule 2 overlap.** Absolute continuity `((M'.fixSet Z).obsKernel s').map π_{Zr∪W} ≪ (M'.obsKernel ∘ fixSetProj s').map π_{Zr∪W}` — a kernel-level AC predicate with no pointwise singleton positivity requirement. Holds trivially in the discrete case; holds in the continuous case whenever the SCM's structural functions are measurable and latents match. Hypothesis of `obsCondKernel_fixSet_eq_ae_witness` (canonical posterior witness-kernel Rule 2) and through it of `do_rule2_kernel` and backdoor / frontdoor identification. | Complete |

Reference: Basic Concepts.tex, Definition 2.12 (Overlap assumption).

---

## 9b. Structural Assumption Ownership

Causalean no longer carries a standalone IV/DID/RDD/proxy assumption catalogue.
Structural assumptions are owned by the theorem module that consumes them
(`PO/ID/Exact/*`, `PO/ID/Partial/*`, or downstream CausalSmith artifacts), while
`SCM/ID/Identifiable.lean` still provides generic `Prop`-valued assumption slots
for abstract identifiability statements.

---

## 9c. `SCM/ID/GraphicalThms/` — Graphical Identification Theorems

Formalizes Basic Concepts.tex §4.1.  Several live files:

* `InducedSubgraph.lean` — graph-only utilities (ancestral closure,
  proper-descendant / non-descendant sets in `G_R`).
* `CComponentFactor.lean` — c-factor definition (`qFactor`),
  c-component parent helpers, and the per-node chain-rule factorization
  theorem `M.obsKernel s = M.qFactorProduct s` (Tian full-history
  convention).
* `QFactorIdentity.lean` — Tian's Q-factor identity (Prop 2.19),
  intervention-target simplification (`fact4`), and the district-id
  corollary.  The Q-factor identity is currently formalized as the
  real marginal fixing identity obtained from Rule 3 and
  `induce_marginal_compat`; the final conditional-`qFactor` reindexing
  remains future work.

The old kernel-era files (`Fixable.lean`, `FixingStep.lean`,
`CFactor.lean`) are **archived** under
`archive/SCM/ID/GraphicalThms/`.  The Shpitser–Pearl c-component
recursion (the chosen design path for the Session-5 ID algorithm) does
not consume the fixing-step machinery, so it is no longer in the build.

### `InducedSubgraph.lean`

| Definition | Description |
|---|---|
| `SWIGGraph.isAncestrallyClosed` | Every observed parent of `v ∈ G.observed` is itself in `G.observed`; `Decidable` |
| `InducedFrom G R` | `G.induce R` — the `G_R` notation from the tex |
| `SWIGGraph.properDescIn G R v₀` | `D := (G.induce R).dag.descendants v₀` — proper descendants of `v₀` in `G_R`; `DAG.descendants` is already irreflexive |
| `SWIGGraph.nonDescIn G R v₀` | `T := (R.erase v₀) \ (G.induce R).dag.descendants v₀` — non-descendants of `v₀` in `G_R`, matching the tex convention that `De(v₀)` includes `v₀` |
| `v₀_not_mem_properDescIn` | `v₀ ∉ G.properDescIn R v₀` — irreflexivity |
| `v₀_not_mem_nonDescIn` | `v₀ ∉ G.nonDescIn R v₀` — by the `erase` in the definition |
| `properDescIn_subset_erase` | `G.properDescIn R v₀ ⊆ R.erase v₀` — **sorry** (needs `descendants_induce_subset`) |
| `nonDescIn_subset_erase` | `G.nonDescIn R v₀ ⊆ R.erase v₀` — proven via `Finset.sdiff_subset` |
| `nonDescIn_subset` | `G.nonDescIn R v₀ ⊆ R` |
| `properDescIn_disjoint_nonDescIn` | `Disjoint (properDescIn R v₀) (nonDescIn R v₀)` |
| `properDescIn_union_nonDescIn_eq_erase` | `D ∪ T = R.erase v₀` (for `v₀ ∈ R`) — **sorry** (needs the subset helper) |

### `CComponentFactor.lean` — c-component factorization (Tian, 2002)

Formalizes `thm:scm-c-factor` (Basic Concepts.tex:662–672) against
`obsKernel`.  The Pa⁺ semantics is the standard Tian (2002) convention:
*topological predecessors*, i.e. observed nodes preceding `v` in a fixed
topological order — not the direct-parent set.

| Definition / Statement | Description |
|---|---|
| `SWIGGraph.observedPredecessors v` | `Pa⁺_G(v) := {w ∈ G.observed | topoOrder w < topoOrder v}` |
| `SWIGGraph.qFactorParents C` | `(⋃_{v ∈ C} Pa⁺_G(v)) \ C` — conditioning set of `Q[C]` |
| `observedPredecessors_subset_observed` / `qFactorParents_subset_observed` | sanity lemmas (proven) |
| `SCM.qFactor M C hC s` | Tian's c-component factor `Q[C]` as a slice of `obsCondKernel M C (qFactorParents C)` at `s` (via `Kernel.comap`); requires `StandardBorelSpace`, `Nonempty`, `IsFiniteMeasure`, `CountableOrCountablyGenerated` instances |
| `SCM.c_component_factorization` | `M.obsKernel s = M.qFactorProduct s`; per-node chain-rule factorization over observed nodes, now sorry-free via `obsKernel_eq_qFactorProduct`; c-component grouping is deferred to a later theorem |

### `QFactorIdentity.lean`

Hypothesis-quantified frames for Tian's identity, fact4, and the
district-id corollary.  The statements are non-vacuous: Tian's identity is the
conditional q-factor equality (a.e. under the induced parent marginal), the
marginal fixing identity is retained as a proved helper, and fact4 is an
`SCM.Equiv` statement.

| Statement | Description | Status |
|---|---|---|
| `QFactorMarginalFixingConclusion M R T Wn` | Under ancestral closure, `T ⊆ (M.induce R).observed`, `Wn.image .random = R \ T`, and the Rule-3 non-descendant condition on `T`, the `T`-marginal of `(M.fixSet Wn).obsKernel` equals the `T`-marginal of `(M.induce R).obsKernel` at the projected fixed slice | **Proved** marginal fixing identity |
| `q_factor_marginal_fixing` | Proves the marginal fixing form by composing `condDistrib_intervention_ancestral_eq` with `induce_marginal_compat` and projection composition | **Proved** |
| `QFactorIdentityConclusion M R T Wn` | Conditional Tian identity: the induced `qFactor (M.induce R) T` equals a.e. the `T | qFactorParents T` conditional extracted from `(M.fixSet Wn).obsKernel`, with the non-descendant condition strengthened to `T ∪ qFactorParents T` for the needed joint identity | Real conditional statement |
| `q_factor_identity` | Proves the conditional Q-factor identity by first deriving the joint law identity on `T ∪ qFactorParents T`, reindexing it to the `(qFactorParents T, T)` pair law, then applying `Kernel.condKernel` uniqueness/disintegration under the common parent marginal | **Proved** |
| `InterventionTargetSimpConclusion M Dn Yn T` | `SCM.Equiv ((M.fixSet Dn).fixSet Yn) (M.fixSet (Dn ∪ Yn))` under observed/fixed/disjointness well-formedness hypotheses | Real `SCM.Equiv` statement |
| `intervention_target_simp` | Proves `fact4` by Finset induction over `Yn`, using the singleton-insert composition helper | Proven modulo `swigInterventionSet_insert_equiv` |
| `SCM.swigInterventionSet_insert_equiv` | Structural equivalence between intervening on `X` then fresh `{y}` and intervening on `insert y X` in one shot | **Proved** |
| `DistrictIdConclusion M T Wn` | Specialization of `QFactorIdentityConclusion` at `R := M.observed` | `:= QFactorIdentityConclusion M M.observed T Wn` |
| `district_id` | Specializes `q_factor_identity` at `R := M.observed` | Direct specialization of the conditional Q-factor identity; **proved** |

### `Density/ReferenceMeasure.lean` — dominated-model density foundation

Namespace `Causalean.SCM`. Foundation for the **density-assisted** c-component
factorization: Tian's assembly `P(v) = ∏_C Q[C]` is a commutative regrouping of
scalar density factors with no kernel-composition analogue, so the
`doKernelY` identification (obligation 2) is routed through the joint density.
Unifies discrete (counting reference) and continuous (Lebesgue reference) models.

| Definition / Theorem | Signature / Statement | Description |
|---|---|---|
| `ReferenceMeasures Ω` | structure: `μ : ∀ v, Measure (swigΩ Ω v)` + per-node `SigmaFinite` | A σ-finite reference measure per SWIG-node value space (counting for discrete, Lebesgue for continuous) |
| `ReferenceFaithful ref` | `∀ v x, ref.μ v {x} ≠ 0` | Full-support condition for finite references; counting reference measures satisfy it |
| `jointRef ref I` | `Measure (ValuesOn I (swigΩ Ω))` | Finite product `Measure.pi` of the per-node references over a node set `I` |
| `DominatedObs M ref` | `∀ s, M.obsKernel s ≪ jointRef ref M.observed` | The gSCM's observational law is absolutely continuous w.r.t. the joint reference (admits a density) |
| `obsDensity M ref s` | `ValuesOn M.observed (swigΩ Ω) → ℝ≥0∞` | Joint observational density `(obsKernel s).rnDeriv (jointRef …)` |
| `withDensity_obsDensity_eq` | `DominatedObs M ref → (jointRef …).withDensity (obsDensity …) = obsKernel s` | Density determines the law (Proved) |
| `obsKernel_eq_of_obsDensity_ae_eq` | a.e.-equal `obsDensity` slices ⟹ equal `obsKernel` slices (single model) | Density injectivity used downstream for the soundness transport (Proved) |

### `Density/FiniteReference.lean` — finite discrete reference infrastructure

Namespace `Causalean.SCM`. Instances and helpers for the finite/discrete density
path: when every base-node value space is finite and has measurable singletons,
the SWIG value spaces and finite product references inherit the corresponding
finite/measurable structure needed by the finite-reference RN chain rule.

| Definition / Theorem | Signature / Statement | Description |
|---|---|---|
| `instFintypeSwigΩ` / `instMeasurableSingletonClassSwigΩ` | `[∀ n, Fintype (Ω n)]` / `[∀ n, MeasurableSingletonClass (Ω n)]` ⟹ the same instances for `swigΩ Ω sn` | Transfers finite and singleton-measurable structure from base nodes to random/fixed SWIG nodes |
| `isFiniteMeasure_of_finite_measurableSingleton` | a σ-finite measure on a finite measurable-singleton type is finite | Generic finite-space measure helper, proved by covering the space with finitely many measurable singletons |
| `instIsFiniteMeasure_refMu` / `instIsFiniteMeasure_jointRef` | finite node spaces ⟹ `IsFiniteMeasure (ref.μ v)` and `IsFiniteMeasure (jointRef ref I)` | Supplies the finite fibre and finite product-reference instances used by discrete density proofs |
| `jointRef_singleton_ne_zero` / `absolutelyContinuous_jointRef_of_faithful` | `ReferenceFaithful ref` ⟹ every product singleton has nonzero `jointRef` mass, hence every measure on the finite coordinate product is `≪ jointRef ref I` | Full-support infrastructure used to prove do-law ancestral marginal domination |
| `aemeasurable_fiber_rnDeriv_of_finite` | any raw fibre RN selector `(κ p.1).rnDeriv ρ p.2` is a.e.-measurable on a finite measurable-singleton product | Discharges the explicit product a.e.-measurability hypothesis of the finite-reference composition-product RN lemma |

### `Density/PiUnion.lean` — `Measure.pi` over a disjoint union

Namespace `Causalean.SCM`. The reference-splitting foundation for the density chain
rule: `Measure.pi` over a disjoint union of coordinates factors as a product.

| Definition / Theorem | Signature / Statement | Description |
|---|---|---|
| `unionSumEquiv hDisj` | `({a // a ∈ A} ⊕ {b // b ∈ B}) ≃ {i // i ∈ A ∪ B}` | Index equivalence for disjoint `A`, `B` |
| `measurePreserving_valuesUnionEquiv` | `MeasurePreserving (valuesUnionEquiv hDisj) (Measure.pi μ_{A∪B}) ((Measure.pi μ_A).prod (Measure.pi μ_B))` | **`Measure.pi` over a disjoint union = the product measure.** Fully proved, axiom-clean; routes the project's union equiv through Mathlib `sumPiEquivProdPi` + `piCongrLeft` |

### `Density/ChainRuleDensity.lean` — observational chain-rule density

Namespace `Causalean.SCM`. Density analogue of the proven kernel chain rule:
the observational density is reduced to the scalar product of the
Radon--Nikodym derivatives of the one-node conditional kernels
`obsStepCondKernel`, evaluated along the observed topological order.

| Definition / Theorem | Signature / Statement | Description |
|---|---|---|
| `obsStepCondDensity M ref s i` | `ValuesOn M.observed (swigΩ Ω) → ℝ≥0∞` | One observed-coordinate conditional density: the RN derivative of `obsStepCondKernel i.isLt` against the node reference measure, evaluated at the prefix and coordinate read from a full observed assignment |
| `qFactorDensityProduct M ref s` | `ValuesOn M.observed (swigΩ Ω) → ℝ≥0∞` | Product over `Fin M.observed.card` of the per-node conditional density factors in observed topological order |
| `qFactorProduct_rnDeriv_eq_qFactorDensityProduct` | with finite measurable-singleton node spaces, `DominatedObs M ref → (M.qFactorProduct s).rnDeriv (jointRef ref M.observed) =ᵐ … qFactorDensityProduct …` | Analytic RN-derivative chain rule. **The `DominatedObs` hypothesis is essential** — false without it (singular part ⟹ vanishing rnDeriv vs nonzero conditional-density product). Fully proved in the finite-reference setting |
| `obsChainKernel_rnDeriv_eq_prefixDensityProduct` | with finite measurable-singleton node spaces, general-`k` prefix induction: `(obsChainKernel k s).rnDeriv (jointRef prefix k) =ᵐ prefixDensityProduct k` | **Proved.** Base on `ValuesOn ∅`; successor peels `extendObsPrefix` via `MeasurableEmbedding.rnDeriv_map`, splits via `jointRef_extendObsPrefix`, derives joint product domination from base and fibre domination, and uses finite-space measurability for the raw fibre derivative |

| `obsChainKernel_absolutelyContinuous_jointRef_prefix` | `M.obsChainKernel k hk s ≪ jointRef ref (M.prefixNodes k)` | **Proved (no Mathlib gap).** Chain = prefix marginal of the dominated `obsKernel`; the reference marginal is a scalar multiple of the prefix reference via the disjoint-union split (`measurePreserving_valuesUnionEquiv`) + `Measure.map_fst_prod` |
| `rnDeriv_compProd_prod_sigmaFinite` | `(μ ⊗ₘ κ).rnDeriv (ν.prod ρ) =ᵐ fun p => f p.1 * (κ p.1).rnDeriv ρ p.2`, for finite `μ`/`ρ`/`κ`, σ-finite `ν`, `μ ≪ ν`, **joint domination** `μ ⊗ₘ κ ≪ ν.prod ρ`, product a.e.-measurability of the raw fibre derivative, and `μ.rnDeriv ν =ᵐ f` | Finite-reference composition-product RN identity in `Causalean/Mathlib/MeasureTheory/RnDerivCompProdSigmaFinite.lean`. Finiteness of `ρ` makes `Kernel.const _ ρ` a finite kernel, so Mathlib extracts μ-a.e. fibre domination from joint domination. The raw `Measure.rnDeriv` fibre representative still carries an explicit product-measurability hypothesis; Mathlib's measurable representative is `Kernel.rnDeriv κ (Kernel.const _ ρ)` |
| `map_pi_valuesEquivOfEq`, `jointRef_prefix_card_map`, `singletonValues_map_ref_eq_jointRef`, `jointRef_extendObsPrefix`, `rnDeriv_compProd_same_left`, `absolutelyContinuous_of_map_measurableEmbedding`, `qFactorProduct_rnDeriv_eq_obsChainKernel_card_pullback_of_jointRef`, `obsChainKernel_card_rnDeriv_pullback_eq_qFactorDensityProduct_of_prefix` | reference reindex / singleton split / per-step `extendObsPrefix` reference split / embedding-pullback of `≪` / `rnDeriv_map` peels / a.e. transport | The transport + reference-split sub-lemmas of the chain rule — **all proved, axiom-clean** |
| `obsDensity_eq_qFactorDensityProduct` | with finite measurable-singleton node spaces, `M.obsDensity ref s =ᵐ[jointRef ref M.observed] M.qFactorDensityProduct ref s` | Dominated observational density factors as the product of one-node conditional densities; D1 is now sorry-free in the finite-reference setting |

### `Density/CComponentDensity.lean` — c-component regrouping of the density

Namespace `Causalean.SCM`. The commutative regrouping with **no kernel analogue**:
the scalar density product is collected by c-component. (Composed kernels can't
be permuted to gather a non-contiguous c-component's factors; scalar densities
can.)

| Definition / Theorem | Signature / Statement | Description |
|---|---|---|
| `cComponentDensityFactor M ref s C` | `ValuesOn M.observed (swigΩ Ω) → ℝ≥0∞` | Product of the one-node conditional density factors over the observed indices whose node lies in c-component `C` (density analogue of Tian's `Q[C]`) |
| `qFactorDensityProduct_eq_prod_cComponentFactor` | `M.qFactorDensityProduct ref s x = ∏ C ∈ cComponentSet, cComponentDensityFactor … C x` | The chain-rule density product regroups as a product over c-components. **Fully proved, axiom-clean** (pure `Finset.prod_fiberwise` regrouping; the kernel-impossible step) |

### Archived (under `archive/SCM/ID/GraphicalThms/`)

* `Fixable.lean` — `SWIGGraph.isFixable`, `isFixableSeq` (kernel-era; no
  longer used by the chosen Shpitser–Pearl recursion).
* `FixingStep.lean` — Lemma 1 skeleton.
* `CFactor.lean` — kernel-era c-factor (replaced by `CComponentFactor.lean`).

---

## 10. `SCM/Examples/IV.lean` — IV DAG Example

Demonstrates the full API on the standard instrumental variable DAG:

```
    U
   ↙ ↘
  Z → D → Y
```

**What it tests:**

| Module | Tests |
|---|---|
| `Graph/DAG.lean` | `parents`, `children`, `isRoot`, `isAncestor`, `isAncestor_irrefl/trans` |
| `Graph/DSep.lean` | `dSep` with various conditioning sets; collider bias; instrument independence |
| `Graph/SWIG.lean` | `SWIGGraph` construction; initial SWIG; SWIG edge tests |
| `Graph/CComponents.lean` | `directlyConfounded` on `SWIGGraph`; `cComponentOf` |
| `SCM/Model/EdgeType.lean` | `EdgeTypeAssignment`; monotonic vs nonparametric; `refines` |
| `SCM/Model/SCM.lean` | Trivial `Causalean.SCM` instance `ivSCM` with `ΩIV := fun _ => Unit`; `structFun` constant; `latentDist := Measure.dirac ()`; `iota_valueSpace` discharged via `Finset.notMem_empty`. Verifies `ivSCM.isStandard` |

---

## 10b. `SCM/Examples/BackDoor.lean` — Backdoor Adjustment Example

Demonstrates the backdoor criterion DAG:

```
    Z
   ↙ ↘
  D → Y
```

Observed: D (treatment), Y (outcome), Z (observed confounder). Latent roots U₁, U₂, U₃ added to satisfy `unobs_are_roots`.

**What it tests:**

| Module | Tests |
|---|---|
| `Graph/DAG.lean` | `parents`, `isRoot`, `isAncestor` (irreflexivity via `isAncestor_topoOrder_lt`) |
| `Graph/DSep.lean` | `dSep` for the observational graph; no d-separation by {Z} (direct edge D → Y remains open) |
| `Graph/SWIG.lean` | `SWIGGraph` construction with three latent roots; `swig_random_root_of_root` for each |
| `Graph/SWIGSplitMono.lean` | Backdoor condition (ii): `splitMonoDAG {bdD}` d-separates Y from D given Z, verified by `native_decide` on the computable `splitMonoDAG` |
| `Graph/CComponents.lean` | Each observed node is its own singleton C-component (no confounding) |
| `SCM/Model/EdgeType.lean` | `allNonparametric` edge type assignment |

The file now additionally demonstrates the full `bdSWIG.backdoorCriterion` on this concrete 3-node DAG.  Condition (i) (no `z ∈ Z` is a descendant of any `random D ∈ X`) is discharged by `native_decide` + `simp`.  Condition (ii) is routed through `splitMonoDAG` (since `splitMono` itself is `noncomputable`) and also closed by `native_decide`.  No full SCM is built — only the graphical criterion is exercised.

---

## 10c. `SCM/Examples/ContinuousBackdoor.lean` — Linear-Gaussian backdoor (continuous treatment)

Validation of the posterior witness-kernel backdoor pipeline: a 3-node SCM with continuous value spaces (`ℝ`) on every observed node, exercising `backdoor_completeness_ae` end-to-end on a treatment variable that is *not* discrete.

DAG: `Z → X`, `Z → Y`, `X → Y` (so `Z` is a backdoor-admissible confounder for the effect of `X` on `Y`).  All three observed nodes have value space `ℝ` (via `CBΩ : Fin 3 → Type := fun _ => ℝ`).  The latent set is empty, so the SCM is fully deterministic — the kernel-native pipeline does not need probabilistic latents to demonstrate the continuous-treatment regime; what matters is the continuity of the value spaces.

The example uses a *computable* SWIGGraph (`cbSWIGGraph`) so the backdoor criterion can be discharged via `native_decide` even though the parent `SCM` is `noncomputable` (carries `Measure`s).  `continuousBackdoorSCM.toSWIGGraph := cbSWIGGraph` definitionally.

| Declaration | Description |
|---|---|
| `CBNode`, `CBΩ` | Node set `Fin 3` (`Zidx = 0`, `Xidx = 1`, `Yidx = 2`) with continuous value spaces `ℝ` |
| `cbEdgeBool`, `cbEdge`, `cbDAG` | Edge relation (`Bool`-lifted for `decide`-friendly `Decidable`) and underlying DAG |
| `cbSWIGGraph` | Computable SWIGGraph (empty latents, `observed = {Z, X, Y}` as `.random` nodes), used for graphical criterion proofs |
| `continuousBackdoorSCM` | The full SCM: extends `cbSWIGGraph`, constant-`0` structural functions, empty `latentDist`.  Marked `noncomputable` only because of the `Measure` API in the SCM structure |
| `cb_Xrand_obs`, `cb_Xfixed` | Witnesses that `random X` is observed and `fixed X` is not in `fixed`; supplied to `backdoor_completeness_ae`'s subset-hypotheses |
| `cb_backdoor_criterion` | Discharges `cbSWIGGraph.backdoorCriterion {X} _ _ {Y} {Z}`.  Condition (i) (`Z` not descendant of `X`) by `native_decide`; condition (ii) (d-separation in splitMono) by `native_decide` on the computable `splitMonoDAG` |

**What this validates.**  Continuous value spaces (`ℝ`) flow through the kernel-native pipeline (`obsKernel`, `obsCondKernel`, `Rule2JointOverlap`, `backdoor_completeness_ae`), and `SWIGGraph.backdoorCriterion` discharges by `native_decide` on the continuous SCM.  This example is sorry-free.

---

## 9d. `SCM/ID/Adjustment.lean` — Adjustment Functionals

Graph-level adjustment functionals that turn an SCM's observational
kernel into a post-intervention `Y`-marginal kernel under the backdoor
or frontdoor criterion.  The split into a *single-SCM completeness*
lemma plus a *cross-SCM congruence* lemma factors the cross-SCM HEq
plumbing out of the do-calculus assembly in `SCM/ID/Backdoor.lean` /
`PO/ID/Exact/Frontdoor.lean`.

| Definition / Statement | Description |
|---|---|
| `SCM.backdoorAdjustment M X hX_obs hX_fixed Y Z hY hZ` | Kernel `Kernel (M.fixSet X).FixedValues (ValuesOn Y _)` implementing `∫_z P(Y \| X, Z=z) dP(z)` as a kernel-native `((zMarginalPost ⊗ₖ M.obsCondKernel Y (X.image .random ∪ Z)).comap ...).map Prod.snd` chain.  The conditional's `(X.image .random ∪ Z)`-argument is assembled via `M.fillZrW X hX_obs hX_fixed Z s_post z`, which fills the `X.image .random` slice from `s_post` (reindexed from `X.image .fixed` through `zFixedAsRandom`) and pairs it with the outer `Z`-value `z` — routing through `fillZrW` (rather than an inline `valuesUnionMk ∘ zFixedAsRandom ∘ valuesProjection`) removes a reindexing-bridge gap in the downstream backdoor completeness proof.  Signature carries `[StandardBorelSpace (ValuesOn Y (swigΩ Ω))]`, `[Nonempty (ValuesOn Y (swigΩ Ω))]`, `[∀ s : M.FixedValues, IsFiniteMeasure (M.obsKernel s)]`, and a `CountableOrCountablyGenerated` instance for the conditional kernel |
| `SCM.frontdoorAdjustment M X hX_obs hX_fixed Y Z hY hZ` | **Proved** (sorry-free).  Kernel `Kernel (M.fixSet X).FixedValues (ValuesOn Y _)` implementing the frontdoor integral as a chain of `⊗ₖ` legs: outer X-marginal `(M.obsKernel.map projXr).comap fixSetProj`, middle `M.obsCondKernel Z (X.image .random)` (Rule 2 leg, `P(Z|X)`), inner `M.obsCondKernel Y (X.image .random ∪ Z)` (Rule 2 leg on inner `do(Z)`, with `X` as adjustment set).  The three kernels compose to `((xMarginal ⊗ₖ zCondX) ⊗ₖ yCondXZ).map Prod.snd`.  Signature requires `[StandardBorelSpace (ValuesOn Y _)]`, `[StandardBorelSpace (ValuesOn Z _)]`, `[Nonempty (ValuesOn Y _)]`, `[Nonempty (ValuesOn Z _)]`, `[StandardBorelSpace (ValuesOn (X.image .random) _)]`, `[StandardBorelSpace (ValuesOn (X.image .random ∪ Z) _)]`, `[∀ s, IsFiniteMeasure (M.obsKernel s)]`, and two `CountableOrCountablyGenerated` instances for the conditional kernels |
| `SCM.backdoorAdjustment_invariant` | **Proved** (sorry closed).  HEq cross-SCM invariance: two SCMs sharing `toSWIGGraph` and `obsKernel` produce the same `backdoorAdjustment` kernel.  Proof destructs both SCMs via `obtain`, `cases h_swig` unifies the SWIGGraph fields definitionally, then `apply heq_of_eq` reduces HEq to Eq. `eq_of_heq _h_obs` strips the obsKernel HEq; `unfold SCM.backdoorAdjustment` + nested `congr 1` peels off `.map Prod.snd` and `⊗ₖ`, leaving the `zMarginalPost` branch (closed by `rw [h_ok]`) and the `condPost` branch (closed by unfolding `obsCondKernel`/`obsCondPairKernel` and `rw [h_ok]`). Does not require `heq_obsCondKernel` — `cases h_swig` already aligns the kernel arguments |
| `SCM.frontdoorAdjustment_invariant` | **Proved** (sorry-free).  Same shape as `backdoorAdjustment_invariant`.  After destructure + `cases h_swig`, `unfold SCM.frontdoorAdjustment` exposes the `⊗ₖ` chain; unfolding `obsCondKernel`/`obsCondPairKernel` exposes the `condKernel`-of-`obsKernel.map`-joint pattern; `simp_rw [h_ok]` rewrites every `obsKernel` mention to the M₂-side, then `rfl` closes the remaining proof-irrelevance noise on `fixSetProj` (only SWIGGraph fields are used in `fixSetProj`; all unified after `cases h_swig`) |

---

## 9e. `SCM/ID/BackdoorCriterion.lean` — Backdoor criterion + Rule-3 leg

The graphical backdoor criterion (Basic Concepts.tex:636–645, Pearl 2009
Theorem 3.3.2) and the single regime-independent do-calculus leg the backdoor
identification proof consumes.  The identification *theorems* live in
`SCM/ID/Backdoor.lean` (§9e').

**Design note on condition (ii).**  `Graph/Mutilation.lean` is not yet
implemented, so the lower-bar mutilation `G_{X̲}` is encoded via
`SWIGGraph.splitMono X hX_obs hX_fix`: splitting `X` reroutes outgoing
edges of `random D` (for `D ∈ X`) to root nodes `fixed D`, which is
exactly the effect of lower-bar mutilation for d-separation purposes.

| Declaration | Description | Status |
|---|---|---|
| `SWIGGraph.backdoorCriterion G X hX_obs hX_fix Y Z` | Two-condition criterion: (i) no `z ∈ Z` is a descendant of any `random D` with `D ∈ X` in `G`; (ii) `Z ∪ X.image .fixed` d-separates `Y` from `X.image .random` in `G.splitMono X hX_obs hX_fix` (encodes `G_{X̲}` d-sep; fixed_X conditioning is vacuous in splitMono but carried to match `do_rule2`'s shape) | Defined; type-checks without sorry |
| `SCM.backdoor_rule3_Z_marginal` | **Rule-3 leg**: under criterion (i), `((M.fixSet X).obsKernel s_post).map proj_Z = (M.obsKernel (fixSetProj s_post)).map proj_Z`. Applies `do_rule3` with `Y_param := ∅`, `W_param := Z` and bridges `hNoDesc` via `fixSet_isAncestor_fixed_forward`. Consumed by `backdoor_completeness_ae`. | **Proved** |

---

## 9e'. `SCM/ID/Backdoor.lean` — Backdoor Identification (continuous, a.e.)

The sound **continuous-treatment** backdoor results, stated a.e. in the
treatment value (so they never read `obsCondKernel`/`backdoorAdjustment` on a
`{X = x}` null slice).  Built on the posterior witness-kernel Rule 2
(`condDistrib_fixSet_cross_SCM_bridge`).  Headline theorems
`backdoor_completeness_ae` and `backdoor_identifiable_ae`.

| Declaration | Description | Status |
|---|---|---|
| `SCM.treatmentMarginal M X hXr s0` | The observational treatment marginal `νX = (M.obsKernel s0).map π_{X.random}` — the supported measure the a.e. statements are anchored at | Defined |
| `SCM.BackdoorPositivityAE M X Z … s0` | Product positivity / overlap `Prop`: `νX ⊗ μZ ≪ μ_{X.rand ∪ Z}` (the standard continuous-treatment positivity; vacuous-free, covers both atomic and non-atomic regimes) | Defined |
| `SCM.doKernelY M X … Y hY s0` | Post-intervention `Y`-marginal as a kernel in the treatment value `t`: `t ↦ ((M.fixSet X).obsKernel (extend s0 t)).map π_Y`. Type `Kernel (ValuesOn (X.image .random)) (ValuesOn Y)` — independent of `M`'s fixed values | Defined |
| `SCM.adjustmentKernelY M X … Y Z hY hZ s0` | Backdoor-adjustment `Y`-marginal as a kernel in the treatment value: `(M.backdoorAdjustment …).comap (fixSetExtend s0)` | Defined |
| `SCM.backdoor_completeness_ae_compProd M X … s0 hOverlap hPositivity` | `νX ⊗ₘ doKernelY = νX ⊗ₘ adjustmentKernelY` at base `s0`, under backdoor criterion + joint overlap + `BackdoorPositivityAE`. The compProd (joint) primary form — well-posed for continuous treatment (never reads `obsCondKernel` on a null slice) | **Proved** (sorry-free) |
| `SCM.backdoor_completeness_ae M X … s0 hOverlap hPositivity` | **Continuous backdoor completeness (a.e.).** For `νX`-a.e. treatment value `t`, `doKernelY … t = adjustmentKernelY … t`. Derived from the compProd form via `Kernel.ae_eq_of_compProd_eq`. **Headline.** | **Proved** (sorry-free) |
| `SCM.backdoor_identifiable_ae M₁ M₂ h_swig X Y Z … h_obs h_s0` | **Continuous backdoor identifiability (a.e., cross-SCM).** Two SCMs sharing the SWIG graph (`h_swig`) and observational kernel (`h_obs : HEq …`) with aligned base points (`h_s0 : HEq s0₁ s0₂`) produce `doKernelY M₁ s0₁ =ᵐ[treatmentMarginal M₁ s0₁] doKernelY M₂ s0₂`. A plain `=ᵐ` (not HEq) since `doKernelY` is `M`-fixed-value-independent. Proof: `backdoor_completeness_ae` on each side + cross-SCM `adjustmentKernelY` invariance (`backdoorAdjustment_invariant` after destructure + `cases h_swig`/`h_s0`). **Headline.** | **Proved** (sorry-free) |

---

## 9f. `PO/ID/Exact/LATE.lean` — IV/LATE Identification Theorem

Formalizes the Wald identification of LATE in the PO framework (Basic Concepts.tex: def:po-iv-system, def:po-iv-assumptions, def:po-late, prop:po-late, rem:po-late).

**Implementation note (2026-04-23 refactor).** The file now consumes the PO
abstraction layer introduced in `PO/`: counterfactual maps are built
as `POVar` (`zVar`, `dVar`, `yVar`), single-node interventions as
`RegimedVar.ofSingle` / `RegimedVar` (`dUnderZ`, `yUnderD`), joint bundles as
`POCFBundle` (`cfBundle`), and the IV independence premise as `P.IndepCF`.
A subsequent pass (2026-04-23) further collapsed the two `hCE` blocks in
`first_stage_identity` / `reduced_form_identity` via
`POSystem.eventCondExp_of_consistency_IndepCF`, deleting the product-form
`cfTuple` / `measurable_cfTuple` / `indepFun_factualZ_cfTuple` /
`integral_zEvent_of_cfTuple` scaffolding in favour of direct
`POCFBundle.jointValue` usage.
Net reduction: 429 → 388 lines.

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POIVSystem P` | `structure { Z, D, Y, hZbool, hDbool, hYreal, distinct }` | IV subsystem over a PO system | **Defined** |
| `POIVSystem.zVar`, `dVar`, `yVar` | `POVar P Bool` / `POVar P Bool` / `POVar P ℝ` | `POVar` wrappers around `Z`, `D`, `Y` using the `hZbool`/`hDbool`/`hYreal` equivalences; abstract away the hand-rolled measurability chains | **Defined** |
| `POIVSystem.instrumentRegime S z` | `Regime P.V P.X` | Regime `r_z := ({Z}, z)` | **Defined** |
| `POIVSystem.treatmentRegime S d` | `Regime P.V P.X` | Regime `r_d := ({D}, d)` | **Defined** |
| `POIVSystem.DofZ S z`, `YofD S d` | `P.Ω → Bool` / `P.Ω → ℝ` | Counterfactual treatment `D(z)` and outcome `Y(d)` | **Defined** |
| `POIVSystem.factualZ`, `factualD`, `factualY` | `P.Ω → Bool` / `Bool` / `ℝ` | Factual instrument / treatment / outcome | **Defined** |
| `POIVSystem.complierEvent` | `Set P.Ω` | `{ω | D(1)(ω)=1 ∧ D(0)(ω)=0}` | **Defined** |
| `POIVSystem.zEvent S z` | `Set P.Ω` | `{ω | Z(ω) = z}`, defined as `S.zVar.event z` | **Defined** |
| `POIVSystem.measurable_{DofZ,factualZ,factualD,factualY,YofD}` | `Measurable …` | Measurability of the counterfactual/factual variables (now one-line delegations to `POVar.measurable_cf` / `POVar.measurable_factual`) | **Proved** |
| `POIVSystem.measurableSet_complierEvent` / `measurableSet_zEvent` | `MeasurableSet …` | Measurability of the two event sets | **Proved** |
| `POIVSystem.dUnderZ S z` | `RegimedVar P Bool` | `⟨S.dVar, Regime.single S.Z (S.hZbool.symm z)⟩` — regimed form of `D(z)` used to populate `cfBundle` | **Defined** |
| `POIVSystem.yUnderD S d` | `RegimedVar P ℝ` | `⟨S.yVar, Regime.single S.D (S.hDbool.symm d)⟩` — regimed form of `Y(d)` used to populate `cfBundle` | **Defined** |
| `POIVSystem.cfBundle` | `POCFBundle P` | The bundle `(D(1), D(0), Y(1), Y(0))` built via iterated `POCFBundle.cons`; target of the IV independence hypothesis | **Defined** |
| `POIVSystem.YofDofZ S z` | `P.Ω → ℝ` | `Y(D(z)) := 1_{D(z)=1} Y(1) + 1_{D(z)=0} Y(0)` | **Defined** |
| `POIVSystem.condExpDZ S z`, `condExpYZ S z` | `ℝ` | Event-level `E[D | Z=z]`, `E[Y | Z=z]` | **Defined** |
| `POIVSystem.Assumptions S` | `structure { consistency, instrumentIndep, monotonicity, relevance }` where `instrumentIndep : P.IndepCF (RegimedVar.ofFactual S.zVar) S.cfBundle P.μ` | def:po-iv-assumptions; the instrument-independence field is now phrased against the bundle-based `IndepCF` shape | **Defined** |
| `POIVSystem.LATE` | `ℝ` | `(∫_C (Y(1)-Y(0)) ∂μ) / (μ C).toReal` — def:po-late | **Defined** |
| `POIVSystem.DofZ_eq_factualD_on_zEvent` | `ω ∈ zEvent z → DofZ z ω = factualD ω` | Pointwise D-consistency on `{Z = z}` | **Proved** |
| `POIVSystem.factualY_eq_YofD_factualD` | `factualY ω = YofD (factualD ω) ω` | Pointwise Y-consistency everywhere | **Proved** |
| `POIVSystem.first_stage_identity` | `condExpDZ 1 - condExpDZ 0 = (μ C).toReal` | Step 1 of rem:po-late | **Proved** |
| `POIVSystem.reduced_form_identity` | `condExpYZ 1 - condExpYZ 0 = ∫ (YofDofZ 1 - YofDofZ 0) ∂μ` | Step 2 of rem:po-late | **Proved** |
| `POIVSystem.pointwise_monotonicity` | `∀ᵐ ω, Y(D(1))-Y(D(0)) = (Y(1)-Y(0))·1_C` | Step 3 of rem:po-late | **Proved** |
| `POIVSystem.event_conditioning_identity` | `∫ (Y(1)-Y(0))·1_C ∂μ = (μ C).toReal · LATE` | Step 4 of rem:po-late | **Proved** |
| `POIVSystem.late_wald` | `(condExpYZ 1 - condExpYZ 0) / (condExpDZ 1 - condExpDZ 0) = LATE` | Wald identification of LATE, prop:po-late | **Proved** |

Drop-of-conditioning and consistency-on-event rewrites are delegated to
`POSystem.eventCondExp_of_consistency_IndepCF` from `PO/Conditioning/EventCondExp.lean`;
no private helper remains in this file.

---

## 9f'. `PO/ID/Exact/HeckmanRoy/{Setup,Wald}.lean` — Heckman–Vytlacil IV / Generalized Roy Selection Model (PO framework)

Formalises the Heckman–Vytlacil IV / generalized Roy selection model from `Basic Concepts.tex` (def:po-iv-heckman-roy-system, def:po-iv-heckman-roy-assumptions, def:po-iv-heckman-roy-late, prop:po-iv-heckman-roy-wald, rem:po-iv-heckman-roy-lean). Generalises `LATE.lean` to:

* an arbitrary measurable instrument value space `α` (with `MeasurableSingletonClass`), instead of `Bool` — same parametrization pattern as `Manski/Setup.lean`;
* a latent uniform rank `U : Ω → ℝ` (`U ~ Unif[0,1]`) plus a propensity map `p : α → ℝ`, replacing the binary `D` potentials and monotonicity by threshold crossing `D(z) = 1_{U ≤ p(z)}`;
* a **pairwise** Wald identity: for any `z₀, z₁ : α` with `p z₀ < p z₁` and positive measure on `{Z = z₀}, {Z = z₁}`,
  `(E[Y|Z=z₁] − E[Y|Z=z₀]) / (E[D|Z=z₁] − E[D|Z=z₀]) = LATE(z₀, z₁)`.

**Out of scope (follow-ups):** the marginal treatment effect `MTE` (def:po-iv-heckman-roy-mte) and the continuous-Z / regression-representative formulation (rem:po-iv-heckman-roy-local-iv); both need the `IsRegressionFunction` infrastructure of `PO/Analysis/Regression.lean` to extend to non-singleton instruments.

### `HeckmanRoy/Setup.lean` — data layer

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `POHeckmanRoySystem P α` | `structure { Z, D, Y, U, hZ, hDbool, hYreal, hUreal, distinctness pairs, p, hp_mem }` | Heckman–Roy IV subsystem over `P`, parametrised by instrument value space `α` with `MeasurableSingletonClass` | **Defined** |
| `POHeckmanRoySystem.{zVar, dVar, yVar, uVar}` | `POVar P α / Bool / ℝ / ℝ` | `POVar` wrappers around `Z, D, Y, U` | **Defined** |
| `POHeckmanRoySystem.instrumentRegime z` | `Regime P.V P.X` | Single-node regime `{Z ← z}` | **Defined** |
| `POHeckmanRoySystem.treatmentRegime d` | `Regime P.V P.X` | Single-node regime `{D ← d}` | **Defined** |
| `POHeckmanRoySystem.DofZ z` | `P.Ω → Bool` | Counterfactual treatment `D(z)` | **Defined** |
| `POHeckmanRoySystem.YofD d` | `P.Ω → ℝ` | Counterfactual outcome `Y(d)` | **Defined** |
| `POHeckmanRoySystem.factualZ / D / Y / U` | `P.Ω → α / Bool / ℝ / ℝ` | Factual realisations | **Defined** |
| `POHeckmanRoySystem.zEvent z` | `Set P.Ω` | `{Z = z}` as a `POVar.event` | **Defined** |
| `POHeckmanRoySystem.intervalComplierEvent z₀ z₁` | `Set P.Ω` | `{ω | p z₀ < U ω ≤ p z₁}` (def:po-iv-heckman-roy-late) | **Defined** |
| `POHeckmanRoySystem.measurable_*` | `Measurable …` / `MeasurableSet …` | One-line delegations to `POVar.*` for `DofZ, YofD, factualZ, factualD, factualY, factualU, YofDofZ` and the events `zEvent`, `intervalComplierEvent` | **Proved** |
| `POHeckmanRoySystem.YofDofZ z` | `P.Ω → ℝ` | `Y` composed with `D(z)`: `if D(z) ω then Y(1) ω else Y(0) ω` | **Defined** |
| `POHeckmanRoySystem.condExpDZ z`, `condExpYZ z` | `ℝ` | Event-level `E[D | Z=z]`, `E[Y | Z=z]` | **Defined** |
| `POHeckmanRoySystem.yUnderD d` | `RegimedVar P ℝ` | Regimed outcome under `{D ← d}`, used for the bundle | **Defined** |
| `POHeckmanRoySystem.cfBundle` | `POCFBundle P` | The bundle `(U, Y(1), Y(0))`; target of the instrument-independence assumption.  `D(z)` is omitted — it is determined by `U` via threshold crossing | **Defined** |
| `POHeckmanRoySystem.Assumptions S` | `structure { consistency, instrumentIndep, thresholdCrossing, uniformU }` | def:po-iv-heckman-roy-assumptions; `instrumentIndep : P.IndepCF (RegimedVar.ofFactual S.zVar) S.cfBundle P.μ`, `thresholdCrossing : ∀ z, ∀ᵐ ω, (D(z) ω = true ↔ U ω ≤ p z)`, `uniformU : ∀ q ∈ [0,1], μ {U ≤ q} = ENNReal.ofReal q` | **Defined** |
| `POHeckmanRoySystem.LATE z₀ z₁` | `ℝ` | Latent interval ATE: `(∫_C (Y(1)-Y(0)) ∂μ) / (μ C).toReal` (def:po-iv-heckman-roy-late) | **Defined** |

### `HeckmanRoy/Wald.lean` — proof layer

Mirrors the five-step decomposition of rem:po-iv-heckman-roy-lean.  All `theorem`/`lemma` proofs below are filled (Codex-assisted).

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `DofZ_eq_factualD_on_zEvent` | `ω ∈ zEvent z → DofZ z ω = factualD ω` | Step 1: pointwise D-consistency on `{Z = z}`; one-line via `POVar.cf_eq_factual_on_event` | **Proved** |
| `factualY_eq_YofD_factualD` | `factualY ω = YofD (factualD ω) ω` | Step 1: pointwise Y-consistency; one-line via `POVar.factual_eq_cfUnder_self_selected` | **Proved** |
| `interval_indicator_sub` | `1_{U ≤ p z₁} ω - 1_{U ≤ p z₀} ω = (intervalComplierEvent z₀ z₁).indicator 1 ω` (for `p z₀ ≤ p z₁`) | Step 5 (algebra): pointwise interval-subtraction identity | **Proved** |
| `complier_measure` | `(μ (intervalComplierEvent z₀ z₁)).toReal = p z₁ - p z₀` (for `p z₀ < p z₁`) | Step 4: uniform-threshold lemma applied at `p z₀, p z₁` plus measure subtraction | **Proved** |
| `first_stage_identity` | `condExpDZ z₁ - condExpDZ z₀ = p z₁ - p z₀` | Step 1+3 (analogue of LATE `first_stage_identity`); uses `POSystem.eventCondExp_of_consistency_IndepCF` | **Proved** |
| `reduced_form_identity` | `condExpYZ z₁ - condExpYZ z₀ = ∫ (YofDofZ z₁ - YofDofZ z₀) ∂μ` | Step 1+3 (analogue of LATE `reduced_form_identity`); same drop-of-conditioning lemma | **Proved** |
| `pointwise_threshold_identity` | `∀ᵐ ω, YofDofZ z₁ ω - YofDofZ z₀ ω = (Y(1)-Y(0))(ω) · 1_{intervalComplierEvent z₀ z₁}(ω)` | Step 2: replaces LATE `pointwise_monotonicity`; case-split on `U ω ≤ p zⱼ` using `thresholdCrossing` | **Proved** |
| `event_conditioning_identity` | `∫ (Y(1)-Y(0)) · 1_C ∂μ = (μ C).toReal · LATE z₀ z₁` | Direct copy of LATE `event_conditioning_identity` with `intervalComplierEvent` | **Proved** |
| `wald_pairwise` | `(condExpYZ z₁ - condExpYZ z₀) / (condExpDZ z₁ - condExpDZ z₀) = LATE z₀ z₁` | Main theorem (prop:po-iv-heckman-roy-wald); stitches the helpers via `field_simp` | **Proved** |

---

## 9f''. `PO/ID/Exact/DynamicLATE/{Setup,Consistency,Bridges,WhenToTreat}.lean` — Two-Period Dynamic LATE (PO framework)

Formalises the two-period dynamic IV/LATE identification of Sojitra (2025) in the bare potential-outcome framework: `subsec:po-dynamic-late`, `def:po-dynamic-late-system`, `def:po-dynamic-late-assumptions`, `def:po-dynamic-late`, `def:po-dynamic-late-observable-functionals`, `prop:po-dynamic-late-when-to-treat`, `rem:po-dynamic-late-bridge`, `rem:po-dynamic-late-lean`. Generalises `LATE.lean` to two periods with sequential encouragements `Z₁,Z₂`, noncompliant treatments `D₁,D₂`, baseline state `S₀ : POVar P γ₀`, intermediate state `S₁ : POVar P γ₁`, and real outcome `Y`.

**Phase A scope.** Definitions, observable functionals, the assumption bundle, the four bridge identities of `rem:po-dynamic-late-bridge`, and the algebraic ratio identifications `whenToTreat_wald`, `mixtureLATE_wald`, plus the heterogeneous (`S₀`-conditional) versions. The bridge proofs and the structural composition-consistency rewrites are filled.

**Out of scope (Phase B):** `prop:po-dynamic-late-always-treat` and `cor:po-dynamic-late-staggered` (always-treat LATE under cross-period mean-independence / staggered-compliance). Will live in a future `AlwaysTreat.lean`.

### `DynamicLATE/Setup.lean` — data layer

| Declaration | Signature | Description | Status |
|---|---|---|---|
| `PODynLATESystem P γ₀ γ₁` | `structure { S0, S1, Z1, D1, Z2, D2, Y, hZ1bool, hD1bool, hZ2bool, hD2bool, hYreal, vars_inj }` | Two-period dynamic IV subsystem over a PO system (def:po-dynamic-late-system). Pairwise distinctness packaged as `Function.Injective` on a `Fin 7 → P.V` accessor. | **Defined** |
| `PODynLATESystem.{z1Var, z2Var, d1Var, d2Var}` | `POVar P Bool` | `POVar` wrappers around `Z₁,Z₂,D₁,D₂` | **Defined** |
| `PODynLATESystem.yVar` | `POVar P ℝ` | `POVar` wrapper around `Y` | **Defined** |
| `PODynLATESystem.{factualS0, factualS1, factualZ1, factualZ2, factualD1, factualD2, factualY}` | `P.Ω → ·` | Factual realisations of the seven nodes | **Defined** |
| `PODynLATESystem.{Z1_ne_Z2, D1_ne_D2, D1_ne_Y, D2_ne_Y, Z1_ne_Y, Z2_ne_Y, Z1_ne_D1, Z1_ne_D2, Z2_ne_D1, Z2_ne_D2}` | `S.Z1 ≠ S.Z2` etc. | Pairwise distinctness extracted from `vars_inj` (the most-used pairs) | **Proved** |
| `PODynLATESystem.encouragementRegime z` | `Regime P.V P.X` | Two-target regime `{Z₁ ↦ z 0, Z₂ ↦ z 1}` via `Regime.ofList` | **Defined** |
| `PODynLATESystem.treatmentRegime d` | `Regime P.V P.X` | Two-target regime `{D₁ ↦ d 0, D₂ ↦ d 1}` via `Regime.ofList` | **Defined** |
| `PODynLATESystem.encZ2Regime z₂` | `Regime P.V P.X` | Single-target regime `{Z₂ ↦ z₂}`, used in stage-2 ignorability | **Defined** |
| `PODynLATESystem.D1ofZ z`, `D2ofZ z` | `P.Ω → Bool` | Counterfactual stage-1 / stage-2 treatment under encouragement `z` | **Defined** |
| `PODynLATESystem.DofZ z` | `P.Ω → (Fin 2 → Bool)` | Joint counterfactual treatment vector `(D₁(z), D₂(z))` | **Defined** |
| `PODynLATESystem.D2ofZ2 z₂` | `P.Ω → Bool` | `D₂(Z₁, z₂)`: stage-2 treatment when only `Z₂` is fixed | **Defined** |
| `PODynLATESystem.YofD d` | `P.Ω → ℝ` | Counterfactual outcome `Y(d)` under treatment regime fixing both `D`'s | **Defined** |
| `PODynLATESystem.YofDofZ z` | `P.Ω → ℝ` | `Y(D(z))`: outcome under the encouragement regime, i.e. `S.yVar.cf (encouragementRegime z)`. Composition consistency identifies it with the explicit composition `Y(d) ∘ DofZ z` on `{D(z) = d}`. | **Defined** |
| `PODynLATESystem.YofZ2 z₂` | `P.Ω → ℝ` | `Y(D₁, D₂(Z₁, z₂))` realised as `Y` under the regime fixing only `Z₂ = z₂` | **Defined** |
| `PODynLATESystem.measurable_*` | `Measurable …` | Measurability one-line delegations for all CF/factual maps | **Proved** |
| `PODynLATESystem.{yUnderZ z, d1UnderZ z, d2UnderZ z}` | `RegimedVar P …` | Regimed wrappers used to populate `cfBundle1` | **Defined** |
| `PODynLATESystem.{yUnderZ2 z₂, d2UnderZ2 z₂}` | `RegimedVar P …` | Regimed wrappers used to populate `cfBundle2` | **Defined** |
| `PODynLATESystem.historyBundle1` | `POCFBundle P` | Stage-1 history `(S₀,)` — conditioning σ-algebra for the outer regression | **Defined** |
| `PODynLATESystem.historyBundle2` | `POCFBundle P` | Stage-2 history `(S₀, S₁, Z₁, D₁)` — conditioning σ-algebra for the inner regression (stage-2 encouragement `Z₂` is restricted via an indicator, not in the conditioning set) | **Defined** |
| `PODynLATESystem.cfBundle1 z` | `POCFBundle P` | Stage-1 ignorability target `(Y(D(z)), D₁(z), D₂(z))…162152 tokens truncated…inshausen, *Causal inference
using invariant prediction* (JRSS-B 2016, `arXiv:1501.01332`). An **environment family**
`EnvFamily` is a `Fintype`-indexed family of generalized SCMs `{M i}` over common observed/latent
node sets, sharing the target's parent set (E4 `hParents`), its structural mechanism (E2 `hStruct`,
as `HEq`), the latent-noise law (E3 `hLatent`, as `HEq`), and carrying an **exogeneity** field
`hExo` (the target's latent parents are independent of its observed parents under each environment's
joint law — the SEM assumption `εᵉ ⊥ Xᵉ_{S*}` that rules out hidden confounding into `Y`).
A predictor set `S` is **invariant** when the conditional law of the target given `X_S` is one fixed
kernel across all environments (an a.e. statement w.r.t. each environment's predictor marginal).

| Declaration | Statement | Description |
| --- | --- | --- |
| `EnvFamily` / `paObs` / `paLat` / `Invariant` (`Model.lean`, `Invariance.lean`, `MechanismFactor.lean`) | environment-family structure with shared parents/mechanism/latent law + exogeneity `hExo`; observed/latent parents of the target; the invariance predicate (one shared conditional kernel a.e. per environment) | Model + grammar layer. **Defs** |
| `mechanism_invariant` (`Invariance.lean`) | the target's observed parents `paObs` form an invariant set: in every environment the conditional law of the target given its observed parents equals one fixed structural factor | **Headline (the engine of soundness), proved.** Witness = law of `structFun Y` driven by the latent-parent noise (reference environment); per-environment disintegration via exogeneity (`hExo`), cross-environment agreement via shared E2/E3/E4. `#print axioms` = `[propext, sorryAx, Classical.choice, Quot.sound]`, where `sorryAx` is **only** the isolated `s_eq_on_fixed_parents` regularity gap below. **Proved (modulo one regularity gap)** |
| `icp_sound` / `idSet` / `invariantSets` (`Soundness.lean`, `IdentifiedSet.lean`) | **Theorem 1 (soundness):** the identified set `S(E) = ⋂` (invariant sets) is contained in the target's observed parents — ICP never selects a non-cause | Immediate from `mechanism_invariant`. Same axiom profile (reduces to `s_eq_on_fixed_parents`). **Proved (modulo the same gap)** |
| `mechanismFun` / `condDistrib_target_eq_mechanismKernel` / `mechanismKernel_env_eq` / `jointKernel_map_paLat_eq_latentProduct_map` / `structFun_yNode_apply_eq` / `latentProduct_heq` / `map_heq_transport` (`MechanismFactor.lean`) | the structural mechanism as a measurable map of observed+latent parents; per-environment factorization of the target conditional through the mechanism kernel; cross-environment equality of that kernel; latent-parent marginal = latent-product marginal; cross-environment `structFun Y` agreement; HEq transport of latent product measures / push-forwards | Supporting machinery for `mechanism_invariant` (Steps A/B/C). **Proved (sorry-free)** |
| `s_eq_on_fixed_parents` (`MechanismFactor.lean`) | environments assign the same value to any **fixed** (intervened) parent of the target | **The one residual `sorry`.** Holds vacuously when the target has no fixed parents; not derivable from the bare `EnvFamily` fields (the `EnvFamily` shares the parent set and forbids changing it, but does not pin the intervention *value* on a fixed parent), so it is isolated here as the structural regularity gap (ICP's "no intervention on a direct cause of `Y` with a shifting value"). **`sorry` (isolated gap)** |
| `parent_omitted_not_invariant` / `icp_complete` / `RichEnv` (`Completeness.lean`) | **Theorem 2 (completeness):** under richness/faithfulness primitives `S(E)` equals the parents | Completeness direction; the hard propagation lemma `parent_omitted_not_invariant` is a pre-existing escalated `sorry` (unchanged). **Partial (`sorry`)** |

### `LinearGaussian/` — completeness in the linear-Gaussian model (`prop:1`(i), sorry-free)

A self-contained linear-Gaussian sub-development (random-variable encoding, NOT built on the
nonparametric SWIG/kernel layer above) that proves the **converse** `S(E) ⊇ PA(Y)` — the only setting
in which the paper establishes it — via the do-intervention **mean-shift** argument. The observational
SEM `ObsSEM` carries the coefficient matrix `β`, an acyclic `DAG` (`edge k j ↔ βⱼₖ ≠ 0`), Gaussian
noises `εⱼ ~ N(0,σⱼ²)`, and the paper's **Assumption-1 exogeneity** `hYexo` (`ε₀ ⊥ Xₖ` for each parent
`k ∈ PA(Y)`); `Env` is a single do-intervention environment on the same probability space (with its own
`hExo`); `EnvFamily` bundles the observational SEM with finitely many environments. The regression layer
(`Regression.lean`) defines the residual `R = Y − Σ γₖ Xₖ`, the regression-invariance null `H_{0,S}`
(`InvarianceNull`: a shared coefficient `γ` and residual law `Fε`, residual ⊥ predictors and same law
across environments), and the identified set `S(E) = ⋂{S : H_{0,S}}`.

| Declaration | Statement | Description |
| --- | --- | --- |
| `ObsSEM` / `Env` / `EnvFamily` / `InvarianceNull` / `identifiedSet` (`Model.lean`, `Regression.lean`) | observational linear-Gaussian SEM with exogeneity field `hYexo`, do-intervention environment with `hExo`, environment family; the regression residual, invariance null `H_{0,S}`, and identified set `S(E)` | Model + observable layer. **Defs** |
| `eps_integrable` / `eps_integral_zero` (`Helpers/Moments.lean`) | each noise `εⱼ` is integrable with `E[εⱼ] = 0` (Gaussian first moment) | Moment helpers. **Proved (sorry-free)** |
| `obsResidual_eq_eps` / `envResidual_eq_eps` (`Helpers/Residual.lean`) | with the causal coefficient `γ* = β₀,·`, the residual equals the target noise `ε₀` a.e. in both the observational and every interventional environment | Algebraic helpers (target never intervened, `β₀₀ = 0`). **Proved (sorry-free)** |
| `nonDescendant_invariance` (`Helpers/Invariance.lean`) | under the single do-intervention `do(X_{k₀}=a)`, every coordinate that is neither `k₀` nor a descendant of `k₀` keeps its observational value a.e. | Structural backbone of the mean-shift (strong induction on topological order). **Proved (sorry-free)** |
| `icp_sound_linearGaussian` (`Completeness.lean`) | **Soundness:** `S(E) ⊆ PA(Y)` — `PA(Y)` satisfies the invariance null with `γ* = β₀,·` and residual law `N(0,σ₀²)` (residual `=ᵐ ε₀`, exogeneity gives independence, `hGauss` gives the shared law) | Reuses the exogeneity fields `hYexo`/`hExo`. **Proved (sorry-free)** |
| `exists_youngest_nonzero` (`Completeness.lean`) | among a nonempty index set there is a youngest one (largest topological order), no directed path to any other element | Youngest-node selection. **Proved (sorry-free)** |
| `residual_mean_shift_of_doIntervention` (`Completeness.lean`) | under `do(X_{k₀}=a)` with `a ≠ E[X¹_{k₀}]`, `α_{k₀} ≠ 0`, and the youngest-node property `hyoung`, the interventional and observational residuals have different means (gap `α_{k₀}·(a − E[X¹_{k₀}])`), so they are not `IdentDistrib` | The eq:help1/help2 mean-shift; `hyoung` kills all non-`k₀` terms. **Proved (sorry-free)** |
| `icp_complete_linearGaussian` (`Completeness.lean`) | **Theorem `prop:1`(i) (completeness):** with shifted single do-interventions on every predictor, `S(E) = PA(Y)` | Combines soundness with the mean-shift: a missing parent forces a youngest support index whose intervention breaks the shared residual law. `#print axioms` = `[propext, Classical.choice, Quot.sound]`. **Proved (sorry-free)** |

## 18. `Experimentation/` — design-based (randomization) inference under interference

The experimentation cluster: a shared, paper-agnostic **design-based substrate**
(`Experimentation/DesignBased/`, namespace `Causalean.Experimentation.DesignBased`) plus one
folder per formalized paper that consumes it (`Experimentation/ExposureMappingInterference/` and
`Experimentation/TwoStageInterference/`, namespaces `Causalean.Experimentation.{ExposureMappingInterference,TwoStageInterference}`).
The substrate is the finite-population,
fixed-potential-outcome flavor of the potential-outcomes framework — probability comes from the
experimenter's randomization over a *finite* assignment space `Ω` (a sibling of the
measure-theoretic superpopulation `PO/`, which it never imports), with a deliberately lightweight
finite-sum layer (`E X = ∑ z, p z · X z`) so all algebraic identities are `Finset` algebra.
Further experimentation papers (two-stage experiments, …) slot in as sibling folders under
`Experimentation/`, reusing `DesignBased`. First paper: Aronow & Samii (2017, AOAS), "Estimating
Average Causal Effects Under General Interference" (arXiv:1305.6156; plan `doc/aronow_samii_plan.md`).
Second paper: Hudgens & Halloran (2008, JASA), "Toward Causal Inference With Interference" — the
two-stage / partial-interference estimand zoo (direct/indirect/total/overall effects), which forced
the reusable `Product`/`TwoStage` substrate combinators (plan `doc/hudgens_halloran_plan.md`).

**Main results** (the paper's named theorems; flagged as headlines in
`doc/library_review/Experimentation.json` — everything else is supporting substrate):
`Experimentation.DesignBased.E_htEffect` (Lemma 4.1, HT effect unbiasedness — substrate),
`Experimentation.DesignBased.Var_htTotal` (Prop 4.4, HT variance — substrate),
`Experimentation.ExposureMappingInterference.htMean_consistent_of_var` (Prop 6.4, consistency),
`…ExposureMappingInterference.wald_coverage_of_conditions` (Prop 6.5, oracle-variance Wald coverage from
primitive conditions), `…ExposureMappingInterference.wald_coverage_feasible_of_conditions` (Prop 6.5/6.6, the
feasible estimated-V̂ interval — the flagship), and
`…ExposureMappingInterference.var_NsqVhat_tendsto_zero_of_conditions` (Prop 6.6, variance-estimator consistency).
Hudgens–Halloran main results: `…TwoStageInterference.E_estDirect` / `E_estIndirect` / `E_estTotal`
(Theorems 1–3, unbiasedness of the direct/indirect/total effect estimators), `…TwoStageInterference.CE_total_decomp`
(total = direct + indirect), `…TwoStageInterference.Var_tauHat` (Theorem 5, the within-group Neyman variance), and
`…TwoStageInterference.Var_popEst` (Theorem 4, the two-stage variance decomposition), and
`…TwoStageInterference.Var_estDirect` (Theorem 6, the direct-effect-estimator variance).
The substrate (`DesignBased/`: finite-sum `E`/`Var`/`Cov`, exposure, HT, Chebyshev, product/compound
designs, the abstract `var_edge_sum_le`, normal-CDF facts, the measure bridge) is reusable
architecture, not main results.

### `Experimentation/DesignBased/Design.lean` — finite randomization design + `E`/`Var`/`Cov` algebra

| Declaration | Statement | Description |
|---|---|---|
| `FiniteDesign` | structure: `p : Ω → ℝ`, `p_nonneg`, `p_sum : ∑ p = 1` | A randomization design = a probability mass function on a finite assignment space `Ω`. |
| `FiniteDesign.E` / `Var` / `Cov` | `E X = ∑ z, p z · X z`; `Var X = E[(X−E X)²]`; `Cov X Y = E[(X−E X)(Y−E Y)]` | Finite-sum expectation, variance, covariance of real random variables under the design. |
| `ind` / `Pr` | `ind A = fun z => if A z then 1 else 0`; `Pr A = E (ind A)` | Indicator of an event and its design probability. |
| `E_const`/`E_add`/`E_sub`/`E_const_mul`/`E_mul_const`/`E_neg`/`E_sum`/`E_congr` | linearity of `E` | Expectation is linear and respects finite sums and pointwise equality. |
| `Var_eq` / `Cov_eq` | `Var X = E[X²] − (E X)²`; `Cov X Y = E[X·Y] − E X · E Y` | The computational forms of variance and covariance. |
| `Cov_self` / `Cov_comm` / `Var_congr` / `Cov_congr` | `Cov X X = Var X`; symmetry; congruence | Basic covariance/variance identities. |
| `Cov_const_mul_left/right` / `Cov_sub_left/right` / `Cov_sum_left/right` | bilinearity of `Cov` | Covariance is bilinear over scalar multiples, differences, and finite sums. |
| `Cov_linear_comb` / `Var_linear_comb` | `Cov (∑ cᵢXᵢ) (∑ eⱼYⱼ) = ∑∑ cᵢeⱼ Cov(Xᵢ,Yⱼ)`; variance specialization | Covariance/variance of finite linear combinations as double sums — the workhorse for HT variance. |
| `Var_sub` / `Var_const_mul` | `Var(X−Y)=Var X+Var Y−2Cov(X,Y)`; `Var(c·X)=c²·Var X` | Variance of a difference and under scaling. |
| `E_ind` / `ind_sq` / `Var_ind` | `E(ind A)=Pr A`; `(ind A)²=ind A`; `Var(ind A)=Pr A·(1−Pr A)` | Indicator expectation/idempotence/variance. |
| `E_nonneg` / `E_le_one` / `ind_nonneg` / `ind_le_one` / `Pr_nonneg` / `Pr_le_one` | `[0,1]` bounds | Elementary bounds: expectations of `[0,1]`-valued variables and probabilities lie in `[0,1]`. |

### `Experimentation/DesignBased/Exposure.lean` — exposure mappings and generalized probability of exposure

| Declaration | Statement | Description |
|---|---|---|
| `expo` / `expoInd` | `expo f θ i z = f z (θ i)`; `expoInd f θ i d = ind (expo i = d)` | The exposure unit `i` receives under assignment `z`, and its `{0,1}` indicator. |
| `prop` / `propPairSame` / `propPairCross` | `π_i(d)=Pr(expo i=d)`; `π_{ij}(d)=E[1ᵢ1ⱼ]`; `π_{ij}(d,d')=E[1ᵢ(d)1ⱼ(d')]` | Generalized probability of exposure and joint exposure probabilities. |
| `E_expoInd` / `sum_prop_eq_one` | `E(expoInd i d)=π_i(d)`; `∑_d π_i(d)=1` | Propensity as an expectation; propensities sum to one over exposures. |
| `Cov_expoInd_same` / `Cov_expoInd_cross` | `Cov(1ᵢ(d),1ⱼ(d))=π_{ij}(d)−π_iπ_j` (and cross) | Covariance of exposure indicators in terms of joint/marginal propensities. |
| `expoInd_mul_self_of_ne` / `propPairCross_self_of_ne` | for `d≠d'`: `1ᵢ(d)·1ᵢ(d')=0`; `π_{ii}(d,d')=0` | A unit cannot occupy two distinct exposures at once. |

### `Experimentation/DesignBased/PotentialOutcome.lean` — properly-specified mapping (Cond 1) and consistency (Cond 2)

| Declaration | Statement | Description |
|---|---|---|
| `ProperlySpecified` | `∀ i z, yr i z = y i (expo i z)` | Condition 1: interference acts only through the exposure (potential outcome factors through it). |
| `Yobs` | `Yobs y f θ i z = y i (expo i z)` | Observed outcome of unit `i` under assignment `z`. |
| `Yobs_eq_sum` | `Yobs i z = ∑_d 1ᵢ(d)·y i d` | Condition 2 (consistency), as a derived lemma. |
| `expoInd_mul_Yobs` / `expoInd_mul_Yobs_sq` / `expoInd₂_mul_Yobs` | on-event substitutions `1·Yobs = 1·y` (and squared / two-indicator forms) | The exposure indicator forces the observed outcome to its potential-outcome value. |

### `Experimentation/DesignBased/HT/{Estimator,Unbiased,Variance}.lean` — Horvitz–Thompson estimators

| Declaration | Statement | Description |
|---|---|---|
| `htTotal` / `htMean` / `htEffect` | `ŷᵀ(d)=∑ᵢ 1ᵢ(d)Yᵢ/π_i(d)`; `μ̂=ŷᵀ/N`; `τ̂=μ̂(dk)−μ̂(dl)` | Inverse-probability-weighted total, mean, and effect estimators. |
| `muTrue` / `tauTrue` / `htTotal_eq` | `μ(d)=(1/N)∑ y i d`; `τ=μ(dk)−μ(dl)`; HT total in `y i d` form | Estimands and the indicator-forced rewrite of the estimator. |
| `E_htTotal` / `E_htMean` / `E_htEffect` | unbiasedness (Lemma 4.1, Prop 4.4) | The HT total/mean/effect estimators are unbiased under positive propensities. **Proved.** |
| `Var_htTotal_cov` / `Var_htTotal` | variance as double-sum-of-covariances and expanded form `eq:total_variance` | Randomization variance of `ŷᵀ(d)`: `∑ π_i(1−π_i)(y/π)² + ∑_{i≠j}(π_{ij}−π_iπ_j)(y/π)(y/π)`. **Proved.** |
| `Cov_htTotal_cov` / `Cov_htTotal` | covariance forms `eq:totals_covariance` | `Cov[ŷᵀ(dk),ŷᵀ(dl)]`; the diagonal yields the famously unidentified `−∑ᵢ yᵢ(dk)yᵢ(dl)` term (needs `dk≠dl`). **Proved.** |

### `Experimentation/ExposureMappingInterference/Variance/Conservative.lean` — conservative variance estimators (§5, positive-joint + zero-pairwise)

| Declaration | Statement | Description |
|---|---|---|
| `htVarEst` / `htCovEst` / `htEffectVarEst` | the HT variance/covariance/effect-variance estimators | Design-based estimators of `Var[ŷᵀ]`, `Cov[ŷᵀ,ŷᵀ]`, `Var[τ̂]` (positive-joint regime). |
| `E_htVarEst` | `E[V̂[ŷᵀ(d)]] = Var[ŷᵀ(d)]` (Lemma 5.1) | The variance estimator is exactly unbiased in the positive-joint regime. **Proved.** |
| `E_htCovEst_le` | `E[Ĉov] ≤ Cov` (Prop 5.4) | The covariance estimator is nonpositively biased (Young's inequality on the diagonal). **Proved.** |
| `E_htEffectVarEst_ge` | `Var[τ̂] ≤ E[V̂[τ̂]]` (Prop 5.7) | The assembled effect-variance estimator is conservative (nonnegative bias). **Proved.** |
| `E_htVarEst_eq_addBias` | `E[V̂[ŷᵀ(d)]] = Var[ŷᵀ(d)] + A` (Prop 5.2) | Bias of the variance estimator when some joint probabilities vanish, `A = ∑_{π_{ij}(d)=0} y_i(d)y_j(d)`. **Proved.** |
| `htA2` / `E_htVarEst_add_htA2_ge` | `Var[ŷᵀ(d)] ≤ E[V̂ + Â₂]` (Prop 5.3) | Young correction `Â₂` over zero-joint pairs makes the variance estimator conservative without the positive-joint assumption. **Proved.** |
| `E_htCovEst_eq_of_noEffect` | `E[Ĉov] = Cov` under `y_i(dk)=y_i(dl)` (Prop 5.5) | The covariance estimator is exactly unbiased when there is no effect (the Young diagonal correction is exact). **Proved.** |
| `htCovEstA` / `E_htCovEstA_le` | `E[Ĉov_A] ≤ Cov` (Prop 5.6) | General covariance estimator handling zero cross-joints; Young correction over all `j` with `π_{ij}(dk,dl)=0` (incl. the diagonal `j=i`, subsuming the unidentified `−∑ᵢ y_i(dk)y_i(dl)` term). Nonpositively biased with no positive-cross-joint assumption. **Proved.** |
| `htEffectVarEstA` / `E_htEffectVarEstA_ge` | `Var[τ̂] ≤ E[V̂_A[τ̂]]` (general Prop 5.7) | General conservative effect-variance estimator assembling `Â₂` and `Ĉov_A`; nonnegative bias with no joint-positivity hypotheses. **Proved.** |

### `Experimentation/DesignBased/{Chebyshev,GaussianCDF,EdgeVarianceBound,FiniteDesignMeasure}.lean` (substrate) + `Experimentation/ExposureMappingInterference/Asymptotics/{Consistency,SteinCLT,SteinInstance,Intervals,VarianceConsistency,VarEstQuadBound,VarEstConsistencyConditions}.lean` (paper) — large-sample theory

| Declaration | Statement | Description |
|---|---|---|
| `FiniteDesign.chebyshev` | `Pr[|X−E X|≥ε] ≤ Var X/ε²` | Finite Chebyshev inequality (the convergence-in-probability engine). **Proved.** |
| `Experiment` / `gdep` / `N` | sequence-of-experiments bundle; pairwise dependency indicator; population size | Substrate for asymptotics over a sequence of nested finite-population experiments. |
| `Var_htMean_le` | `Var[μ̂(d)] ≤ c²(N+∑g)/N²` | Variance bound under bounded weights and pairwise dependence. **Proved.** |
| `htMean_consistent_of_var` | `Var→0 ⇒ Pr[|μ̂−μ|≥ε]→0` (Prop 6.4) | Consistency of the HT estimator via Chebyshev + unbiasedness. **Proved.** |
| `stdNormalCdf` / `stdNormalCdf_neg` / `monotone_stdNormalCdf` | `Φ(t)=(𝒩(0,1)).real(Iic t)`; `Φ(−t)=1−Φ(t)`; monotone | Standard-normal CDF (`GaussianCDF.lean`), agrees with Mathlib `cdf`; symmetry from `gaussianReal_map_neg` + atomlessness. **Proved.** |
| `Experiment.studentizedEffect` | `(τ̂−τ)/√Var[τ̂]` | The studentized HT effect statistic. |
| `LocalDependenceCLT` | interface premise: studentized statistic `→d 𝒩(0,1)` (Chen–Shao 2004 Thm 2.7, bounded-neighborhood case) | **DISCHARGED** by `localDependenceCLT_of_stein` (`SteinInstance.lean`) via the from-scratch Stein CLT below — no longer an open gate. |
| `wald_coverage` | `1−α ≤ liminf` of Wald-interval coverage (Prop 6.5, "at least `1−α`") | **Proved** from `LocalDependenceCLT` + nonzero variance + CDF symmetry. |
| `GaussianCDF`/`FiniteDesignMeasure`/`SteinInstance` | `stdNormalCdf`+symmetry; `D.toMeasure := ∑ p(z)·δ_z` bridge (`∫=E`,`.real=Pr`,`variance=Var`); `localDependenceCLT_of_stein`, `wald_coverage_of_stein` | Bridge from the lightweight design layer to the measure-theoretic Stein CLT + the discharge. `wald_coverage_of_stein` is **end-to-end** A–S asymptotic coverage from primitive conditions (no CLT premise). **All axiom-clean.** |
| `continuous_stdNormalCdf` | `Φ` is continuous (Gaussian atomless) | Used by the *feasible* interval (`GaussianCDF.lean`). **Proved.** |
| `wald_coverage_feasible` | `1−α ≤ liminf` coverage of `τ̂ ± z·√V̂` (Prop 6.5, the paper's **estimated**-variance interval) | The faithful interval, from CLT + a single variance-estimator-consistency input `hVhat` (`Intervals.lean`). **Proved.** |
| `htEffectVarEst_undershoot_tendsto_zero` / `relVar_of_NsqVar_tendsto` / `wald_coverage_feasible_of_relVar` | reduce `hVhat` to `Var[V̂]/Var²→0`; bridge `Var[N·V̂]→0`+Cond4 ⇒ that; capstone | Chebyshev reduction + conservativeness `E[V̂]≥Var` isolate the variance-consistency input to one limit (`VarianceConsistency.lean`). **Proved, axiom-clean.** |
| `FiniteDesign.var_edge_sum_le` | `Var[∑ᵢⱼ bᵢⱼ] ≤ 8M²m³N` for bounded edge-functions vanishing off a degree-≤`m` graph with unlinked-edge `Cov=0` | Abstract pure-FiniteDesign formalization of the appendix `O(N⁻¹)` quadruple-sum count (`EdgeVarianceBound.lean`). Reusable. **Proved, axiom-clean.** |
| `var_htEdgeStat_le` | `Var[ŷVar(dk)+ŷVar(dl)−2Ĉov] ≤ 8·vbBound²·m³·N` | Per-population bound: `V̂_raw` written as an edge-sum, then `var_edge_sum_le` under Conditions 1, 1′ (joint overlap `1/π_{ij}≤c₃`), 3 (`VarEstQuadBound.lean`). **Proved, axiom-clean.** |
| `var_NsqVhat_tendsto_zero_of_conditions` / `wald_coverage_feasible_of_conditions` | `N²·Var[V̂]→0` from uniform Conditions 1/1′/3 + `N→∞`; end-to-end feasible coverage `≥1−α` from the primitive conditions | Discharges the variance-consistency input to primitives (`VarEstConsistencyConditions.lean`). The only assumption beyond the literal Conditions 1/3/4 is the explicit joint-overlap bound `1/π_{ij}≤c₃` that the paper's appendix uses **implicitly**. **Proved, axiom-clean.** |

**Faithfulness note (Prop 6.6).** The paper's appendix derivation of `Var[N·V̂]→0` treats each
variance-estimator summand `aᵢⱼ ∝ 1/π_{ij}` as `O(1)`, but Condition 1 bounds only `1/π_i`, never
the joint `1/π_{ij}`; the bound therefore needs a joint-overlap lower bound on dependent pairs that
the literal Conditions 1/3/4 omit. We make this explicit as **Condition 1′** (`1/π_{ij}(d) ≤ c₃`)
and recover the paper's claim under it. See `doc/aronow_samii_varest_consistency_plan.md`.

The Chen–Shao dependency-graph CLT is built from scratch in
`Causalean/Mathlib/Probability/SteinMethod/{Solution,Bounds,DependencyCLT,CLT}.lean` (Mathlib has no
Stein's method or Wasserstein metric): the Stein equation `steinSol_hasDerivAt`, the three
Chen–Goldstein–Shao solution bounds `‖f_h‖,‖f_h'‖,‖f_h''‖≤2L` (incl. a from-scratch Mills-ratio
bound), the local-dependence Stein bound `stein_local_dependence_bound`, and the abstract CLT
`stein_cdf_clt` (via the `clt` package's Lévy continuity + portmanteau). Reusable / promotable.

### `Experimentation/DesignBased/{Product,TwoStage}.lean` — product & compound (two-stage) designs (substrate)

The reusable two-stage substrate that Hudgens–Halloran (paper #2) forced. Paper-agnostic.

| Declaration | Statement | Description |
|---|---|---|
| `prodDesign` | `(prodDesign D).p w = ∏ i, (D i).p (w i)` | Product of a finite family of designs `D i : FiniteDesign (α i)` on the dependent product `∀ i, α i`. Makes cross-coordinate (cross-group) independence a structural fact, not an assumption. |
| `FiniteDesign.E_prod_prod` / `E_prod_apply` | `E(∏ᵢ gᵢ(wᵢ))=∏ᵢ E gᵢ`; `E(g(wⱼ))=(D j).E g` | Expectation of a product of single-coordinate functions factors; a function of one coordinate has that coordinate's marginal expectation. **Proved.** |
| `compound` | `(compound D₁ D₂).p (s,w) = D₁.p s · ∏ᵢ (D₂ s i).p (wᵢ)` | Compound (two-stage) design: stage-1 design `D₁` on `Ω₁`, then conditionally on `s`, independent within-coordinate designs `D₂ s i` (which may depend on `s`). |
| `FiniteDesign.E_compound` / `E_compound_factor` | `E[h(s)·g(wⱼ)] = E_s[h(s)·(D₂ s j).E g]` | The stage-2 collapse engine: a stage-1 quantity times a single-group within-function reduces the inner randomization to that group's conditional marginal. **Proved.** |
| `FiniteDesign.E_compound_tower` | `(compound D₁ D₂).E F = E_s[(prodDesign (D₂ s)).E (w ↦ F(s,w))]` | Tower property: the joint expectation is the stage-1 expectation of the stage-2 conditional expectation (`CompoundVariance.lean`). **Proved.** |
| `FiniteDesign.Var_compound_eq_tower` | `Var X = E_s[Var_{w∣s} X] + Var_s(E_{w∣s} X)` | **Law of total variance** for the two-stage design: total variance = expected within-stage variance + variance of the stage-2 conditional mean. The gateway to the between-group / within-group variance decomposition (HH Thm 4/6). **Proved, axiom-clean.** |
| `FiniteDesign.E_prod_apply₂` / `Cov_prod_apply_of_ne` / `Var_prod_apply` (`ProductVariance.lean`) | `E[g(wᵢ)h(wⱼ)]=Eg·Eh` (`i≠j`); `Cov=0` (`i≠j`); `Var(g(wⱼ))=(D j).Var g` | Cross-coordinate independence of the product design: functions of distinct coordinates are uncorrelated. **Proved.** |
| `FiniteDesign.Var_prod_linear_comb` | `(prodDesign D).Var (∑ᵢ cᵢ gᵢ(wᵢ)) = ∑ᵢ cᵢ²·(D i).Var gᵢ` | Variance of a linear combination of single-coordinate functions = sum of coordinate variances (the within-group variance term). **Proved, axiom-clean.** |

### `Experimentation/DesignBased/HeydeBrown.lean` — finite-product Heyde--Brown bridge

This paper-independent adapter puts finite product randomization designs on the product probability
space and reveal filtration required by an externally supplied fourth-moment martingale bound. It
does not assert the analytic Heyde--Brown inequality: callers provide that theorem as a premise,
while the bridge discharges its finite-design interface obligations exactly.

<!-- GEN:Causalean.Experimentation.DesignBased.HeydeBrown -->
| Decl | Signature | Description |
|---|---|---|
| `Experimentation.DesignBased.prefixRank` | `Equiv.Perm (Fin N) → Fin N → Fin N` | A reveal permutation and coordinate determine that coordinate's reveal rank, namely the step at which the permutation reveals it. |
| `Experimentation.DesignBased.AgreeOnPrefix` | `Equiv.Perm (Fin N) → Fin (N + 1) → ((i : Fin N) → alpha i) → ((i : Fin N) → alpha i) → Prop` | A reveal permutation, prefix length, and two assignments determine agreement through the reveal prefix: the assignments have the same values on every coordinate already revealed by this equality condition. |
| `Experimentation.DesignBased.revealMeasurableSpace` | `Equiv.Perm (Fin N) → Fin (N + 1) → MeasurableSpace ((i : Fin N) → alpha i)` | A reveal permutation and prefix length determine the σ-algebra generated by the revealed coordinates, which records exactly the information available after that many reveal steps by generating from those coordinate evaluations. |
| `Experimentation.DesignBased.revealFiltration` | `Equiv.Perm (Fin N) → MeasureTheory.Filtration (Fin (N + 1)) inferInstance` | A reveal permutation determines the reveal filtration, whose time-k σ-algebra is the prefix σ-algebra, is monotone in reveal time, and lies inside the full product σ-algebra. |
| `Experimentation.DesignBased.prefixCondExp` | `((i : Fin N) → Causalean.Experimentation.DesignBased.FiniteDesign (alpha i)) → Equiv.Perm (Fin N) → Fin (N + 1) → (((i : Fin N) → alpha i) → ℝ) → ((i : Fin N) → alpha i) → ℝ` | A family of coordinate designs, reveal permutation, prefix length, and statistic determine the explicit prefix conditional expectation, obtained by averaging over unrevealed coordinates while holding revealed coordinates fixed by the stated finite sum. |
| `Experimentation.DesignBased.IsPrefixMartingaleDifference` | `((i : Fin N) → Causalean.Experimentation.DesignBased.FiniteDesign (alpha i)) → Equiv.Perm (Fin N) → (Fin N → ((i : Fin N) → alpha i) → ℝ) → Prop` | A family of coordinate designs, reveal permutation, and increment family satisfy the prefix martingale-difference condition when each increment has zero conditional mean immediately before its reveal and is visible after that reveal. |
| `Experimentation.DesignBased.finitePredictableVariation` | `((i : Fin N) → Causalean.Experimentation.DesignBased.FiniteDesign (alpha i)) → Equiv.Perm (Fin N) → (Fin N → ((i : Fin N) → alpha i) → ℝ) → ((i : Fin N) → alpha i) → ℝ` | A family of coordinate designs, reveal permutation, and increment family determine the finite-design predictable variation, the sum of conditional second moments just before each reveal step by the displayed finite sum. |
| `Experimentation.DesignBased.measurePredictableVariation` | `MeasureTheory.Measure Omega → MeasureTheory.Filtration (Fin (N + 1)) m → (Fin N → Omega → ℝ) → Omega → ℝ` | A probability measure, filtration, and increment family determine the measure-theoretic predictable variation, the sum of conditional second moments at the preceding filtration times by the displayed finite sum. |
| `Experimentation.DesignBased.finiteFourthMomentError` | `((i : Fin N) → Causalean.Experimentation.DesignBased.FiniteDesign (alpha i)) → Equiv.Perm (Fin N) → (Fin N → ((i : Fin N) → alpha i) → ℝ) → ℝ` | A family of coordinate designs, reveal permutation, and increment family determine the finite fourth-moment error: the sum of fourth moments plus the second moment of predictable variation minus one by the displayed sum of two terms. |
| `Experimentation.DesignBased.measureFourthMomentError` | `MeasureTheory.Measure Omega → MeasureTheory.Filtration (Fin (N + 1)) m → (Fin N → Omega → ℝ) → ℝ` | A probability measure, filtration, and increment family determine the measure-theoretic fourth-moment error: the sum of fourth moments plus the second moment of predictable variation minus one by the displayed sum of two terms. |
| `Experimentation.DesignBased.finiteKolmogorovExpr` | `(Omega → ℝ) → ℝ` | A finite randomization design and real statistic determine its finite-design Kolmogorov expression, the largest absolute gap between its CDF and the standard-normal CDF by taking the supremum over thresholds. |
| `Experimentation.DesignBased.measureKolmogorovExpr` | `MeasureTheory.Measure Omega → (Omega → ℝ) → ℝ` | A measure and real random variable determine its measure-theoretic Kolmogorov expression, the largest absolute gap between its CDF and the standard-normal CDF by taking the supremum over thresholds. |
| `Experimentation.DesignBased.HeydeBrownFourthMomentPremise` | `MeasureTheory.Measure Omega → MeasureTheory.Filtration (Fin (N + 1)) m → (Fin N → Omega → ℝ) → ℝ → Prop` | A probability measure, filtration, increment family, and constant define the supplied Heyde--Brown fourth-moment premise: adapted, centered, normalized increments with finite fourth moments obey the stated one-fifth-power Kolmogorov bound by the four displayed assumptions and conclusion. |
| `Experimentation.DesignBased.prefixCondExp_ae_eq_condExp` | `Causalean.Experimentation.DesignBased.prefixCondExp D pi k f =ᵐ[(Causalean.Experimentation.DesignBased.prodDesign D).toMeasure] (Causalean.Experimentation.DesignBased.prodDesign D).toMeasure[f \| ↑(Causalean.Experimentation.DesignBased.revealFiltration pi) k]` | A family of coordinate designs, reveal permutation, prefix length, and statistic give an almost-everywhere identification of the explicit prefix average with conditional expectation under the product-design measure and its reveal σ-algebra. |
| `Experimentation.DesignBased.aestronglyMeasurable_reveal_of_prefixCondExp_eq` | `Causalean.Experimentation.DesignBased.prefixCondExp D pi k f = f → MeasureTheory.AEStronglyMeasurable f (Causalean.Experimentation.DesignBased.prodDesign D).toMeasure` | A family of coordinate designs, reveal permutation, prefix length, statistic, and pointwise equality to its prefix conditional expectation imply that the statistic is almost-everywhere strongly measurable for the reveal σ-algebra. |
| `Experimentation.DesignBased.condExp_ae_eq_zero_of_prefixCondExp_eq_zero` | `Causalean.Experimentation.DesignBased.prefixCondExp D pi k f = 0 → (Causalean.Experimentation.DesignBased.prodDesign D).toMeasure[f \| ↑(Causalean.Experimentation.DesignBased.revealFiltration pi) k] =ᵐ[(Causalean.Experimentation.DesignBased.prodDesign D).toMeasure] 0` | A family of coordinate designs, reveal permutation, prefix length, statistic, and zero explicit prefix conditional expectation imply the measure-theoretic conditional expectation is almost everywhere zero. |
| `Experimentation.DesignBased.finitePredictableVariation_ae_eq_measurePredictableVariation` | `Causalean.Experimentation.DesignBased.finitePredictableVariation D pi X =ᵐ[(Causalean.Experimentation.DesignBased.prodDesign D).toMeasure] Causalean.Experimentation.DesignBased.measurePredictableVariation (Causalean.Experimentation.DesignBased.prodDesign D).toMeasure (Causalean.Experimentation.DesignBased.revealFiltration pi) X` | A family of coordinate designs, reveal permutation, and increment family give an almost-everywhere equality between finite-design and measure-theoretic predictable variations under the product-design measure. |
| `Experimentation.DesignBased.finiteKolmogorovExpr_eq_measureKolmogorovExpr` | `Causalean.Experimentation.DesignBased.finiteKolmogorovExpr (Causalean.Experimentation.DesignBased.prodDesign D) Y = Causalean.Experimentation.DesignBased.measureKolmogorovExpr (Causalean.Experimentation.DesignBased.prodDesign D).toMeasure Y` | A family of coordinate designs and real statistic give an exact identification between the finite-design and measure-theoretic Kolmogorov expressions under the induced product-design measure. |
| `Experimentation.DesignBased.finiteFourthMomentError_eq_measureFourthMomentError` | `Causalean.Experimentation.DesignBased.finiteFourthMomentError D pi X = Causalean.Experimentation.DesignBased.measureFourthMomentError (Causalean.Experimentation.DesignBased.prodDesign D).toMeasure (Causalean.Experimentation.DesignBased.revealFiltration pi) X` | A family of coordinate designs, reveal permutation, and increment family give an exact identification between finite-design and measure-theoretic fourth-moment errors, including the predictable-variation term. |
| `Experimentation.DesignBased.finiteDesign_heydeBrown_fourthMoment` | `Causalean.Experimentation.DesignBased.IsPrefixMartingaleDifference D pi X → (∑ s, (Causalean.Experimentation.DesignBased.prodDesign D).E fun w => X s w ^ 2) = 1 → Causalean.Experimentation.DesignBased.HeydeBrownFourthMomentPremise (Causalean.Experimentation.DesignBased.prodDesign D).toMeasure (Causalean.Experimentation.DesignBased.revealFiltration pi) X C → (Causalean.Experimentation.DesignBased.finiteKolmogorovExpr (Causalean.Experimentation.DesignBased.prodDesign D) fun w => ∑ s, X s w) ≤ C * (Causalean.Experimentation.DesignBased.finiteFourthMomentError D pi X).rpow (1 / 5)` | Given coordinate designs, a reveal permutation, an increment family, and a bound constant, if the increments are prefix martingale differences, their total second moment is one, and the supplied Heyde--Brown premise holds, then their sum satisfies the finite-design one-fifth-power Kolmogorov bound. |
<!-- /GEN -->

### `Experimentation/TwoStageInterference/{Basic,Stratified,Unbiased,Effects}.lean` — two-stage estimands, stratified interference, unbiasedness

Hudgens & Halloran (2008). Groups `ι`, group `i` of size `n i`; within-group assignment
`WAssign n i = Fin (n i) → Bool`; two-stage `jointDesign D₁ ψ φ = compound D₁ (fun s i => if s i then ψ i else φ i)`.
Partial interference is structural (the product over groups); the only modeling restriction is
*within*-group stratified interference, needed only for the variance theory (Phase 1 unbiasedness
holds without it). Stage-1 and within-group design propensities (`C/N`, `mᵢ/nᵢ`) enter as
hypotheses — the design-based known-propensity stance; Assumption 1's mixed strategy satisfies them.
Plan: `doc/hudgens_halloran_plan.md`. Namespace `Causalean.Experimentation.TwoStageInterference`.

| Declaration | Statement | Description |
|---|---|---|
| `WAssign` / `StratAssign` / `jointDesign` | `Fin (n i)→Bool`; `ι→Bool`; `compound D₁ (…)` | Within-group and stage-1 assignment spaces and the joint two-stage design. |
| `indMean` / `groupMean` / `popMean` / `indMarg` / `popMarg` | `ȳ_ij(z;ρ)` conditional mean; group/population averages; marginal versions | The average-potential-outcome estimands (conditional on own treatment `z`, and the marginal forms). |
| `CE_direct` / `CE_indirect` / `CE_total` / `CE_overall` | `ȳ(0;ψ)−ȳ(1;ψ)`; `ȳ(0;φ)−ȳ(0;ψ)`; `ȳ(0;φ)−ȳ(1;ψ)`; `ȳ(φ)−ȳ(ψ)` | The four population causal-effect contrasts (direct, indirect/spillover, total, overall). |
| `groupEst` / `popEst` / `estDirect` / `estIndirect` / `estTotal` | within-group Hájek mean; population average over the selected groups; the effect contrasts | The estimators (fixed-count Hájek form, hence linear in the treatment indicators). |
| `numTreatedOthers` / `stratExpo` / `StratifiedInterference` / `exists_strat_factor` | count of other treated; `(wⱼ, #others)`; Assumption 2; factorization `Y i j w = g (stratExpo i j w)` | Stratified interference (`Stratified.lean`): outcomes depend on the assignment only through own treatment and the count of other treated units; hence factor through the exposure. **Proved.** |
| `E_groupEst` | `E[Ŷ_i(z;ρ)] = ȳ_i(z;ρ)` | Within-group unbiasedness under constant treatment propensity `mᵢ/nᵢ`. **Proved.** |
| `E_popEst` / `E_popEst_pick` | `E[Ŷ(z;ψ)] = ȳ(z;ψ)` and the strategy-agnostic generalization | **Theorem 1**: population unbiasedness, via the stage-2 collapse engine; `E_popEst_pick` covers either allocation strategy. **Proved.** |
| `E_estDirect` / `E_estIndirect` / `E_estTotal` | `E[effect estimator] = CE_{D,I,T}` | **Theorems 1–3**: the direct/indirect/total effect estimators are exactly unbiased for their estimands. **Proved.** |
| `CE_total_decomp` | `CE^T = CE^D + CE^I` | The total effect decomposes into the direct plus indirect effects. **Proved.** |

### `Experimentation/TwoStageInterference/{Variance,VarianceMoments,VarianceConservative}.lean` — Theorem 5 (within-group Neyman variance) + conservative estimator (conservativeness proved)

Hudgens & Halloran (2008, JASA), "Toward Causal Inference With Interference". Within one group under
a completely randomized experiment that always treats exactly `K` of `n` units, and under stratified
interference (Assumption 2), each unit's outcome on the design support is two-valued — `a j` when
treated, `b j` when in control — so the difference-in-means estimator is linear in the treatment
indicators and its randomization variance is the classical Neyman completely-randomized variance.
The two-valued outcomes `a, b` are taken as data; the link to the stratified factorization
(`exists_strat_factor`) is upstream. The completely-randomized first/second-order propensities enter
as hypotheses `hmean` (`E[Tⱼ]=K/n`) and `hpair` (`E[TⱼTₖ]=K(K−1)/(n(n−1))`, `j≠k`). Namespace
`Causalean.Experimentation.TwoStageInterference`.

| Declaration | Statement | Description |
|---|---|---|
| `T` | `T j = ind (fun w => w j = true)` | Treatment indicator of unit `j` on the assignment space `Fin n → Bool` (design-independent). |
| `tauHat` | `(∑ⱼ bⱼ(1−Tⱼ))/(n−K) − (∑ⱼ aⱼTⱼ)/K` | Difference-in-means estimator `ȳ(0)−ȳ(1)`: control mean minus treated mean as a function of the assignment. |
| `popMeanV` / `S1` / `S0` / `Stau` | `x̄=(∑x)/n`; `S₁=∑(aⱼ−ā)²/(n−1)`; `S₀=∑(bⱼ−b̄)²/(n−1)`; `Sτ=∑((aⱼ−bⱼ)−(ā−b̄))²/(n−1)` | Population sample variances (Neyman, `n−1` denominator) of treated-state, control-state outcomes and unit effects. |
| `FiniteDesign.Var_add_const` | `Var(X+c)=Var X` | Variance is shift-invariant (substrate helper). |
| `sum_sum_ite_quadratic` | `∑ⱼ∑ₖ cⱼcₖ(if j=k then vd else vo) = vo(∑c)²+(vd−vo)∑c²` | The double-sum-to-split-form algebraic core turning `Var_linear_comb` into the Neyman split. |
| `sum_sub_mean_sq` | `∑ⱼ(xⱼ−x̄)² = ∑ⱼxⱼ² − (∑x)²/m` | Sum of squared deviations equals raw second moment minus squared first moment over `m`. |
| `cov_diag` / `cov_offdiag` | `Cov(Tⱼ,Tⱼ)=(K/n)(1−K/n)`; `Cov(Tⱼ,Tₖ)=K(K−1)/(n(n−1))−(K/n)²` (`j≠k`) | Complete-randomization indicator covariances from `hmean`/`hpair`. **Proved.** |
| `Var_tauHat` | `ρ.Var(tauHat) = S₁/K + S₀/(n−K) − Sτ/n` | **Theorem 5 (Neyman form).** Derived (not assumed) from the indicator covariances via the linear-comb double sum and moment algebra. **Proved, sorry-free.** |
| `obsMeanTreated` / `obsMeanControl` | `(∑ⱼTⱼaⱼ)/K`; `(∑ⱼ(1−Tⱼ)bⱼ)/(n−K)` | Empirical means among observed treated / control units (`VarianceConservative.lean`). |
| `ShatTreated` / `ShatControl` | `∑ⱼTⱼ(aⱼ−ā_obs)²/(K−1)`; `∑ⱼ(1−Tⱼ)(bⱼ−b̄_obs)²/(n−K−1)` | Observed sample variances among treated / control units. |
| `varHat` | `Ŝ₁/K + Ŝ₀/(n−K)` | Conservative variance estimator (empirical analogue of the first two Neyman terms), computable from one realized assignment. |
| `varHat_nonneg` | `0 ≤ varHat` (for `1≤K`, `K+1≤n`) | Pointwise nonnegativity: sum of two nonnegative sample variances over positive counts. **Proved.** |
| `E_congr_supp` / `E_Shat` (`VarianceMoments.lean`) | support-congruence for `E`; `E[(1/(M−1))∑ Uⱼ(xⱼ−x̄_U)²] = S_x` | Generic unbiasedness of the observed sample variance under a `{0,1}` selection family `U` with the CRE moments (first `M/n`, pairwise `M(M−1)/(n(n−1))`, deterministic support total `M`). **Proved, axiom-clean.** |
| `E_ShatTreated` / `E_ShatControl` | `ρ.E Ŝ₁ = S₁`; `ρ.E Ŝ₀ = S₀` | The observed treated/control sample variances are unbiased for the population variances under sampling without replacement (`E_Shat` with `U=T`,`M=K` and `U=1−T`,`M=n−K`; control moments derived from `hmean`/`hpair`/`hsupp`). **Proved.** |
| `E_varHat_conservative` | `ρ.Var(tauHat) ≤ ρ.E(varHat)` | **Conservativeness (HH Eq. 9).** `E[v̂ar] = S₁/K + S₀/(n−K) = Var + Sτ/n ≥ Var`. **Proved, axiom-clean.** Hypotheses: CRE moments `hmean`/`hpair`, deterministic treated count on the support `hsupp` (`∑ⱼTⱼ=K`), and non-degeneracy `2≤K`, `K+2≤n` (so both sample variances are well-defined). |

### `Experimentation/TwoStageInterference/{StageOne,BetweenGroup}.lean` — Theorem 4 (two-stage variance decomposition)

The between-group / within-group variance decomposition of the population estimator `Ŷ(z;ψ)` under
the two-stage mixed-strategy design, assembled from the law of total variance
(`Var_compound_eq_tower`), the product-design within-group variance (`Var_prod_linear_comb`), and the
stage-1 SRS sample-mean variance. Namespace `Causalean.Experimentation.TwoStageInterference`.

| Declaration | Statement | Description |
|---|---|---|
| `SmuVar` / `Var_srs_mean` (`StageOne.lean`) | `SmuVar μ = ∑(μᵢ−μ̄)²/(N−1)`; `D₁.Var((1/m)∑ᵢ Uᵢμᵢ) = (1−m/N)/m · SmuVar μ` | The variance of a simple-random-sample mean of `m` of `N` fixed numbers is the finite-population correction `(1−m/N)/m` times their population variance — the between-group variance term. Given the SRS selection moments (first `m/N`, pairwise `m(m−1)/(N(N−1))`, diagonal `(m/N)(1−m/N)`). **Proved, derived constant.** |
| `Var_groupAgg` (`BetweenGroup.lean`) | `Var((∑ᵢ 1(Sᵢ=ψ)·gᵢ(wᵢ))/C) = (1−C/N)/C·SmuVar((ψ·).E g·) + (1/(CN))∑ᵢ (ψ i).Var gᵢ` | The abstract two-stage variance decomposition for an arbitrary per-group statistic `g`; Theorems 4 and 6 are corollaries (instantiating `g` as a single-treatment mean / a per-group effect difference). Assembled via the law of total variance. **Proved, axiom-clean.** |
| `Var_popEst` (`BetweenGroup.lean`) | `Var(Ŷ(z;ψ)) = (1−C/N)/C · σ²_D + (1/(CN))∑ᵢ Var(Ŷ_i(z;ψ)∣Sᵢ=ψ)` | **Theorem 4**: the two-stage randomization variance of the population mean estimator splits into a between-group SRS term (finite-population correction `(1−C/N)/C` on the group-level means `ȳ_i(z;ψ)`) plus a within-group term averaging the per-group conditional variances. A corollary of `Var_groupAgg`. Hypotheses: within propensities `mᵢ/nᵢ`, stage-1 marginal `C/N` and pair `C(C−1)/(N(N−1))`. **Proved, axiom-clean.** |
| `Var_estDirect` (`BetweenGroupEffect.lean`) | `Var(ĈE^D(ψ)) = (1−C/N)/C · σ²_D + (1/(CN))∑ᵢ Var(ĈE^D_i(ψ)∣Sᵢ=ψ)` | **Theorem 6**: the two-stage variance of the direct-*effect* estimator `Ŷ(0;ψ)−Ŷ(1;ψ)` — between-group SRS term over the group-level direct effects `ȳ_i(0;ψ)−ȳ_i(1;ψ)` plus a within-group term averaging the per-group direct-effect-estimator variances. Corollary of `Var_groupAgg` with `gᵢ` the per-group direct-effect estimator (`Ŷ(0;ψ)−Ŷ(1;ψ) = (∑ᵢ 1(Sᵢ=ψ)·dᵢ(wᵢ))/C`). **Proved, axiom-clean.** |

### `Experimentation/TwoStageInterference/Asymptotic/{Setup,Consistency,CLT,CLTDischarge,CLTDischargeMain,Wald}.lean` — Liu–Hudgens (2014) large-sample inference (minimal)

Liu & Hudgens (2014, JASA), "Large-Sample Randomization Inference of Causal Effects in the Presence of
Interference" — the asymptotic theory for the two-stage design, minimal direct-effect slice. Regime:
many groups (`m → ∞`), exact permutation first stage, **homogeneity**. The Prop 5.1 CLT is proved the
paper's own way — condition on the selection (groups are then independent), conditional CLT, lift to
unconditional via homogeneity — so **no finite-population (Hájek) CLT is needed**. The conditional CLT
is now discharged from primitives (the independent-summands CLT `prodDesign_clt`), so Prop 5.1 rests
on explicit homogeneity + regularity, not a CLT black box. Plan: `doc/liu_hudgens_plan.md`. Namespace
`Causalean.Experimentation.TwoStageInterference`.

| Declaration | Statement | Description |
|---|---|---|
| `LHExperiment` / `E_estD` / `var_estD` (`Setup.lean`) | the sequence-of-experiments bundle; `jointD.E estD = DEbar`; `jointD.Var estD = directVar` | The bundle carrying the two-stage design + its known propensities; the unbiasedness and Theorem-6 variance bridges (from `E_estDirect` / `Var_estDirect`). |
| `estDirect_consistent` (`Consistency.lean`) | `Var → 0 ⟹ D̂E(α₁) − DE̅ →ₚ 0` | Consistency of the direct-effect estimator via Chebyshev + the vanishing design variance. **Proved, axiom-clean.** |
| `tendsto_E_of_uniformBound` / `Pr_compound_eq_E_condPr` (`CLT.lean`) | mixture lifting (`E F_n → L` from uniform bounds); `(compound D₁ D₂).Pr P = D₁.E (conditional Pr)` | Reusable substrate: the unconditional law is the design-average of the conditional laws (from `E_compound_tower`), and uniform conditional convergence lifts through the average. **Proved.** |
| `directEffect_clt` (`CLT.lean`) | studentized `(D̂E − DE̅)/√Var →_d N(0,1)` | **Proposition 5.1** (direct effect), modulo the uniform conditional-CLT regularity `hcond` (the paper's Lindeberg + homogeneity). Proved by the tower bridge + mixture lifting. The `hcond`-free primitive form is `directEffect_clt_homogeneous` below. **Proved, axiom-clean.** |
| `tendsto_E_of_uniformBound_ae` / `Var_sub_const` (`CLTDischarge.lean`) | support-restricted mixture lifting (`E F_n → L` from bounds only where `D₁.p s ≠ 0`); `Var(X−c) = Var X` | The "a.e." variant of `tendsto_E_of_uniformBound`: the stage-1 average only weights support points, so a uniform bound on the support suffices to lift the conditional limit — needed because homogeneity (`hhom`) only relates conditional CDFs across the support. Plus the constant-shift variance invariance. **Proved.** |
| `Homogeneous` / `DEbar_eq_of_homogeneous` / `directVar_eq_of_homogeneous` / `stud_eq_sum_of_homogeneous` (`CLTDischarge.lean`) | the homogeneity + regularity bundle; `DEbar = δ`; `directVar = v/C`; `stud(s,w) = ∑ᵢ gₛ,ᵢ(wᵢ)` on the support | The faithful encoding of Prop 5.1's hypotheses (constant group direct effects `δ`, constant within-group variance `v n > 0`, bounded centered per-group estimator `M`, exactly-`C` selections on the support, the `B → 0` / `card·B³ → 0` rates, and selection-independence `hhom`), with the reductions that turn the conditional studentized statistic into a normalized independent sum. **Proved.** |
| `condCLT_ref` (`CLTDischargeMain.lean`) | conditional CDF at the reference selection `→ Φ(t)` | The conditional CLT, obtained by feeding the homogeneity-reduced per-coordinate summands `gₛ₀,ᵢ` (mean-zero, unit total variance via `Var_prod_linear_comb`, uniformly bounded) into the independent-summands CLT `prodDesign_clt`. **Proved, axiom-clean.** |
| `directEffect_clt_homogeneous` (`CLTDischargeMain.lean`) | studentized `(D̂E − DE̅)/√Var →_d N(0,1)` | **Proposition 5.1, fully primitive.** Identical conclusion to `directEffect_clt` but `hcond`-free: it rests on the explicit `Homogeneous` bundle. The conditional CLT is `condCLT_ref` (from `prodDesign_clt`); `hhom` lifts the uniform bound across the stage-1 support; `tendsto_E_of_uniformBound_ae` averages it. **Proved, axiom-clean.** |
| `prodDesign_Pr_reindex` (`DesignBased/ProductReindex.lean`) / `hhom_of_identical` / `directEffect_clt_identical` (`Asymptotic/Identical.lean`) | `(prodDesign D).Pr(P∘(·∘σ)) = (prodDesign (D∘σ)).Pr P`; `hhom` for identical groups; the CLT under identical groups | **Prop 5.1 on literal identical groups** — `hhom` is *derived*, not assumed. The reindex lemma (a pure finite-sum permutation invariance) shows the conditional CDF is selection-independent when all groups are identical (a permutation `σ` matching two equal-size selections, built via `Equiv.sumCompl` + `Fintype.equivOfCardEq`, relabels one conditional law to the other). `directEffect_clt_identical` then rests only on identical groups + bounded outcomes + the many-groups rate. **Proved, axiom-clean.** |
| `wald_coverage_oracle` (`Wald.lean`) | `1 − γ ≤ liminf Pr(\|D̂E − DE̅\| ≤ z·√Var)` | Asymptotic coverage of the oracle Wald interval `D̂E ± z·√Var`, from the CLT + standard-normal CDF symmetry (transplant of the A-S oracle `wald_coverage`). **Proved, axiom-clean.** |
| `wald_coverage_feasible` (`WaldFeasible.lean`) | `1 − γ ≤ liminf Pr(\|D̂E − DE̅\| ≤ z·√V̂)` | Asymptotic coverage of the **feasible** Wald interval `D̂E ± z·√V̂` using an *estimated* variance, from the per-threshold CLT + a single conservative-consistency input `hVhat` (`Pr(V̂ < (1−ε)·Var) → 0`), with the estimator `Vh` abstract — transplant of the A-S feasible `wald_coverage_feasible`. Discharging `hVhat` to a concrete two-stage estimator (the A-S `_of_conditions` analogue) is future work. **Proved, axiom-clean.** |

### `UnknownInterference/` — Sävje–Aronow–Hudgens (2021), EATE under unknown interference (arXiv:1711.06399)

Bernoulli-design core of "Average treatment effects in the presence of unknown interference." Units `U`, treatment vector `z : U → Bool`, potential outcomes `y i z` depending on the *whole* assignment (interference), of unknown form. Scope: Bernoulli design with the Horvitz–Thompson **and Hájek** estimators (the paper's conceptual heart). Deferred (see `doc/savje_aronow_hudgens_plan.md`): complete/paired/arbitrary designs (α-mixing), the variance-estimator results, external validity. No CLT — the paper proves Chebyshev is sharp and Gaussian approximations generally fail under these conditions.

| Declaration (file) | Statement | Description |
|---|---|---|
| `Interferes` / `InterfDep` / `dbar` (`Basic.lean`) | interference indicator `I ℓ i`; interference dependence (some `ℓ` interferes with both `i`,`j`); average dependence `d̄ = n⁻¹∑ᵢ∑ⱼ 1[InterfDep i j]` | The interference structure; `d̄` is the basis for "restricted interference" `d̄ = o(n)`. **Defs** |
| `tau` / `ACATE` / `EATE` / `htEst` (`Basic.lean`) | `τ_i(z₋ᵢ)=y_i(1;z₋ᵢ)−y_i(0;z₋ᵢ)`; `ACATE(z)=n⁻¹∑ᵢτ_i`; `EATE = E[ACATE(Z)]`; the Horvitz–Thompson estimator | The estimand (assignment-conditional ATE marginalized over the design; generalizes ATE) + the HT estimator. **Defs** |
| `y_eq_of_agree_on_interferers` (`Basic.lean`) | if `z`,`z'` agree on every unit interfering with `i` then `y i z = y i z'` | A unit's outcome depends only on its interferers — the bridge to disjoint-block independence. **Proved, axiom-clean.** |
| `bernoulliDesign` (`Bernoulli.lean`) | `prodDesign` of per-unit coin flips with `Pr(Z_i=1)=p_i` | The Bernoulli design; cross-unit independence is structural. **Def + marginal lemmas** |
| `htEst_unbiased` (`Unbiased.lean`) | `E[ĤT] = EATE` under the Bernoulli design | HT is **exactly unbiased** for EATE (`Z_i ⊥ Z₋ᵢ` ⇒ `E[Z_iY_i/p_i]=E[y_i(1;Z₋ᵢ)]`). **Proved, axiom-clean.** |
| `var_htEst_le` (`VarianceBound.lean`) | `Var(ĤT) ≤ k⁴·d̄/n` | The quantitative heart (paper's body bound): covariances vanish off the interference-dependence graph (disjoint-block independence `Cov_prod_disjoint_zero`), surviving ones bounded by `k⁴`, counted by `dbarCount = n·d̄`. **Proved, axiom-clean.** |
| `htEst_consistent_eate` (`Consistency.lean`) | along a sequence with `k⁴·d̄/n → 0`, `Pr(\|ĤT − EATE\| ≥ ε) → 0` | **Flagship (Prop, Bernoulli rate).** HT is consistent for EATE under restricted interference, no structural knowledge of the interference — Chebyshev on the variance bound. The paper's `O_p(√(d̄/n))` rate is exactly this Chebyshev reading. **Proved, axiom-clean.** |
| `root_n_var` (`Consistency.lean`) | `d̄ ≤ C ⇒ n·Var(ĤT) ≤ k⁴·C` | **Root-n consistency (Corollary)** under bounded interference: the variance is `O(1/n)`. **Proved, axiom-clean.** |
| `hajekEst` / `hajek_consistent_eate` (`Hajek.lean`) | the Hájek (ratio/IPW) estimator `Â₁/B̂₁ − Â₀/B̂₀`; along a sequence with `k⁴·d̄/n → 0`, uniformly bounded `k`, and bounded potential-outcome moments, `ĤA →ₚ EATE` | **Hájek consistency.** Each numerator `Âₜ →ₚ ȳ(t)` (vanishing variance) and each realized-weight normalizer `B̂ₜ →ₚ 1` (`E[B̂ₜ]=1`); the Slutsky ratio step gives `ĤA →ₚ ȳ(1)−ȳ(0) = EATE`. Adds the uniform-`k` bound and Assumption-C potential-outcome moments beyond the HT hypotheses (disclosed). **Proved, axiom-clean.** |
| `VhatBer` / `E_VhatBer_bias` (`Confidence.lean`) | conventional variance estimator `V̂_Ber = n⁻²∑ĤTᵢ²`; `E[V̂_Ber] − Var(ĤT) = n⁻²(∑(E ĤTᵢ)² − ∑_{i≠j}Cov(ĤTᵢ,ĤTⱼ))` | **Anti-conservativeness mechanism** (the warning): the off-diagonal covariances (nonzero only on the interference graph, either sign) are the bias making `V̂_Ber` understate uncertainty. **Proved, axiom-clean.** |
| `var_htEst_le_inflated` (`Confidence.lean`) | `(∀ i, degDep i ≤ D) ⇒ Var(ĤT) ≤ (1+D)·E[V̂_Ber]` | **Conservative inflation** (the fix, in expectation): inflating by an interference-degree bound restores conservativeness — the cleaner cousin of the paper's `d_max`/spectral-radius estimators. **Proved, axiom-clean.** |
| `chebyshev_ci_eate` / `eate_ci_kbound` (`Confidence.lean`) | `Var(ĤT) ≤ V ⇒ Pr(\|ĤT − EATE\| ≤ √(V/α)) ≥ 1−α`; concretely the interval `ĤT ± √(k⁴·d̄/(n·α))` covers EATE `≥ 1−α` | **Finite-sample confidence interval for EATE** under unknown interference, Chebyshev-based (the paper proves a CLT fails). Exact, from HT unbiasedness + the proven variance bound. **Proved, axiom-clean.** |
| `FiniteDesign.E_prod_block_mul` / `Cov_prod_disjoint_zero` (`DesignBased/ProductBlock.lean`) | functions of disjoint coordinate blocks of a product design factor in expectation / are uncorrelated | Substrate (block generalization of `E_prod_apply₂`/`Cov_prod_apply_of_ne`), proved via the existing product-measure independence bridge; requires `MeasurableSpace`/`MeasurableSingletonClass` on the coordinate types. **Proved, axiom-clean.** |
| `FiniteDesign.TendstoInProb` / `tendstoInProb_of_var` / `tendstoInProb_div_one` / `.sub` / `.add` / `.abs` / `.const_mul` · `BoundedInProb` / `boundedInProb_of_var_bound` / `TendstoInProb.mul_boundedInProb` (`DesignBased/InProb.lean`) | convergence in probability for finite designs; the Chebyshev consistency engine; the Slutsky ratio step (`X→ₚa`, `Y→ₚ1`, `|a|≤M` ⇒ `X/Y→ₚa`); closure under sums/differences/absolute value/scaling; uniform tightness (`BoundedInProb`) with a variance-bound criterion and the product-tightness engine `o_p × O_p = o_p` | Reusable in-probability substrate for ratio estimators (Hájek); `mul_boundedInProb` is the delta-method-remainder engine behind the bipartite denominator-tightness discharge. **Proved, axiom-clean.** |

## 10z. Reusable minimax and nonparametric reduction substrate

These modules package the experiment-level tools used by sharp lower-bound
arguments: maximal couplings and coordinatewise overlap, marked-Poisson
depoissonization, outer integration, countable empirical-process reductions,
Bernoulli common-statistic kernels, local-polynomial coercivity, and planar
polar-integration identities.  They are independent of any particular paper
construction and can be imported directly from the Causalean hierarchy.

### Reusable affine sign-cell closure

Finite real affine systems with mixed strict and weak inequalities can be represented as an
`AffineSystem`. The strict cell has the weak relaxation as its closure whenever it is
nonempty; the bounded common-slack value is positive exactly when that strict cell is
nonempty. Consequently, continuous objectives have equal bounded extrema on the strict
cell and its weak relaxation. Checked degree-one multivariate polynomial systems compile to
this API without changing either cell.

<!-- GEN:Causalean.Mathlib.Optimization.AffineSignCellClosure.Basic -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Optimization.AffineSignCellClosure.AffineFn` | `ℕ → Type` | Given a finite number of coordinates, an affine real-valued function is specified by one coefficient for each coordinate and one constant term. |
| `Mathlib.Optimization.AffineSignCellClosure.AffineFn.eval` | `(Fin n → ℝ) → ℝ` | Given an affine function and a coordinate vector, its evaluated real value is given by the finite coefficient-weighted sum plus the constant. |
| `Mathlib.Optimization.AffineSignCellClosure.AffineFn.eval_affineCombination` | `f.eval ((1 - t) • x + t • y) = (1 - t) * f.eval x + t * f.eval y` | Given an affine function, two coordinate vectors, and a real weight, evaluation at their affine combination equals the same affine combination of their evaluations. |
| `Mathlib.Optimization.AffineSignCellClosure.AffineFn.continuous_eval` | `Continuous f.eval` | Given an affine function, its evaluation map is continuous. |
| `Mathlib.Optimization.AffineSignCellClosure.ConstraintKind` | `Type` | A constraint kind records whether its affine inequality is weak or strict. |
| `Mathlib.Optimization.AffineSignCellClosure.instDecidableEqConstraintKind` | `DecidableEq Causalean.Mathlib.Optimization.AffineSignCellClosure.ConstraintKind` | — |
| `Mathlib.Optimization.AffineSignCellClosure.instReprConstraintKind` | `Repr Causalean.Mathlib.Optimization.AffineSignCellClosure.ConstraintKind` | — |
| `Mathlib.Optimization.AffineSignCellClosure.Constraint` | `ℕ → Type` | Given a finite number of coordinates, a marked affine constraint contains its normalized affine left-hand side and its weak-or-strict mark. |
| `Mathlib.Optimization.AffineSignCellClosure.AffineSystem` | `ℕ → Type` | Given a finite number of coordinates, an affine constraint system is given by a finite list of marked affine constraints. |
| `Mathlib.Optimization.AffineSignCellClosure.Constraint.strictHolds` | `(Fin n → ℝ) → Prop` | Given a marked affine constraint and a coordinate vector, the original constraint-satisfaction condition uses the comparison selected by the constraint's mark. |
| `Mathlib.Optimization.AffineSignCellClosure.Constraint.weakHolds` | `(Fin n → ℝ) → Prop` | Given a marked affine constraint and a coordinate vector, the weak constraint-satisfaction condition is given by the nonpositive affine evaluation. |
| `Mathlib.Optimization.AffineSignCellClosure.strictCell` | `Set (Fin n → ℝ)` | Given an affine constraint system, its strict cell is given by the points satisfying every listed constraint using its original comparison. |
| `Mathlib.Optimization.AffineSignCellClosure.weakCell` | `Set (Fin n → ℝ)` | Given an affine constraint system, its weak relaxation is given by the points weakly satisfying every listed constraint. |
| `Mathlib.Optimization.AffineSignCellClosure.mem_strictCell` | `x ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ ↔ ∀ c ∈ Γ, c.strictHolds x` | Given a point, membership in the strict cell is equivalent to satisfying every listed constraint with its original comparison. |
| `Mathlib.Optimization.AffineSignCellClosure.mem_weakCell` | `x ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ ↔ ∀ c ∈ Γ, c.weakHolds x` | Given a point, membership in the weak relaxation is equivalent to weakly satisfying every listed constraint. |
| `Mathlib.Optimization.AffineSignCellClosure.strictCell_subset_weakCell` | `Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ ⊆ Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ` | Given an affine constraint system, every strictly feasible point belongs to its weak relaxation. |
| `Mathlib.Optimization.AffineSignCellClosure.isClosed_weakCell` | `IsClosed (Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ)` | Given an affine constraint system, its weak relaxation is closed. |
| `Mathlib.Optimization.AffineSignCellClosure.convex_weakCell` | `Convex ℝ (Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ)` | Given an affine constraint system, its weak relaxation is convex. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Optimization.AffineSignCellClosure.Closure -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Optimization.AffineSignCellClosure.segmentPoint` | `(Fin n → ℝ) → (Fin n → ℝ) → ℝ → Fin n → ℝ` | Given a weak endpoint, a distinguished strict endpoint, and a real weight, the segment point is given by placing weight `ε` on the strict endpoint. |
| `Mathlib.Optimization.AffineSignCellClosure.tendsto_segmentPoint_zero` | `Filter.Tendsto (Causalean.Mathlib.Optimization.AffineSignCellClosure.segmentPoint x x₀) (nhds 0) (nhds x)` | Given a weak endpoint and a distinguished strict endpoint, their segment points converge to the weak endpoint as the strict-endpoint weight tends to zero. |
| `Mathlib.Optimization.AffineSignCellClosure.segmentPoint_mem_strictCell` | `x ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ → x₀ ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → Causalean.Mathlib.Optimization.AffineSignCellClosure.segmentPoint x x₀ ε ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ` | Given a weakly feasible point, a strictly feasible point, a positive segment weight, and a weight at most one, the corresponding segment point is strictly feasible. |
| `Mathlib.Optimization.AffineSignCellClosure.exists_strictCell_sequence_tendsto` | `x ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ → x₀ ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ → ∃ u, (∀ (k : ℕ), u k ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) ∧ Filter.Tendsto u Filter.atTop (nhds x)` | Given a weakly feasible point and a strictly feasible point, there is a sequence of strictly feasible points converging to the weakly feasible point. |
| `Mathlib.Optimization.AffineSignCellClosure.weakCell_subset_closure_strictCell` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty → Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ ⊆ closure (Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ)` | Given a nonempty strict cell, every point of the weak relaxation belongs to the closure of the strict cell. |
| `Mathlib.Optimization.AffineSignCellClosure.closure_strictCell_eq_weakCell` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty → closure (Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) = Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ` | Given a nonempty strict cell, the closure of that strict cell equals its weak relaxation. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Optimization.AffineSignCellClosure.CommonSlack -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Optimization.AffineSignCellClosure.commonSlackFeasible` | `(Fin n → ℝ) → ℝ → Prop` | Given an affine constraint system, a coordinate vector, and a real slack, the common-slack feasibility condition is given by the slack lying between zero and one, the slack being at most one, and weak constraints remaining at zero while strict constraints are at most the negative slack. |
| `Mathlib.Optimization.AffineSignCellClosure.commonSlackSet` | `Set ℝ` | Given an affine constraint system, its feasible slack set is given by the slacks for which some coordinate vector is common-slack feasible. |
| `Mathlib.Optimization.AffineSignCellClosure.commonSlackValue` | `ℝ` | Given an affine constraint system, its common-slack value is given by the supremum of its feasible slack set. |
| `Mathlib.Optimization.AffineSignCellClosure.bddAbove_commonSlackSet` | `BddAbove (Causalean.Mathlib.Optimization.AffineSignCellClosure.commonSlackSet Γ)` | Given an affine constraint system, its feasible slack set is bounded above. |
| `Mathlib.Optimization.AffineSignCellClosure.positiveSlackWitness_of_strictPoint` | `x ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ → ∃ δ, 0 < δ ∧ Causalean.Mathlib.Optimization.AffineSignCellClosure.commonSlackFeasible Γ x δ` | Given a strictly feasible point, there is a positive common slack for that same point. |
| `Mathlib.Optimization.AffineSignCellClosure.strictPoint_of_positiveSlack` | `0 < δ → Causalean.Mathlib.Optimization.AffineSignCellClosure.commonSlackFeasible Γ x δ → x ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ` | Given a positive slack and a common-slack feasible point, that point belongs to the strict cell. |
| `Mathlib.Optimization.AffineSignCellClosure.commonSlackValue_pos_of_witness` | `0 < δ → Causalean.Mathlib.Optimization.AffineSignCellClosure.commonSlackFeasible Γ x δ → 0 < Causalean.Mathlib.Optimization.AffineSignCellClosure.commonSlackValue Γ` | Given a positive slack and a common-slack feasible point, the common-slack value is positive. |
| `Mathlib.Optimization.AffineSignCellClosure.positiveSlackWitness_of_commonSlackValue_pos` | `0 < Causalean.Mathlib.Optimization.AffineSignCellClosure.commonSlackValue Γ → ∃ δ, 0 < δ ∧ δ ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.commonSlackSet Γ` | Given a positive common-slack value, some feasible slack is positive. |
| `Mathlib.Optimization.AffineSignCellClosure.strictFeasible_iff_commonSlackValue_pos` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty ↔ 0 < Causalean.Mathlib.Optimization.AffineSignCellClosure.commonSlackValue Γ` | Given an affine constraint system, its strict cell is nonempty exactly when its bounded common-slack value is positive. |
| `Mathlib.Optimization.AffineSignCellClosure.commonSlackValue_nil` | `Causalean.Mathlib.Optimization.AffineSignCellClosure.commonSlackValue [] = 1` | Given a number of coordinates, the empty system's common-slack value equals one. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Optimization.AffineSignCellClosure.Extrema -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Optimization.AffineSignCellClosure.closure_image_strictCell_eq_closure_image_weakCell` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty → Continuous φ → closure (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) = closure (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ)` | Given a nonempty strict cell and a continuous real objective, the closures of its strict-cell and weak-cell image sets are equal. |
| `Mathlib.Optimization.AffineSignCellClosure.bddBelow_image_weakCell_of_strictCell` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty → Continuous φ → BddBelow (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) → BddBelow (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ)` | Given a nonempty strict cell, a continuous real objective, and a lower bound for its strict-cell image, the weak-cell image is bounded below. |
| `Mathlib.Optimization.AffineSignCellClosure.bddAbove_image_weakCell_of_strictCell` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty → Continuous φ → BddAbove (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) → BddAbove (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ)` | Given a nonempty strict cell, a continuous real objective, and an upper bound for its strict-cell image, the weak-cell image is bounded above. |
| `Mathlib.Optimization.AffineSignCellClosure.sInf_image_strictCell_eq_weakCell` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty → Continuous φ → BddBelow (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) → sInf (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) = sInf (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ)` | Given a nonempty strict cell, a continuous real objective, and a lower bound for its strict-cell image, the strict and weak image sets have the same infimum. |
| `Mathlib.Optimization.AffineSignCellClosure.sSup_image_strictCell_eq_weakCell` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty → Continuous φ → BddAbove (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) → sSup (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) = sSup (φ '' Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ)` | Given a nonempty strict cell, a continuous real objective, and an upper bound for its strict-cell image, the strict and weak image sets have the same supremum. |
| `Mathlib.Optimization.AffineSignCellClosure.sInf_affineEval_strictCell_eq_weakCell` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty → BddBelow (f.eval '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) → sInf (f.eval '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) = sInf (f.eval '' Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ)` | Given an affine objective, a nonempty strict cell, and a lower bound for the strict-cell objective image, the affine objective has the same infimum on the strict cell and weak relaxation. |
| `Mathlib.Optimization.AffineSignCellClosure.sSup_affineEval_strictCell_eq_weakCell` | `(Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ).Nonempty → BddAbove (f.eval '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) → sSup (f.eval '' Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Γ) = sSup (f.eval '' Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Γ)` | Given an affine objective, a nonempty strict cell, and an upper bound for the strict-cell objective image, the affine objective has the same supremum on the strict cell and weak relaxation. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Optimization.AffineSignCellClosure.Polynomial -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Optimization.AffineSignCellClosure.affineFnOfMvPolynomial` | `MvPolynomial (Fin n) ℝ → Causalean.Mathlib.Optimization.AffineSignCellClosure.AffineFn n` | Given a real multivariate polynomial, its compiled affine function is given by the coefficients of its degree-one monomials and its constant coefficient. |
| `Mathlib.Optimization.AffineSignCellClosure.affineFnOfMvPolynomial_eval` | `p.totalDegree ≤ 1 → ∀ (x : Fin n → ℝ), (Causalean.Mathlib.Optimization.AffineSignCellClosure.affineFnOfMvPolynomial p).eval x = (MvPolynomial.eval x) p` | Given a real multivariate polynomial, a proof that its total degree is at most one, and a coordinate vector, evaluating its compiled affine function equals evaluating the polynomial. |
| `Mathlib.Optimization.AffineSignCellClosure.PolynomialConstraint` | `ℕ → Type` | Given a finite number of coordinates, a checked polynomial constraint contains its polynomial left-hand side, its weak-or-strict mark, and a certificate that it is affine. |
| `Mathlib.Optimization.AffineSignCellClosure.PolynomialConstraint.toConstraint` | `Causalean.Mathlib.Optimization.AffineSignCellClosure.Constraint n` | Given a checked polynomial constraint, its affine constraint compilation is given by the compiled affine function with the original mark retained. |
| `Mathlib.Optimization.AffineSignCellClosure.affineSystemOfPolynomials` | `List (Causalean.Mathlib.Optimization.AffineSignCellClosure.PolynomialConstraint n) → Causalean.Mathlib.Optimization.AffineSignCellClosure.AffineSystem n` | Given a finite list of checked polynomial constraints, its compiled affine system is given by compiling every listed constraint. |
| `Mathlib.Optimization.AffineSignCellClosure.polynomialStrictCell` | `List (Causalean.Mathlib.Optimization.AffineSignCellClosure.PolynomialConstraint n) → Set (Fin n → ℝ)` | Given a finite list of checked polynomial constraints, its direct strict polynomial cell is given by satisfaction of each original weak-or-strict polynomial comparison. |
| `Mathlib.Optimization.AffineSignCellClosure.polynomialWeakCell` | `List (Causalean.Mathlib.Optimization.AffineSignCellClosure.PolynomialConstraint n) → Set (Fin n → ℝ)` | Given a finite list of checked polynomial constraints, its direct weak polynomial cell is given by weak satisfaction of every polynomial constraint. |
| `Mathlib.Optimization.AffineSignCellClosure.strictCell_affineSystemOfPolynomials` | `Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell (Causalean.Mathlib.Optimization.AffineSignCellClosure.affineSystemOfPolynomials Γ) = Causalean.Mathlib.Optimization.AffineSignCellClosure.polynomialStrictCell Γ` | Given a finite checked polynomial system, compilation preserves its strict cell. |
| `Mathlib.Optimization.AffineSignCellClosure.weakCell_affineSystemOfPolynomials` | `Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell (Causalean.Mathlib.Optimization.AffineSignCellClosure.affineSystemOfPolynomials Γ) = Causalean.Mathlib.Optimization.AffineSignCellClosure.polynomialWeakCell Γ` | Given a finite checked polynomial system, compilation preserves its weak cell. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Optimization.AffineSignCellClosure.Example -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Optimization.AffineSignCellClosure.mixedExample` | `Causalean.Mathlib.Optimization.AffineSignCellClosure.AffineSystem 1` | The mixed one-dimensional example system is given by the strict lower inequality `-x < 0` and the weak upper inequality `x - 1 ≤ 0`. |
| `Mathlib.Optimization.AffineSignCellClosure.mem_strictCell_mixedExample` | `x ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Causalean.Mathlib.Optimization.AffineSignCellClosure.mixedExample ↔ 0 < x 0 ∧ x 0 ≤ 1` | Given a one-dimensional coordinate vector, it belongs to the example's strict cell exactly when its coordinate lies above zero and at most one. |
| `Mathlib.Optimization.AffineSignCellClosure.mem_weakCell_mixedExample` | `x ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Causalean.Mathlib.Optimization.AffineSignCellClosure.mixedExample ↔ 0 ≤ x 0 ∧ x 0 ≤ 1` | Given a one-dimensional coordinate vector, it belongs to the example's weak cell exactly when its coordinate lies between zero and one inclusively. |
| `Mathlib.Optimization.AffineSignCellClosure.half_mem_strictCell_mixedExample` | `(fun x => 1 / 2) ∈ Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Causalean.Mathlib.Optimization.AffineSignCellClosure.mixedExample` | The constant one-half coordinate vector belongs to the example's strict cell. |
| `Mathlib.Optimization.AffineSignCellClosure.closure_strictCell_mixedExample` | `closure (Causalean.Mathlib.Optimization.AffineSignCellClosure.strictCell Causalean.Mathlib.Optimization.AffineSignCellClosure.mixedExample) = Causalean.Mathlib.Optimization.AffineSignCellClosure.weakCell Causalean.Mathlib.Optimization.AffineSignCellClosure.mixedExample` | The closure of the example's half-open strict interval equals its closed weak interval. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Optimization.AffineSignCellClosure.Main -->
_(no documented declarations in Causalean.Mathlib.Optimization.AffineSignCellClosure.Main)_
<!-- /GEN -->

### Paired Poisson-histogram Rao–Blackwell transfer

This package converts any estimator based on paired fixed samples into a
parameter-independent estimator on two independent count histograms. It supplies
the exact iid pairing law, conditional squared-risk contraction, a general
fixed-to-Poisson risk bound with explicit fallback loss, and the specialization
to Poisson means twice the fixed sample size.

<!-- GEN:Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.Basic -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram` | `(Fin m → X) → X → ℕ` | Given a finite ordered sample and an alphabet symbol, its finite-sample histogram count is the number of sample positions equal to that symbol. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal` | `(X → ℕ) → ℕ` | Given a finite count histogram, its histogram total is the sum of the counts over the alphabet. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal_finiteSampleHistogram` | `Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram x) = m` | The histogram of a finite ordered sample has total equal to the sample size. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramFiber` | `(X → ℕ) → Type (max 0 u_1)` | Given a finite count histogram, its histogram fibre is the set of ordered arrays whose length is the histogram total and whose histogram equals the given one. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramFiberFintype` | `(c : X → ℕ) → Fintype (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramFiber c)` | Given a finite count histogram, its histogram fibre has a finite enumeration. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramFiber_nonempty` | `Nonempty (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramFiber c)` | Every finite count histogram has at least one compatible ordering. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.retainedHistogramPrefix` | `n ≤ Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal c → Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramFiber c → Fin n → X` | Given a certificate that the requested length does not exceed the histogram total and a compatible ordering, the retained histogram prefix consists of the ordering's first requested entries. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairRetainedArrays` | `(Fin n → X) → (Fin n → Y) → Fin n → X × Y` | Given one retained array and another retained array, their coordinatewise pairing places the entries with each common index into a pair. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedHistogramAverage` | `((Fin n → X × Y) → ℝ) → (cX : X → ℕ) → (cY : Y → ℕ) → n ≤ Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal cX → n ≤ Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal cY → ℝ` | Given a paired-sample estimator, two finite count histograms, and certificates that both totals contain the requested sample length, the paired conditional histogram average independently averages the estimator over all compatible orderings, after retaining and coordinatewise pairing the two prefixes. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator` | `((Fin n → X × Y) → ℝ) → ℝ → (X → ℕ) × (Y → ℕ) → ℝ` | Given a paired-sample estimator, a fallback value, and two finite count histograms, the paired Poisson-histogram estimator uses the independent compatible-ordering average when both totals are large enough and returns the fallback when either total is too small. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator_of_totals_ge` | `Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator est fallback (cX, cY) = Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedHistogramAverage est cX cY hX hY` | Given a paired-sample estimator, a fallback value, two finite count histograms, and certificates that both totals contain the requested sample length, the paired count estimator equals the independent compatible-ordering average. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator_of_total_lt` | `Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal cX < n ∨ Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal cY < n → Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator est fallback (cX, cY) = fallback` | Given a paired-sample estimator, a fallback value, two finite count histograms, and a certificate that at least one total is too small, the paired count estimator equals its fallback. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.measurable_pairedPoissonHistogramEstimator` | `Measurable (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator est fallback)` | Given a paired-sample estimator and a fallback value, the resulting paired count estimator is measurable on finite measurable alphabets with measurable singletons. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.PairingLaw -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.measurable_pairRetainedArrays` | `Measurable fun z => Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairRetainedArrays z.1 z.2` | Pairing two finite arrays coordinatewise is measurable. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.map_pairRetainedArrays_prod_pi` | `MeasureTheory.Measure.map (fun z => Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairRetainedArrays z.1 z.2) ((MeasureTheory.Measure.pi fun x => P).prod (MeasureTheory.Measure.pi fun x => Q)) = MeasureTheory.Measure.pi fun x => P.prod Q` | Given one probability law and a second probability law, coordinatewise pairing sends two independent iid arrays to an iid array from the product law. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.FixedRisk -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedHistogramAverage_sq_sub_le` | `(Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedHistogramAverage est cX cY hX hY - theta) ^ 2 ≤ (∑ x, ∑ y, (est (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairRetainedArrays (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.retainedHistogramPrefix hX x) (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.retainedHistogramPrefix hY y)) - theta) ^ 2) / (↑(Fintype.card (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramFiber cX)) * ↑(Fintype.card (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramFiber cY)))` | Given a paired-sample estimator, a real target, two finite count histograms, and certificates that both totals contain the requested sample length, the squared loss of the independent two-fibre average is at most the uniform average squared loss over both ordering fibres. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedHistogramAverage_productRisk_le` | `∫ (z : (Fin NX → X) × (Fin NY → Y)), (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedHistogramAverage est (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram z.1) (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram z.2) (Eq.mpr (id (congrArg (LE.le n) (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal_finiteSampleHistogram z.1))) hX) (Eq.mpr (id (congrArg (LE.le n) (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal_finiteSampleHistogram z.2))) hY) - theta) ^ 2 ∂(MeasureTheory.Measure.pi fun x => P).prod (MeasureTheory.Measure.pi fun x => Q) ≤ ∫ (z : Fin n → X × Y), (est z - theta) ^ 2 ∂MeasureTheory.Measure.pi fun x => P.prod Q` | Given two finite-alphabet probability laws, a paired-sample estimator, a real target, and certificates that both fixed totals contain the requested sample length, independent histogram averaging followed by coordinatewise pairing has no greater squared risk than the paired iid experiment. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.Risk -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw` | `(P : MeasureTheory.Measure X) → [MeasureTheory.IsProbabilityMeasure P] → NNReal → MeasureTheory.Measure (X → ℕ)` | Given a finite-alphabet probability law and a Poisson intensity, the count-histogram law is the distribution of the unordered histogram of a finite Poisson sample. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.measurable_finiteSampleHistogram` | `Measurable fun s => Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram s.points` | The map from a finite sample to its histogram is measurable over a finite alphabet with measurable singletons. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw_map_histogramTotal` | `MeasureTheory.Measure.map Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.histogramTotal (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw P lam) = ProbabilityTheory.poissonMeasure lam` | Given a finite-alphabet probability law and a Poisson intensity, the total count under the histogram law has the scalar Poisson distribution with that intensity. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramRisk_le_fixedRisk_add_tails` | `MeasureTheory.Integrable (fun c => (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator est fallback c - theta) ^ 2) ((Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw P lamP).prod (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw Q lamQ)) ∧ ∫ (c : (X → ℕ) × (Y → ℕ)), (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator est fallback c - theta) ^ 2 ∂(Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw P lamP).prod (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw Q lamQ) ≤ (∫ (z : Fin n → X × Y), (est z - theta) ^ 2 ∂MeasureTheory.Measure.pi fun x => P.prod Q) + (fallback - theta) ^ 2 * ((ProbabilityTheory.poissonMeasure lamP).real {k \| k < n} + (ProbabilityTheory.poissonMeasure lamQ).real {k \| k < n})` | Given two finite-alphabet probability laws, their Poisson intensities, a paired fixed-sample estimator, a fallback value, and a real target, the paired histogram estimator has integrable squared loss and risk at most the paired fixed-sample risk plus the fallback loss times the sum of the two marginal lower-tail probabilities. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramRisk_two_n_le` | `\|theta\| ≤ B → ∫ (c : (X → ℕ) × (Y → ℕ)), (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator est 0 c - theta) ^ 2 ∂(Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw P (2 * ↑n)).prod (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw Q (2 * ↑n)) ≤ (∫ (z : Fin n → X × Y), (est z - theta) ^ 2 ∂MeasureTheory.Measure.pi fun x => P.prod Q) + B ^ 2 * (ProbabilityTheory.poissonMeasure (2 * ↑n)).real {k \| k < n} * 2` | Given two finite-alphabet probability laws, a paired fixed-sample estimator, a real target, a target-magnitude bound, and a certificate of that bound, using zero fallback and Poisson means twice the sample size gives a risk penalty no larger than twice the squared bound times the common Poisson lower-tail probability. |
| `Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramRisk_two_n_exp_le` | `\|theta\| ≤ B → ∫ (c : (X → ℕ) × (Y → ℕ)), (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.pairedPoissonHistogramEstimator est 0 c - theta) ^ 2 ∂(Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw P (2 * ↑n)).prod (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.countLaw Q (2 * ↑n)) ≤ (∫ (z : Fin n → X × Y), (est z - theta) ^ 2 ∂MeasureTheory.Measure.pi fun x => P.prod Q) + B ^ 2 * Real.exp (-↑n * (1 - Real.log 2)) * 2` | Given two finite-alphabet probability laws, a paired fixed-sample estimator, a real target, a target-magnitude bound, and a certificate of that bound, using zero fallback and Poisson means twice the sample size gives the explicit exponential risk penalty supplied by the Poisson lower-tail inequality. |
<!-- /GEN -->

### Finite-moment perturbations of the standard Gaussian

This moment-problem substrate constructs non-Gaussian laws that are arbitrarily close
to the standard Gaussian in testing total variation yet agree with it on any requested
finite initial segment of raw moments and cumulants.  The construction uses a bounded
Gaussian-orthogonal density profile, and its Gaussian-tail domination supplies both all
absolute moments and the explicit Hamburger--Carleman divergence certificate.

<!-- GEN:Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.Basic -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.MomentProblems.rawMoment` | `MeasureTheory.Measure ℝ → ℕ → ℝ` | Given a real measure and a nonnegative integer order, the raw moment is given by integrating the corresponding power. |
| `Stat.MomentProblems.rawMoment_eq_integral` | `Causalean.Stat.MomentProblems.rawMoment ν k = ∫ (x : ℝ), x ^ k ∂ν` | For a real measure at a nonnegative integer order, the raw-moment notation equals the integral of the corresponding power. |
| `Stat.MomentProblems.totalVariationDistance` | `MeasureTheory.Measure α → MeasureTheory.Measure α → ℝ` | Given two measures on the same measurable outcome space, the testing total-variation distance is given by the supremum of their absolute probability gaps over measurable events. |
| `Stat.MomentProblems.totalVariationDistance_eq_tvDist` | `Causalean.Stat.MomentProblems.totalVariationDistance P Q = Causalean.Stat.tvDist P Q` | For two probability measures on the same measurable outcome space, the set-supremum testing distance equals the library's indexed total-variation distance. |
| `Stat.MomentProblems.hamburgerCarlemanSeries` | `MeasureTheory.Measure ℝ → ENNReal` | Given a real measure, the explicit Hamburger--Carleman series is given by the sum of inverse roots of its positive even raw moments. |
| `Stat.MomentProblems.hamburgerCarlemanSeries_eq` | `Causalean.Stat.MomentProblems.hamburgerCarlemanSeries ν = ∑' (s : ℕ), (ENNReal.ofReal \|∫ (x : ℝ), x ^ (2 * (s + 1)) ∂ν\|).rpow (-1 / (2 * (↑s + 1)))` | For a real measure, the Hamburger--Carleman notation equals its explicit integral-series formula. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.OrthogonalPerturbation -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.MomentProblems.exists_bounded_gaussian_orthogonal_perturbation` | `∃ h, Measurable h ∧ (∀ (x : ℝ), \|h x\| ≤ 1) ∧ 0 < ∫ (x : ℝ), \|h x\| ∂ProbabilityTheory.gaussianReal 0 1 ∧ ∀ k ≤ K, MeasureTheory.Integrable (fun x => x ^ k * h x) (ProbabilityTheory.gaussianReal 0 1) ∧ ∫ (x : ℝ), x ^ k * h x ∂ProbabilityTheory.gaussianReal 0 1 = 0` | For a finite degree cutoff, there is a measurable profile bounded by one, nonzero under the standard Gaussian law, and orthogonal to every monomial through that cutoff. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.DensityPerturbation -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.MomentProblems.gaussianPerturbation` | `(ℝ → ℝ) → ℝ → MeasureTheory.Measure ℝ` | Given a signed profile and a real amplitude, the Gaussian density perturbation is given by weighting the standard Gaussian law by one plus the scaled profile. |
| `Stat.MomentProblems.gaussianPerturbation_spec` | `Measurable h → (∀ (x : ℝ), \|h x\| ≤ 1) → 0 < ∫ (x : ℝ), \|h x\| ∂ProbabilityTheory.gaussianReal 0 1 → (∀ k ≤ K, MeasureTheory.Integrable (fun x => x ^ k * h x) (ProbabilityTheory.gaussianReal 0 1) ∧ ∫ (x : ℝ), x ^ k * h x ∂ProbabilityTheory.gaussianReal 0 1 = 0) → 0 < ε → ε < 1 → ε < rho → have F := Causalean.Stat.MomentProblems.gaussianPerturbation h ε; MeasureTheory.IsProbabilityMeasure F ∧ F ≠ ProbabilityTheory.gaussianReal 0 1 ∧ Causalean.Stat.MomentProblems.totalVariationDistance F (ProbabilityTheory.gaussianReal 0 1) < rho ∧ (∀ k ≤ K, Causalean.Stat.MomentProblems.rawMoment F k = Causalean.Stat.MomentProblems.rawMoment (ProbabilityTheory.gaussianReal 0 1) k) ∧ (∀ (k : ℕ), MeasureTheory.Integrable (fun x => \|x\| ^ k) F) ∧ ∀ (n : ℕ), 0 < n → \|Causalean.Stat.MomentProblems.rawMoment F (2 * n)\| ≤ 2 * (2 * ↑n) ^ n` | If a profile is measurable, bounded by one, nonzero under the standard Gaussian law, and orthogonal to the required monomials, while its amplitude is positive, below one, and below the requested distance radius, then the resulting density perturbation is a distinct nearby probability law with the specified raw moments, all absolute moments, and a Gaussian-scale even-moment bound. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.Carleman -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.MomentProblems.hamburgerCarlemanSeries_eq_top_of_evenMoment_le` | `(∀ (n : ℕ), 0 < n → \|Causalean.Stat.MomentProblems.rawMoment ν (2 * n)\| ≤ 2 * (2 * ↑n) ^ n) → Causalean.Stat.MomentProblems.hamburgerCarlemanSeries ν = ⊤` | If a real measure has positive even raw moments bounded at the Gaussian scale, then its explicit Hamburger--Carleman series diverges. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.CumulantTransfer -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.MomentProblems.cumFromMom_congr_up_to` | `(∀ j ≤ K, m₁ j = m₂ j) → k ≤ K → Causalean.Stat.MomentProblems.cumFromMom k m₁ = Causalean.Stat.MomentProblems.cumFromMom k m₂` | When two abstract moment sequences agree through a cutoff and the requested cumulant order lies below that cutoff, their combinatorial cumulants at that order agree. |
| `Stat.MomentProblems.sourceCumulant_eq_of_rawMoment_eq_up_to` | `(∀ j ≤ K, Causalean.Stat.MomentProblems.rawMoment μ j = Causalean.Stat.MomentProblems.rawMoment ν j) → ∀ k ≤ K, Causalean.Stat.MomentProblems.sourceCumulant μ id k = Causalean.Stat.MomentProblems.sourceCumulant ν id k` | Given two real measures, a finite cutoff, and equality of their raw moments through that cutoff, the source cumulants of the identity statistic agree at every order through the cutoff. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.Main -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.MomentProblems.exists_finiteMoment_near_gaussian_perturbation` | `3 ≤ K → 0 < rho → ∃ F, MeasureTheory.IsProbabilityMeasure F ∧ ∫ (x : ℝ), x ∂F = 0 ∧ ProbabilityTheory.variance id F = 1 ∧ ¬Causalean.Stat.MomentProblems.IsGaussianLaw F ∧ Causalean.Stat.MomentProblems.totalVariationDistance F (ProbabilityTheory.gaussianReal 0 1) < rho ∧ (∀ k ≤ K, ∫ (x : ℝ), x ^ k ∂F = ∫ (x : ℝ), x ^ k ∂ProbabilityTheory.gaussianReal 0 1) ∧ (∀ (k : ℕ), MeasureTheory.Integrable (fun x => \|x\| ^ k) F) ∧ ∑' (s : ℕ), (ENNReal.ofReal \|∫ (x : ℝ), x ^ (2 * (s + 1)) ∂F\|).rpow (-1 / (2 * (↑s + 1))) = ⊤ ∧ ∀ k ≤ K, Causalean.Stat.MomentProblems.sourceCumulant F id k = Causalean.Stat.MomentProblems.sourceCumulant (ProbabilityTheory.gaussianReal 0 1) id k` | Given a finite moment cutoff of at least three and a strictly positive testing-distance radius, there is a non-Gaussian probability law within that radius of the standard Gaussian, with matching raw moments and source cumulants through the cutoff, all absolute moments, and a divergent Hamburger--Carleman series. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Minimax.MaximalCoupling -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.measurableEqOfStandardBorel` | `MeasurableEq X` | For a standard Borel measurable space, the measurability of its equality relation is defined. |
| `Stat.tvDist_eq_half_integral_abs_rnDeriv_sub` | `mu.AbsolutelyContinuous xi → nu.AbsolutelyContinuous xi → Causalean.Stat.tvDist mu nu = 1 / 2 * ∫ (x : X), \|(mu.rnDeriv xi x).toReal - (nu.rnDeriv xi x).toReal\| ∂xi` | Scheffé's identity with both probability laws dominated by an arbitrary finite reference measure. |
| `Stat.rnCommonPart` | `MeasureTheory.Measure X → MeasureTheory.Measure X → MeasureTheory.Measure X → MeasureTheory.Measure X` | Given a measurable sample space and three measures on it, consisting of two target measures and a reference measure, the common Radon--Nikodym submeasure is the reference measure weighted by the pointwise minimum of the two target measures' Radon--Nikodym densities relative to that reference measure. |
| `Stat.rnCommonPart_le_left` | `mu.AbsolutelyContinuous xi → Causalean.Stat.rnCommonPart mu nu xi ≤ mu` | The RN common part is dominated by its first law. |
| `Stat.rnCommonPart_le_right` | `nu.AbsolutelyContinuous xi → Causalean.Stat.rnCommonPart mu nu xi ≤ nu` | The RN common part is dominated by its second law. |
| `Stat.rnCommonPart_mass_eq_one_sub_tvDist` | `mu.AbsolutelyContinuous xi → nu.AbsolutelyContinuous xi → (Causalean.Stat.rnCommonPart mu nu xi) Set.univ = ENNReal.ofReal (1 - Causalean.Stat.tvDist mu nu)` | The mass of the RN common part is exactly one minus total variation. |
| `Stat.measure_eq_of_tvDist_eq_zero` | `Causalean.Stat.tvDist mu nu = 0 → mu = nu` | Probability measures at total-variation distance zero are equal. |
| `Stat.maximalCoupling` | `(mu nu : MeasureTheory.Measure X) → [MeasureTheory.IsProbabilityMeasure mu] → [MeasureTheory.IsProbabilityMeasure nu] → MeasureTheory.Measure (X × X)` | Given a measurable sample space and two probability measures on it, the maximal coupling is the measure on pairs whose first branch is the diagonal coupling when their total-variation distance is zero, and whose second branch otherwise combines their common part on the diagonal with the normalized product of their residual measures. |
| `Stat.maximalCoupling_map_fst` | `MeasureTheory.Measure.map Prod.fst (Causalean.Stat.maximalCoupling mu nu) = mu` | The first marginal of the maximal coupling is the first law. |
| `Stat.maximalCoupling_map_snd` | `MeasureTheory.Measure.map Prod.snd (Causalean.Stat.maximalCoupling mu nu) = nu` | The second marginal of the maximal coupling is the second law. |
| `Stat.maximalCoupling.instIsProbabilityMeasure` | `MeasureTheory.IsProbabilityMeasure (Causalean.Stat.maximalCoupling mu nu)` | — |
| `Stat.maximalCoupling_eq_mass_ge` | `ENNReal.ofReal (1 - Causalean.Stat.tvDist mu nu) ≤ (Causalean.Stat.maximalCoupling mu nu) {p \| p.1 = p.2}` | For two probability measures `mu` and `nu` on a standard Borel space `X`, the two coordinates of their maximal coupling agree with probability at least one minus their total variation distance. |
| `Stat.compressionCoupling` | `(Q0 Q1 : MeasureTheory.Measure Z) → [MeasureTheory.IsProbabilityMeasure Q0] → [MeasureTheory.IsProbabilityMeasure Q1] → (compress : Z → S) → Measurable compress → MeasureTheory.Measure (Z × Z)` | Given two standard Borel measurable spaces, an observation space and a compressed-state space, two probability measures on the observation space, and a measurable compression map from observations to compressed states, the compression coupling is the joint law obtained by maximally coupling the two compressed laws and then, conditional on each coupled compressed state, drawing each observation from its corresponding regular conditional distribution. |
| `Stat.compressionCoupling_map_fst` | `MeasureTheory.Measure.map Prod.fst (Causalean.Stat.compressionCoupling Q0 Q1 compress hcompress) = Q0` | The first marginal of the lifted compression coupling is the first raw law. |
| `Stat.compressionCoupling_map_snd` | `MeasureTheory.Measure.map Prod.snd (Causalean.Stat.compressionCoupling Q0 Q1 compress hcompress) = Q1` | The second marginal of the lifted compression coupling is the second raw law. |
| `Stat.compressionCoupling_map_compress_pair` | `MeasureTheory.Measure.map (Prod.map compress compress) (Causalean.Stat.compressionCoupling Q0 Q1 compress hcompress) = Causalean.Stat.maximalCoupling (MeasureTheory.Measure.map compress Q0) (MeasureTheory.Measure.map compress Q1)` | Compressing both coordinates of the lifted coupling recovers the maximal coupling of the compressed laws. |
| `Stat.compressionCoupling.instIsProbabilityMeasure` | `MeasureTheory.IsProbabilityMeasure (Causalean.Stat.compressionCoupling Q0 Q1 compress hcompress)` | — |
| `Stat.compressionCoupling_equal_compression_mass_ge` | `ENNReal.ofReal (1 - Causalean.Stat.tvDist (MeasureTheory.Measure.map compress Q0) (MeasureTheory.Measure.map compress Q1)) ≤ (Causalean.Stat.compressionCoupling Q0 Q1 compress hcompress) {p \| compress p.1 = compress p.2}` | In the lifted coupling, the compressed observations agree with probability at least one minus the total variation of their compressed laws. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Minimax.CoordinatewiseOverlap -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.compressedCoordinateLaw` | `(Z → S) → MeasureTheory.Measure Z → MeasureTheory.Measure S` | For a compression from a measurable observation space to a measurable summary space and a measure on the observation space, the compressed-coordinate law is the image measure of the summary obtained by applying the compression to an observation governed by that measure. |
| `Stat.compressedCoordinateLaw_klDiv_le` | `Measurable compress → ∀ (μ ν : MeasureTheory.Measure Z) [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν], InformationTheory.klDiv (Causalean.Stat.compressedCoordinateLaw compress μ) (Causalean.Stat.compressedCoordinateLaw compress ν) ≤ InformationTheory.klDiv μ ν` | Measurable finite-coordinate compression cannot increase KL divergence. |
| `Stat.coordinatewiseSuccessProbability` | `(Q : (j : Fin M) → Bool → MeasureTheory.Measure (Z j)) → (R : MeasureTheory.Measure A) → [∀ (j : Fin M) (b : Bool), MeasureTheory.IsProbabilityMeasure (Q j b)] → [MeasureTheory.IsProbabilityMeasure R] → ((j : Fin M) → Z j → S j) → ((j : Fin M) → S j → ((k : Fin M) → Z k) → A → Bool) → ENNReal` | For a nonnegative number of coordinates, measurable raw-observation and summary spaces at every coordinate, a measurable ancillary space, two probability laws for each coordinate, indexed by its binary state, a probability law for a common ancillary variable, one compression for each coordinate, and a decoder for each coordinate that uses its compressed observation, the full raw observation vector, and the ancillary variable, the coordinatewise success probability is the average, over all binary state vectors, of the probability that every decoder recovers its corresponding state under the associated independent product experiment. |
| `Stat.coordinateOverlap` | `((j : Fin M) → Bool → MeasureTheory.Measure (Z j)) → ((j : Fin M) → Z j → S j) → Fin M → ℝ` | For two probability laws at each coordinate, indexed by its binary state, a compression at each coordinate, and one coordinate, the common-part overlap at that coordinate is one minus the total-variation distance between the two compressed laws of that coordinate. |
| `Stat.selectCoupledRaw` | `(Fin M → Bool) → ((j : Fin M) → Z j × Z j) → (j : Fin M) → Z j` | For a binary hypercube vertex and a pair of raw observations at every coordinate, the selected raw observation vector takes the first member of each pair when the corresponding vertex bit is false and the second member when it is true. |
| `Stat.coupledDecoderGood` | `((j : Fin M) → Z j → S j) → ((j : Fin M) → S j → ((k : Fin M) → Z k) → A → Bool) → (Fin M → Bool) → ((j : Fin M) → Z j × Z j) → A → Prop` | For a nonnegative number of coordinates, one compression for each coordinate, one decoder for each coordinate, a binary hypercube vertex, a pair of raw observations at every coordinate, and an ancillary-variable value, the coupled decoder-good condition holds exactly when every decoder, applied to its compressed selected observation together with the full selected raw vector and the ancillary value, returns its corresponding vertex bit. |
| `Stat.coupledGoodIndicator` | `((j : Fin M) → Z j → S j) → ((j : Fin M) → S j → ((k : Fin M) → Z k) → A → Bool) → (Fin M → Bool) → ((j : Fin M) → Z j × Z j) → A → ENNReal` | For a nonnegative number of coordinates, one compression for each coordinate, one decoder for each coordinate, a binary hypercube vertex, a pair of raw observations at every coordinate, and an ancillary-variable value, the coupled decoder-good condition holds exactly when every decoder, applied to its compressed selected observation together with the full selected raw vector and the ancillary value, returns its corresponding vertex bit. |
| `Stat.coupledDecoderGood_flip_exclusive` | `(∀ (j : Fin M) (s : S j) (z z' : (k : Fin M) → Z k) (a : A), (∀ (k : Fin M), k ≠ j → z k = z' k) → decoder j s z a = decoder j s z' a) → ∀ (omega : Fin M → Bool) (z : (j : Fin M) → Z j × Z j) (a : A) (j : Fin M), compress j (z j).1 = compress j (z j).2 → ¬(Causalean.Stat.coupledDecoderGood compress decoder omega z a ∧ Causalean.Stat.coupledDecoderGood compress decoder (Causalean.Stat.flipBit j omega) z a)` | If the two compressed versions agree at coordinate `j`, simultaneous correctness is impossible at both endpoints of the corresponding cube edge. |
| `Stat.coupledDecoderGood_count_le_half` | `(∀ (j : Fin M) (s : S j) (z z' : (k : Fin M) → Z k) (a : A), (∀ (k : Fin M), k ≠ j → z k = z' k) → decoder j s z a = decoder j s z' a) → ∀ (z : (j : Fin M) → Z j × Z j) (a : A) (j : Fin M), compress j (z j).1 = compress j (z j).2 → ∑ omega, Causalean.Stat.coupledGoodIndicator compress decoder omega z a ≤ 2 ^ M / 2` | Once one coupled coordinate has equal compressions, at most half of the hypercube vertices can be simultaneously decoded correctly. |
| `Stat.half_integral_abs_rnDeriv_sub_le_tvDist` | `μ.AbsolutelyContinuous ξ → ν.AbsolutelyContinuous ξ → 1 / 2 * ∫ (x : Ω), \|(μ.rnDeriv ξ x).toReal - (ν.rnDeriv ξ x).toReal\| ∂ξ ≤ Causalean.Stat.tvDist μ ν` | For two probability measures dominated by a common finite measure, half the `L¹` distance between their Radon--Nikodym densities is bounded by total variation. This is the reverse Scheffé inequality needed to construct the common submeasure in the maximal-coupling argument. |
| `Stat.overlap_ge_exp_neg_klBudget` | `0 ≤ B → InformationTheory.klDiv μ ν ≤ ENNReal.ofReal B → 1 / 2 * Real.exp (-B) ≤ 1 - Causalean.Stat.tvDist μ ν` | A nonnegative finite KL budget yields the corresponding Bretagnolle--Huber lower bound on testing overlap. |
| `Stat.prod_one_sub_le_exp_neg_sum` | `(∀ (j : Fin M), ρ j ≤ 1) → ∏ j, (1 - ρ j) ≤ Real.exp (-∑ j, ρ j)` | A product of complementary overlap probabilities is bounded by the exponential of minus their sum. |
| `Stat.prod_one_sub_le_exp_neg_card_mul` | `(∀ (j : Fin M), ρ j ≤ 1) → (∀ (j : Fin M), c ≤ ρ j) → ∏ j, (1 - ρ j) ≤ Real.exp (-↑M * c)` | A common coordinatewise overlap floor `c` bounds the complementary product by `exp (-M * c)`. |
| `Stat.tvDist_eq_zero_of_klBudget_nonpos` | `B ≤ 0 → InformationTheory.klDiv μ ν ≤ ENNReal.ofReal B → Causalean.Stat.tvDist μ ν = 0` | A nonpositive real KL budget forces two probability measures to coincide, and hence forces their total variation distance to vanish. |
| `Stat.card_mul_exp_neg_log_eq_rpow` | `1 ≤ M → ∀ (κ : ℝ), ↑M * (1 / 2 * Real.exp (-(κ * Real.log ↑M))) = ↑M ^ (1 - κ) / 2` | The exponential KL-overlap floor has the expected power-law scaling after multiplication by the number of coordinates. |
| `Stat.coordinateOverlap_product_le_of_nonnegative_kl` | `1 ≤ M → ∀ {Z : Fin M → Type u_1} {S : Fin M → Type u_2} [inst : (j : Fin M) → MeasurableSpace (Z j)] [inst_1 : (j : Fin M) → MeasurableSpace (S j)] (Q : (j : Fin M) → Bool → MeasureTheory.Measure (Z j)) [∀ (j : Fin M) (b : Bool), MeasureTheory.IsProbabilityMeasure (Q j b)] (compress : (j : Fin M) → Z j → S j), (∀ (j : Fin M), Measurable (compress j)) → ∀ {κ : ℝ}, 0 ≤ κ → (∀ (j : Fin M), InformationTheory.klDiv (Causalean.Stat.compressedCoordinateLaw (compress j) (Q j false)) (Causalean.Stat.compressedCoordinateLaw (compress j) (Q j true)) ≤ ENNReal.ofReal (κ * Real.log ↑M)) → ∏ j, (1 - Causalean.Stat.coordinateOverlap Q compress j) ≤ Real.exp (-↑M ^ (1 - κ) / 2)` | Under a nonnegative logarithmic KL budget, the product of coordinatewise total-variation factors has the finite-`M` exponential bound. |
| `Stat.ennreal_error_lower_bound_of_success_upper_bound` | `0 ≤ p → e ≤ 1 → p ≤ e → s ≤ ENNReal.ofReal (1 / 2 * (1 + p)) → ENNReal.ofReal (1 / 2 * (1 - e)) ≤ 1 - s` | A real-valued product bound below one converts an ENNReal simultaneous success upper bound into the complementary error lower bound. |
| `Stat.coordinatewise_overlap_direct_product` | `1 ≤ M → ∀ {Z : Fin M → Type u_1} {S : Fin M → Type u_2} {A : Type u_3} [inst : (j : Fin M) → MeasurableSpace (Z j)] [∀ (j : Fin M), StandardBorelSpace (Z j)] [inst_2 : (j : Fin M) → MeasurableSpace (S j)] [∀ (j : Fin M), StandardBorelSpace (S j)] [inst_4 : MeasurableSpace A] [StandardBorelSpace A] (Q : (j : Fin M) → Bool → MeasureTheory.Measure (Z j)) (R : MeasureTheory.Measure A) [inst_6 : ∀ (j : Fin M) (b : Bool), MeasureTheory.IsProbabilityMeasure (Q j b)] [inst_7 : MeasureTheory.IsProbabilityMeasure R] (compress : (j : Fin M) → Z j → S j), (∀ (j : Fin M), Measurable (compress j)) → ∀ (decoder : (j : Fin M) → S j → ((k : Fin M) → Z k) → A → Bool), (∀ (j : Fin M), Measurable fun p => decoder j p.1 p.2.1 p.2.2) → (∀ (j : Fin M) (s : S j) (z z' : (k : Fin M) → Z k) (a : A), (∀ (k : Fin M), k ≠ j → z k = z' k) → decoder j s z a = decoder j s z' a) → Causalean.Stat.coordinatewiseSuccessProbability Q R compress decoder ≤ ENNReal.ofReal (1 / 2 * (1 + ∏ j, (1 - Causalean.Stat.coordinateOverlap Q compress j))) ∧ ∀ κ < 1, (∀ (j : Fin M), InformationTheory.klDiv (Causalean.Stat.compressedCoordinateLaw (compress j) (Q j false)) (Causalean.Stat.compressedCoordinateLaw (compress j) (Q j true)) ≤ ENNReal.ofReal (κ * Real.log ↑M)) → ENNReal.ofReal (1 / 2 * (1 - Real.exp (-↑M ^ (1 - κ) / 2))) ≤ 1 - Causalean.Stat.coordinatewiseSuccessProbability Q R compress decoder` | Coordinatewise-overlap direct-product bound. In a conditionally independent hypercube experiment with at least one coordinate, per-coordinate candidate laws `Q j`, indexed by a bit, a per-coordinate compression map `compress` that is measurable at every coordinate, and per-coordinate decoders `decoder` built from the compressed local summary, the other coordinates' raw data, and shared randomness that are jointly measurable and depend on the raw sample at coordinate `j` only through its compressed summary, not directly on the raw value at `j`, then decentralized coordinate decoders cannot on average be correct more often than the common-part product bound built from the per-coordinate total-variation overlaps; and if every compressed adjacent KL divergence is at most `κ log M`, the displayed finite-`M` simultaneous-error certificate follows. |
| `Stat.coordinatewise_overlap_direct_product_asymptotic` | `∀ κ < 1, Filter.Tendsto Mseq Filter.atTop Filter.atTop → Filter.Tendsto (fun n => 1 / 2 * (1 - Real.exp (-↑(Mseq n) ^ (1 - κ) / 2))) Filter.atTop (nhds (1 / 2))` | Along any sequence `M_n → ∞` and for fixed `κ < 1`, the finite direct-product certificate tends to one half. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSampleMap` | `(X → Y) → Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X → Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample Y` | Given a map from one observation space to another and a finite sample in the first space, the mapped finite sample has the same size and applies the map to every observation. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.measurable_finiteSampleMap` | `Measurable f → Measurable (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSampleMap f)` | Pointwise mapping of dependent finite samples is measurable. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSampleMap_fixedSizeEmbed` | `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSampleMap f (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed n x) = Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed n fun i => f (x i)` | Mapping commutes with fixed-size embedding. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.cellObservationLaw_eq_of_restrict_eq` | `μ (p.cellSet j) ≠ 0 → μ (p.cellSet j) = ν (p.cellSet j) → μ.restrict (p.cellSet j) = ν.restrict (p.cellSet j) → p.cellObservationLaw μ j = p.cellObservationLaw ν j` | Equal restrictions and equal cell masses give equal normalized cell laws. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.markedPoissonKL_le_two_mul_of_piKL` | `1 ≤ n → ∀ {B : ℝ}, 0 ≤ B → InformationTheory.klDiv (MeasureTheory.Measure.pi fun x => P) (MeasureTheory.Measure.pi fun x => Q) ≤ ENNReal.ofReal B → InformationTheory.klDiv (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteMeasureMarkedPoissonLaw P P R (2 * ↑n)) (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteMeasureMarkedPoissonLaw Q P R (2 * ↑n)) ≤ ENNReal.ofReal (2 * B)` | Consider a sample size `n` that is at least `1` and a nonnegative KL budget `B`, and suppose the KL divergence between `n` independent identically distributed draws from `P` and from `Q` is at most `B`. Then the KL divergence between the marked Poisson experiments with mean count `2n`, mark law `R`, and intensity measures `P` and `Q` respectively (both built over the same baseline `P`) is at most `2B`. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.canonicalPrefixObservations` | `X → (n : ℕ) → Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample (X × ℝ) → Fin n → X` | Given a fallback observation, a nonnegative integer prefix length, and a finite sample of observation--real-mark pairs, the canonical prefix observations are the first $n$ observations when the sample has at least $n$ pairs, and otherwise are the constant $n$-tuple of the fallback observation. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.measurable_canonicalPrefixObservations` | `Measurable (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.canonicalPrefixObservations x₀ n)` | Reading a fixed prefix from a canonical finite configuration is measurable. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.map_canonicalPrefixObservations_restrict_count_ge` | `MeasureTheory.Measure.map (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.canonicalPrefixObservations x₀ n) ((Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.canonicalMarkedPoissonSampleLaw P R lam).restrict (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample.count ⁻¹' Set.Ici n)) = (ProbabilityTheory.poissonMeasure lam) (Set.Ici n) • MeasureTheory.Measure.pi fun x => P` | On the successful-count event, the canonical marked-Poisson configuration's first `n` observations have the unnormalised product law. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.poisson_two_n_lower_tail` | `(ProbabilityTheory.poissonMeasure (2 * ↑n)) {k \| k < n} ≤ ENNReal.ofReal (Real.exp (-↑n * (1 - Real.log 2)))` | The lower tail used in de-Poissonization is exponentially small. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSamplePaddedStream` | `X → Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X → ℕ × (ℕ → X)` | Given a fallback observation and a finite sample, the padded stream representation is the pair consisting of its size and an infinite stream that agrees with the sample at positions below that size and equals the fallback observation thereafter. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSamplePaddedStream_measurable` | `Measurable (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSamplePaddedStream x0)` | — |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.streamToFiniteSample_paddedStream` | `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.streamToFiniteSample (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSamplePaddedStream x0 s) = s` | — |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSamplePaddedStream_range` | `Set.range (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSamplePaddedStream x0) = {z \| ∀ (k : ℕ), z.1 ≤ k → z.2 k = x0}` | — |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.finiteSample_standardBorelSpace` | `StandardBorelSpace (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X)` | For every nonempty standard Borel observation space equipped with its measurable structure, the space of finite samples from that observation space is a standard Borel space. |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.canonicalMarkedPoissonSampleLaw_map_count` | `MeasureTheory.Measure.map Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample.count (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.canonicalMarkedPoissonSampleLaw P R lam) = ProbabilityTheory.poissonMeasure lam` | — |
| `Mathlib.Probability.FiniteMarkedPoissonPartition.finiteMeasureMarkedPoissonLaw_probability_eq` | `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteMeasureMarkedPoissonLaw P P0 R lam = Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finiteMarkedPoissonSampleLaw P R lam` | When the intensity measure is already a probability law, the finite-measure Poisson wrapper agrees with the ordinary marked-Poisson sample law. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.MeasureTheory.AnalyticSetUniversalMeasurability.UpperSemianalytic -->
| Decl | Signature | Description |
|---|---|---|
| `MeasureTheory.outerLIntegral` | `MeasureTheory.Measure Ω → (Ω → ENNReal) → ENNReal` | The outer integral of an extended-nonnegative-valued function on a measurable sample space, under a measure on that sample space, is the infimum of the lower Lebesgue integrals of all measurable functions that dominate the given function pointwise. |
| `MeasureTheory.outerLIntegral_mono` | `f ≤ g → MeasureTheory.outerLIntegral μ f ≤ MeasureTheory.outerLIntegral μ g` | Outer integration is monotone in its extended-nonnegative integrand. |
| `MeasureTheory.lintegral_le_outerLIntegral` | `∫⁻ (ω : Ω), f ω ∂μ ≤ MeasureTheory.outerLIntegral μ f` | The lower Lebesgue integral is bounded by the outer integral. |
| `MeasureTheory.lintegral_le_outerLIntegral_of_measurable_le` | `f ≤ g → ∫⁻ (ω : Ω), f ω ∂μ ≤ MeasureTheory.outerLIntegral μ g` | A pointwise lower bound may be integrated before comparison with an outer integral, without measurability of either function. |
| `MeasureTheory.outerLIntegral_eq_lintegral_of_measurable` | `Measurable f → MeasureTheory.outerLIntegral μ f = ∫⁻ (ω : Ω), f ω ∂μ` | Outer integration agrees with Lebesgue integration for measurable functions. |
| `MeasureTheory.lintegral_le_lintegral_completion` | `∫⁻ (ω : Ω), f ω ∂μ ≤ ∫⁻ (ω : MeasureTheory.NullMeasurableSpace Ω μ), f ω ∂μ.completion` | Completing a measure can only increase the lower integral of an arbitrary extended-nonnegative function. |
| `MeasureTheory.lintegral_completion_eq_of_measurable` | `Measurable f → ∫⁻ (ω : MeasureTheory.NullMeasurableSpace Ω μ), f ω ∂μ.completion = ∫⁻ (ω : Ω), f ω ∂μ` | A measurable extended-nonnegative function has the same integral before and after completion of the measure. |
| `MeasureTheory.UpperSemianalytic` | `(Ω → ENNReal) → Prop` | An extended-nonnegative-valued function on a topological sample space is upper-semi-analytic exactly when, for every extended-nonnegative threshold $a$, the set of sample points at which its value is strictly greater than $a$ is analytic. |
| `MeasureTheory.UpperSemianalytic.nullMeasurable` | `MeasureTheory.UpperSemianalytic f → ∀ (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ], MeasureTheory.NullMeasurable f μ` | An upper-semi-analytic extended-nonnegative function is null-measurable for every finite Borel measure. |
| `MeasureTheory.UpperSemianalytic.measurable_completion` | `MeasureTheory.UpperSemianalytic f → ∀ (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ], Measurable f` | An upper-semi-analytic extended-nonnegative loss is measurable once a finite Borel sampling measure is completed, so it is available to ordinary completed-measure integration. |
| `MeasureTheory.UpperSemianalytic.lintegral_completion_eq_outerLIntegral` | `MeasureTheory.UpperSemianalytic f → ∀ (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ], ∫⁻ (ω : MeasureTheory.NullMeasurableSpace Ω μ), f ω ∂μ.completion = MeasureTheory.outerLIntegral μ f` | On a Polish sample space equipped with its Borel σ-algebra and a finite measure `μ`, if `f` is upper-semi-analytic — every strict superlevel set `{ω \| a < f ω}` is analytic, then the lower Lebesgue integral of `f` against the completion of `μ` equals the outer integral of `f` with respect to `μ`, i.e. the infimum of the lower integrals of all measurable pointwise majorants of `f`. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.Separability -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.Concentration.centeredEmpiricalAverage` | `MeasureTheory.Measure Ω → {n : ℕ} → (Fin n → Ω) → (Ω → ℝ) → ℝ` | Given a measure $\mu$ on an observation space, a sample of $n$ observations, and a real-valued function, the centered empirical average is its sample average minus its integral with respect to $\mu$. |
| `Stat.Concentration.HasCountableEmpiricalSupReduction` | `MeasureTheory.Measure Ω → (ι → Ω → ℝ) → Prop` | Given a measure $\mu$ on an observation space and a family of real-valued functions indexed by a set $\iota$, the countable empirical-supremum reduction property holds exactly when every member of the family is measurable and there is a sequence of indices whose associated countable subfamily has, for every sample size, the same supremum of absolute centered empirical averages as the full family almost surely under the corresponding product measure. |
| `Stat.Concentration.hasCountableEmpiricalSupReduction_of_pointwise_dense` | `(∀ᵐ (z : Ω) ∂μ, z ∈ S) → (∀ (i : ι), ∃ kseq, ∀ z ∈ S, Filter.Tendsto (fun m => g (g0 (kseq m)) z) Filter.atTop (nhds (g i z))) → (∀ (i : ι), Measurable (g i)) → (∃ G, MeasureTheory.Integrable G μ ∧ ∀ (i : ι) (z : Ω), \|g i z\| ≤ G z) → Causalean.Stat.Concentration.HasCountableEmpiricalSupReduction μ g` | Countable supremum reduction from pointwise density. Let `μ` be a σ-finite measure on `Ω`, `g : ι → Ω → ℝ` a family of functions, and `g0 : ℕ → ι` a countable subfamily. Suppose `S` is a `μ`-conull subset of `Ω`, on `S`, every `g i` is the pointwise limit, along some subsequence, of the countable subfamily `g ∘ g0`, each `g i` is measurable, and there is a single `μ`-integrable envelope `G` dominating `\|g i\|` uniformly in `i`. Then the countable subfamily indexed by `g0` realizes the full continuum empirical-process supremum of `g` almost surely under every finite product law of `μ`. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.EntropyChaining -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.Concentration.HasVCUniformEntropy` | `MeasureTheory.Measure Ω → (ι → Ω → ℝ) → ℝ → ℝ → ℝ → ℝ → Prop` | For a measure on a measurable sample space, a class of real-valued functions indexed by a set, an envelope bound, a radius, a covering constant, and an entropy exponent, the class has uniform VC-type entropy exactly when (1) the radius is positive, (2) the radius is strictly smaller than the envelope bound, (3) the covering constant is at least $e$, (4) the entropy exponent is at least one, (5) every function in the class is measurable, (6) every function is bounded in absolute value by the envelope bound at every sample point, (7) every function has population $L^2$ distance at most the radius from the zero function, and (8) every countable enumeration of the class has the stipulated polynomial empirical $L^2$ covering property. |
| `Stat.Concentration.countableEmpiricalProcessSup` | `MeasureTheory.Measure Ω → (ι → Ω → ℝ) → (ℕ → ι) → {n : ℕ} → (Fin n → Ω) → ENNReal` | For a measure on a measurable sample space, a class of real-valued functions, a countable enumeration of that class, and a finite sample, the countable empirical-process supremum is the extended nonnegative real supremum, over the enumerated functions, of the absolute centered empirical average. |
| `Stat.Concentration.vcEntropy_chaining_bound` | `Causalean.Stat.Concentration.HasVCUniformEntropy μ g U σ A v → ∃ C, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → (∫⁻ (w : Fin n → Ω), Causalean.Stat.Concentration.countableEmpiricalProcessSup μ g g0 w ∂MeasureTheory.Measure.pi fun x => μ) ≤ ENNReal.ofReal (C * (σ * √(Real.log (U / σ) / ↑n) + U * Real.log (U / σ) / ↑n))` | Dudley chaining bound for VC-type entropy. Let `μ` be a probability measure on `Ω`, `g : ι → Ω → ℝ` a family of functions, and `g0 : ℕ → ι` a countable enumeration of the index set. If `g` has uniform VC-type entropy relative to `μ`, with envelope `U`, population $L^2$ radius `σ`, covering-entropy base `A`, and exponent `v`, then there is a universal constant `C > 0` such that, for every sample size `n ≥ 1`, the expectation of the countable empirical-process supremum along the enumeration `g0` over the `n`-fold product of `μ` is at most `C · (σ √(log(U/σ)/n) + U log(U/σ)/n)`. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.InformationTheory.CommonStatisticBernoulli -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.InformationTheory.one_add_mul_one_sub_mem_Icc` | `p ∈ Set.Icc (1 / 4) (3 / 4) → 1 + p * (1 - p) ∈ Set.Icc 1 (5 / 4)` | A Bernoulli parameter in the middle half of the unit interval has variance between zero and one quarter, so adding unit noise gives variance between one and five quarters. |
| `Mathlib.InformationTheory.commonStatisticBernoulliKernel` | `(p : S → ℝ) → Measurable p → ProbabilityTheory.Kernel S ℝ` | For a measurable input space, a real-valued function of the input, and the hypothesis that this function is measurable, the common-statistic Bernoulli kernel assigns to every input the Bernoulli probability measure on the real line with success probability given by that function at the input. |
| `Mathlib.InformationTheory.commonStatisticBernoulliKernel_isMarkovKernel` | `(∀ (r : S), 0 ≤ p r) → (∀ (r : S), p r ≤ 1) → ProbabilityTheory.IsMarkovKernel (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp)` | Pointwise unit-interval parameters make the common-statistic Bernoulli kernel Markov. |
| `Mathlib.InformationTheory.commonStatisticBernoulli_klDiv_le_of_localized_parameter` | `(∀ (r : ℝ), 1 / 4 ≤ p r) → (∀ (r : ℝ), p r ≤ 3 / 4) → (∀ (r : ℝ), 1 / 4 ≤ q r) → (∀ (r : ℝ), q r ≤ 3 / 4) → ∀ {D : ℝ}, 0 ≤ D → ∀ {E : Set ℝ}, MeasurableSet E → (∀ᵐ (r : ℝ) ∂m, \|p r - q r\| ≤ E.indicator (fun x => D) r) → InformationTheory.klDiv (m.compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp)) (m.compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel q hq)) ≤ ENNReal.ofReal (4 * D ^ 2) * m E` | A common statistic with conditionally Bernoulli outcomes has KL bounded by the squared change in its success parameter, integrated only over the statistic region where that parameter can change. This is the generic disintegration step used by the signed hard-cell comparison. |
| `Mathlib.InformationTheory.commonStatisticBernoulliOutcome_klDiv_le_of_localized_parameter` | `(∀ (r : ℝ), 1 / 4 ≤ p r) → (∀ (r : ℝ), p r ≤ 3 / 4) → (∀ (r : ℝ), 1 / 4 ≤ q r) → (∀ (r : ℝ), q r ≤ 3 / 4) → ∀ {D : ℝ}, 0 ≤ D → ∀ {E : Set ℝ}, MeasurableSet E → (∀ᵐ (r : ℝ) ∂m, \|p r - q r\| ≤ E.indicator (fun x => D) r) → InformationTheory.klDiv (MeasureTheory.Measure.map Prod.swap (m.compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp))) (MeasureTheory.Measure.map Prod.swap (m.compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel q hq))) ≤ ENNReal.ofReal (4 * D ^ 2) * m E` | Swapping a common statistic behind its Bernoulli outcome preserves the localized KL estimate, giving the `(outcome, statistic)` coordinate order used by signed observations. |
| `Mathlib.InformationTheory.statisticSuccessMeasure` | `MeasureTheory.Measure A → (A → ℝ) → (A → ℝ) → MeasureTheory.Measure ℝ` | For a measurable sample space, a measure on that space, a real-valued success-weight function, and a real-valued statistic, the success-weighted statistic law is the pushforward along the statistic of the base measure weighted by $\max\{p(x),0\}$. |
| `Mathlib.InformationTheory.statisticSuccessParameter` | `MeasureTheory.Measure A → (A → ℝ) → (A → ℝ) → ℝ → ℝ` | For a measurable sample space, a measure on that space, a real-valued success-weight function, and a real-valued statistic, the statistic-level success parameter is the Radon--Nikodym derivative of the success-weighted statistic law with respect to the statistic's pushforward law under the base measure, converted to a real number. |
| `Mathlib.InformationTheory.statisticSuccessMeasure_absolutelyContinuous` | `Measurable stat → (∀ (x : A), p x ≤ 1) → (Causalean.Mathlib.InformationTheory.statisticSuccessMeasure nu p stat).AbsolutelyContinuous (MeasureTheory.Measure.map stat nu)` | The success-weighted statistic law is dominated by the statistic marginal when the pointwise success probability is at most one. |
| `Mathlib.InformationTheory.statisticSuccessParameter_setIntegral` | `Measurable p → Measurable stat → (∀ (x : A), 0 ≤ p x) → (∀ (x : A), p x ≤ 1) → ∀ (B : Set ℝ), MeasurableSet B → ∫ (r : ℝ) in B, Causalean.Mathlib.InformationTheory.statisticSuccessParameter nu p stat r ∂MeasureTheory.Measure.map stat nu = ∫ (x : A) in {x \| stat x ∈ B}, p x ∂nu` | Set integrals of the conditional parameter recover success-weighted integrals on statistic preimages. |
| `Mathlib.InformationTheory.statisticSuccessParameter_mem_Icc_ae` | `Measurable p → Measurable stat → (∀ (x : A), 1 / 4 ≤ p x) → (∀ (x : A), p x ≤ 3 / 4) → ∀ᵐ (r : ℝ) ∂MeasureTheory.Measure.map stat nu, Causalean.Mathlib.InformationTheory.statisticSuccessParameter nu p stat r ∈ Set.Icc (1 / 4) (3 / 4)` | Middle-half pointwise bounds pass to the conditional statistic parameter almost everywhere. |
| `Mathlib.InformationTheory.clippedStatisticSuccessParameter` | `MeasureTheory.Measure A → (A → ℝ) → (A → ℝ) → ℝ → ℝ` | For a measurable sample space, a measure on that space, a real-valued success-weight function, and a real-valued statistic, the clipped statistic-level success parameter is the statistic-level success parameter truncated below at $1/4$ and above at $3/4$. |
| `Mathlib.InformationTheory.clippedStatisticSuccessParameter_measurable` | `Measurable (Causalean.Mathlib.InformationTheory.clippedStatisticSuccessParameter nu p stat)` | — |
| `Mathlib.InformationTheory.clippedStatisticSuccessParameter_mem_Icc` | `Causalean.Mathlib.InformationTheory.clippedStatisticSuccessParameter nu p stat r ∈ Set.Icc (1 / 4) (3 / 4)` | — |
| `Mathlib.InformationTheory.clippedStatisticSuccessParameter_ae_eq` | `Measurable p → Measurable stat → (∀ (x : A), 1 / 4 ≤ p x) → (∀ (x : A), p x ≤ 3 / 4) → Causalean.Mathlib.InformationTheory.clippedStatisticSuccessParameter nu p stat =ᵐ[MeasureTheory.Measure.map stat nu] Causalean.Mathlib.InformationTheory.statisticSuccessParameter nu p stat` | — |
| `Mathlib.InformationTheory.commonStatisticBernoulliKernel_setLIntegral_eq` | `(∀ (x : A), 0 ≤ p x) → (∀ (x : A), p x ≤ 1) → (∀ (x : B), 0 ≤ p' x) → (∀ (x : B), p' x ≤ 1) → ∀ {D : Set A} {D' : Set B}, nu D = nu' D' → ∫ (x : A) in D, p x ∂nu = ∫ (x : B) in D', p' x ∂nu' → ∀ (E : Set ℝ), ∫⁻ (x : A) in D, ((Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp) x) E ∂nu = ∫⁻ (x : B) in D', ((Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p' hp') x) E ∂nu'` | Integrating Bernoulli kernels over two base sets gives the same outcome measure when the base masses and success-weighted masses agree. |
| `Mathlib.InformationTheory.statisticBernoulliOutcomeLaw_eq_map_swap_compProd` | `Measurable stat → (∀ (x : A), 1 / 4 ≤ p x) → (∀ (x : A), p x ≤ 3 / 4) → MeasureTheory.Measure.map (fun z => (z.2, stat z.1)) (nu.compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp)) = MeasureTheory.Measure.map Prod.swap ((MeasureTheory.Measure.map stat nu).compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel (Causalean.Mathlib.InformationTheory.clippedStatisticSuccessParameter nu p stat) (Causalean.Mathlib.InformationTheory.clippedStatisticSuccessParameter_measurable nu p stat)))` | Compressing the base coordinate to a statistic turns a Bernoulli mixture into a Bernoulli composition product over the statistic marginal. |
| `Mathlib.InformationTheory.clippedStatisticSuccessParameter_abs_sub_le_ae` | `Measurable p → Measurable p' → Measurable stat → (∀ (x : A), 1 / 4 ≤ p x) → (∀ (x : A), p x ≤ 3 / 4) → (∀ (x : A), 1 / 4 ≤ p' x) → (∀ (x : A), p' x ≤ 3 / 4) → MeasureTheory.Measure.map stat nu = MeasureTheory.Measure.map stat nu' → ∀ {D : ℝ}, 0 ≤ D → ∀ {E : Set ℝ}, MeasurableSet E → (∀ (B : Set ℝ), MeasurableSet B → \|∫ (x : A) in {x \| stat x ∈ B}, p x ∂nu - ∫ (x : A) in {x \| stat x ∈ B}, p' x ∂nu'\| ≤ D * ((MeasureTheory.Measure.map stat nu) (B ∩ E)).toReal) → ∀ᵐ (r : ℝ) ∂MeasureTheory.Measure.map stat nu, \|Causalean.Mathlib.InformationTheory.clippedStatisticSuccessParameter nu p stat r - Causalean.Mathlib.InformationTheory.clippedStatisticSuccessParameter nu' p' stat r\| ≤ E.indicator (fun x => D) r` | A localized setwise bound on success-weighted statistic masses yields the corresponding almost-everywhere bound on conditional Bernoulli parameters. |
| `Mathlib.InformationTheory.statisticBernoulliOutcome_klDiv_le_of_localized_success_bound` | `Measurable stat → (∀ (x : A), 1 / 4 ≤ p x) → (∀ (x : A), p x ≤ 3 / 4) → (∀ (x : A), 1 / 4 ≤ p' x) → (∀ (x : A), p' x ≤ 3 / 4) → MeasureTheory.Measure.map stat nu = MeasureTheory.Measure.map stat nu' → ∀ {D : ℝ}, 0 ≤ D → ∀ {E : Set ℝ}, MeasurableSet E → (∀ (B : Set ℝ), MeasurableSet B → \|∫ (x : A) in {x \| stat x ∈ B}, p x ∂nu - ∫ (x : A) in {x \| stat x ∈ B}, p' x ∂nu'\| ≤ D * ((MeasureTheory.Measure.map stat nu) (B ∩ E)).toReal) → InformationTheory.klDiv (MeasureTheory.Measure.map (fun z => (z.2, stat z.1)) (nu.compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp))) (MeasureTheory.Measure.map (fun z => (z.2, stat z.1)) (nu'.compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p' hp'))) ≤ ENNReal.ofReal (4 * D ^ 2) * (MeasureTheory.Measure.map stat nu) E` | For a measurable space `A`, two finite measures `nu` and `nu'` on it, and success-probability functions `p`, `p'` on `A`, suppose `p`, `p'`, and a statistic `stat` are all measurable, `p` takes values in `[1/4, 3/4]` and `p'` likewise takes values in `[1/4, 3/4]`, and `stat` pushes `nu` and `nu'` forward to the same marginal law. Given a nonnegative discrepancy bound `D` and a measurable exceptional set `E` such that for every measurable set `B` of statistic values, the setwise success-mass discrepancy `\|∫_{stat∈B} p dnu − ∫_{stat∈B} p' dnu'\|` is at most `D` times the `stat`-pushforward mass of `nu` on `B ∩ E`, then the Kullback–Leibler divergence between the compressed Bernoulli-outcome laws obtained by pairing the outcome with `stat` under `nu` and under `nu'` is at most `4·D²` times the `stat`-pushforward mass of `E` under `nu`. |
| `Mathlib.InformationTheory.statisticBernoulliOutcome_restrict_compl_eq_of_localized_success_bound` | `Measurable stat → (∀ (x : A), 1 / 4 ≤ p x) → (∀ (x : A), p x ≤ 3 / 4) → (∀ (x : A), 1 / 4 ≤ p' x) → (∀ (x : A), p' x ≤ 3 / 4) → MeasureTheory.Measure.map stat nu = MeasureTheory.Measure.map stat nu' → ∀ {D : ℝ}, 0 ≤ D → ∀ {E : Set ℝ}, MeasurableSet E → (∀ (B : Set ℝ), MeasurableSet B → \|∫ (x : A) in {x \| stat x ∈ B}, p x ∂nu - ∫ (x : A) in {x \| stat x ∈ B}, p' x ∂nu'\| ≤ D * ((MeasureTheory.Measure.map stat nu) (B ∩ E)).toReal) → (MeasureTheory.Measure.map (fun z => (z.2, stat z.1)) (nu.compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp))).restrict {z \| z.2 ∉ E} = (MeasureTheory.Measure.map (fun z => (z.2, stat z.1)) (nu'.compProd (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p' hp'))).restrict {z \| z.2 ∉ E}` | Common statistic marginals and a localized setwise success-mass bound also imply exact agreement of the compressed outcome laws away from the exceptional statistic set. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Nonparametric.LocalPolynomial.GramCoercivity -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.Nonparametric.LocalPolynomial.localPolynomial` | `(p : ℕ) → (Fin (p + 1) → ℝ) → Polynomial ℝ` | For a nonnegative polynomial degree and real coefficients indexed from zero through that degree, the local-polynomial coefficient polynomial is $\sum_i v_i u^i$. |
| `Stat.Nonparametric.LocalPolynomial.localPolynomial_eval` | `Polynomial.eval u (Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial p v) = ∑ i, v i * u ^ ↑i` | Evaluation of the coefficient polynomial is the dot product with the monomial basis. |
| `Stat.Nonparametric.LocalPolynomial.localPolynomial_eq_zero_iff` | `Causalean.Stat.Nonparametric.LocalPolynomial.localPolynomial p v = 0 ↔ v = 0` | The coefficient polynomial vanishes only when every coefficient does. |
| `Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy` | `(p : ℕ) → (Fin (p + 1) → ℝ) → ℝ` | For a nonnegative polynomial degree and real coefficients indexed from zero through that degree, the radial polynomial energy is the double sum of $v_i v_j$ divided by $i+j+2$, over all coefficient indices $i,j$ from zero through that degree. |
| `Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy_eq_integral` | `Causalean.Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy p v = ∫ (u : ℝ) in 0..1, (∑ i, v i * u ^ ↑i) ^ 2 * u` | The explicit moment matrix is exactly the weighted squared-polynomial integral on the unit interval. |
| `Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy_pos` | `v ≠ 0 → 0 < Causalean.Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy p v` | A nonzero coefficient vector has strictly positive radial energy. |
| `Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy_continuous` | `Continuous (Causalean.Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy p)` | The radial energy is a continuous quadratic function of its coefficient vector. |
| `Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy_smul` | `Causalean.Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy p (a • v) = a ^ 2 * Causalean.Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy p v` | Radial energy is homogeneous of degree two in the coefficient vector. |
| `Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy_coercive` | `∃ c, 0 < c ∧ ∀ (v : Fin (p + 1) → ℝ), c * ∑ i, v i ^ 2 ≤ Causalean.Stat.Nonparametric.LocalPolynomial.radialPolynomialEnergy p v` | For a polynomial degree bound `p`, there is a positive constant such that the radial polynomial energy of any coefficient vector is bounded below by that constant times the sum of the squared coefficients: on the Euclidean unit sphere, radial polynomial energy has a positive minimum, and homogeneity packages this as a coercive lower bound for all coefficient vectors. |
| `Stat.Nonparametric.LocalPolynomial.signedRadialPolynomialEnergy_coercive` | `∃ c, 0 < c ∧ ∀ (t : Bool) (v : Fin (p + 1) → ℝ), c * ∑ i, v i ^ 2 ≤ ∫ (u : ℝ) in 0..1, (∑ i, v i * (if t = true then u else -u) ^ ↑i) ^ 2 * u` | The same coercivity constant works in both signed-distance orientations. The negative orientation merely changes coefficient `i` by the sign `(-1)^i`, which preserves the sum of coefficient squares. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Analysis.HalfDiscPolar -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.planarRadius` | `ℝ × ℝ → ℝ` | For a point in the real coordinate plane, the planar radius is its Euclidean distance from the origin, namely $\sqrt{x^2+y^2}$ for coordinates $(x,y)$. |
| `Mathlib.Analysis.planarRadius_measurable` | `Measurable Causalean.Mathlib.Analysis.planarRadius` | The Euclidean radius on the coordinate plane is Borel measurable. |
| `Mathlib.Analysis.planarAngle` | `ℝ × ℝ → ℝ` | For a point in the real coordinate plane, the planar angle is the angular coordinate assigned by the polar-coordinate chart. |
| `Mathlib.Analysis.integral_cos_zero_to_pi` | `∫ (θ : ℝ) in Set.Ioc 0 Real.pi, Real.cos θ = 0` | The cosine has zero integral on a half-circle. |
| `Mathlib.Analysis.integral_cos_sq_zero_to_pi` | `∫ (θ : ℝ) in Set.Ioc 0 Real.pi, Real.cos θ ^ 2 = Real.pi / 2` | The quadratic cosine moment on a half-circle is `π / 2`. |
| `Mathlib.Analysis.halfDisc_weighted_polar_integral` | `∫ (z : ℝ × ℝ) in {z \| 0 < z.2 ∧ Causalean.Mathlib.Analysis.planarRadius z ≤ r}, g (Causalean.Mathlib.Analysis.planarRadius z) * h (Causalean.Mathlib.Analysis.planarAngle z) = (∫ (s : ℝ) in Set.Ioc 0 r, s * g s) * ∫ (θ : ℝ) in Set.Ioo 0 Real.pi, h θ` | For radial and angular weight functions `g` and `h` and a radius `r`, the integral of the product `g(radius)·h(angle)` over the open upper half-disc of radius `r` factors as the product of the radial integral `∫ s·g(s) ds` over `(0, r]` and the angular integral `∫ h(θ) dθ` over `(0, π)`. |
| `Mathlib.Analysis.halfDisc_weighted_cos_cancellation` | `∫ (z : ℝ × ℝ) in {z \| 0 < z.2 ∧ Causalean.Mathlib.Analysis.planarRadius z ≤ r}, g (Causalean.Mathlib.Analysis.planarRadius z) * Real.cos (Causalean.Mathlib.Analysis.planarAngle z) = 0` | A cosine angular tilt has zero integral against every radial weight on an upper half-disc. |
| `Mathlib.Analysis.halfDisc_radialSet_weighted_cos_cancellation` | `MeasurableSet A → ∫ (z : ℝ × ℝ) in {z \| 0 < z.2 ∧ Causalean.Mathlib.Analysis.planarRadius z ≤ r} ∩ Causalean.Mathlib.Analysis.planarRadius ⁻¹' A, g (Causalean.Mathlib.Analysis.planarRadius z) * Real.cos (Causalean.Mathlib.Analysis.planarAngle z) = 0` | A cosine angular tilt has zero mass on every measurable radial subset of an upper half-disc. This is the setwise interface used to identify radial pushforwards, rather than merely their total masses. |
| `Mathlib.Analysis.planarFirst_div_radius_eq_cos` | `0 < z.2 → z.1 / Causalean.Mathlib.Analysis.planarRadius z = Real.cos (Causalean.Mathlib.Analysis.planarAngle z)` | On the open upper half-plane, the first coordinate divided by the radius is the cosine of the polar angle. |
| `Mathlib.Analysis.halfDisc_weighted_first_div_radius_cancellation` | `∫ (z : ℝ × ℝ) in {z \| 0 < z.2 ∧ Causalean.Mathlib.Analysis.planarRadius z ≤ r}, g (Causalean.Mathlib.Analysis.planarRadius z) * (z.1 / Causalean.Mathlib.Analysis.planarRadius z) = 0` | A radial weight times the Cartesian direction cosine has zero integral on an open upper half-disc. |
| `Mathlib.Analysis.closedHalfDisc_weighted_first_div_radius_cancellation` | `∫ (z : ℝ × ℝ) in {z \| 0 ≤ z.2 ∧ Causalean.Mathlib.Analysis.planarRadius z ≤ r}, g (Causalean.Mathlib.Analysis.planarRadius z) * (z.1 / Causalean.Mathlib.Analysis.planarRadius z) = 0` | Replacing the open diameter of an upper half-disc by the closed diameter does not affect the Cartesian cosine integral. |
| `Mathlib.Analysis.translatedClosedHalfDisc_weighted_first_div_radius_cancellation` | `∫ (z : ℝ × ℝ) in {z \| 0 ≤ (z - c).2 ∧ Causalean.Mathlib.Analysis.planarRadius (z - c) ≤ r}, g (Causalean.Mathlib.Analysis.planarRadius (z - c)) * ((z - c).1 / Causalean.Mathlib.Analysis.planarRadius (z - c)) = 0` | Translation preserves the zero Cartesian-cosine integral over a closed upper half-disc. |
| `Mathlib.Analysis.halfDisc_weighted_cos_sq` | `∫ (z : ℝ × ℝ) in {z \| 0 < z.2 ∧ Causalean.Mathlib.Analysis.planarRadius z ≤ r}, g (Causalean.Mathlib.Analysis.planarRadius z) * Real.cos (Causalean.Mathlib.Analysis.planarAngle z) ^ 2 = (∫ (s : ℝ) in Set.Ioc 0 r, s * g s) * (Real.pi / 2)` | The cosine-squared angular moment converts a radial weight into the nonzero `π/2` factor used to cancel the affine regression term. |
| `Mathlib.Analysis.halfDisc_radial_integral` | `∫ (z : ℝ × ℝ) in {z \| 0 < z.2 ∧ Causalean.Mathlib.Analysis.planarRadius z ≤ r}, g (Causalean.Mathlib.Analysis.planarRadius z) = ∫ (s : ℝ) in Set.Ioc 0 r, Real.pi * s * g s` | A radial integrand on a half-disc admits the expected polar-coordinate decomposition. |
| `Mathlib.Analysis.halfDisc_cos_radial_cancellation` | `∫ (s : ℝ) in Set.Ioc 0 r, s * g s * ∫ (θ : ℝ) in Set.Ioc 0 Real.pi, Real.cos θ = 0` | Multiplication by cosine contributes zero after angular integration on every radial shell. |
| `Mathlib.Analysis.translatedHalfDisc_weighted_cos_cancellation` | `∫ (z : ℝ × ℝ) in (fun u => c + u) '' {u \| 0 < u.2 ∧ Causalean.Mathlib.Analysis.planarRadius u ≤ r}, g (Causalean.Mathlib.Analysis.planarRadius (z - c)) * Real.cos (Causalean.Mathlib.Analysis.planarAngle (z - c)) = 0` | Translating an upper half-disc does not change the cosine cancellation. |
| `Mathlib.Analysis.translatedHalfDisc_radialSet_weighted_cos_cancellation` | `MeasurableSet A → ∫ (z : ℝ × ℝ) in (fun u => c + u) '' {u \| 0 < u.2 ∧ Causalean.Mathlib.Analysis.planarRadius u ≤ r} ∩ {z \| Causalean.Mathlib.Analysis.planarRadius (z - c) ∈ A}, g (Causalean.Mathlib.Analysis.planarRadius (z - c)) * Real.cos (Causalean.Mathlib.Analysis.planarAngle (z - c)) = 0` | Translation preserves cosine cancellation on every measurable radial subset of a half-disc. |
<!-- /GEN -->

<!-- GEN:Causalean.Stat.Nonparametric.LocalPolynomial.CoordinateDerivative -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.Nonparametric.LocalPolynomial.coordinateMultiOrder` | `(Fin 2 → ℕ) → ℕ` | For a bivariate multi-index, the total order of that multi-index is the sum of its two coordinate orders. |
| `Stat.Nonparametric.LocalPolynomial.coordinateDirections` | `(alpha : Fin 2 → ℕ) → Fin (Causalean.Stat.Nonparametric.LocalPolynomial.coordinateMultiOrder alpha) → EuclideanSpace ℝ (Fin 2)` | For a bivariate multi-index and a position in a list whose length is its total order, the associated ordered standard-coordinate direction is the first standard coordinate direction when the position is smaller than the first coordinate order, and the second standard coordinate direction otherwise. |
| `Stat.Nonparametric.LocalPolynomial.coordinatePartial` | `(EuclideanSpace ℝ (Fin 2) → ℝ) → (Fin 2 → ℕ) → EuclideanSpace ℝ (Fin 2) → ℝ` | For a real-valued function on two-dimensional Euclidean space, a bivariate multi-index, and a point in that space, the scalar coordinate partial derivative is the iterated derivative of total order given by the multi-index, evaluated at the point along the associated ordered standard-coordinate directions. |
| `Stat.Nonparametric.LocalPolynomial.coordinatePartial_abs_le_iteratedFDeriv_norm` | `\|Causalean.Stat.Nonparametric.LocalPolynomial.coordinatePartial f alpha x\| ≤ ‖iteratedFDeriv ℝ (Causalean.Stat.Nonparametric.LocalPolynomial.coordinateMultiOrder alpha) f x‖` | Evaluating the iterated Fréchet derivative of a function `f` of a bivariate multi-index `alpha` at a point `x`, along the standard coordinate directions, cannot increase its operator norm — the resulting scalar coordinate partial is bounded in absolute value by the operator norm of the full iterated derivative. |
| `Stat.Nonparametric.LocalPolynomial.coordinatePartial_sub_abs_le_iteratedFDeriv_sub_norm` | `\|Causalean.Stat.Nonparametric.LocalPolynomial.coordinatePartial f alpha x - Causalean.Stat.Nonparametric.LocalPolynomial.coordinatePartial f alpha z\| ≤ ‖iteratedFDeriv ℝ (Causalean.Stat.Nonparametric.LocalPolynomial.coordinateMultiOrder alpha) f x - iteratedFDeriv ℝ (Causalean.Stat.Nonparametric.LocalPolynomial.coordinateMultiOrder alpha) f z‖` | Differences of scalar coordinate partials are bounded by the operator norm of the corresponding Fréchet-derivative difference. |
<!-- /GEN -->

### Finite penalized model selection

`Stat/MEstimation/FiniteModelSelection.lean` provides the finite-model
selection step used by fixed-dimensional BIC-style arguments. Coordinatewise
probability convergence becomes uniform convergence over the finite candidate
set; a strictly separated population optimum and sublinear deterministic
penalties then make every ranked empirical minimizer select a population
minimizer with probability tending to one.

<!-- GEN:Causalean.Stat.MEstimation.FiniteModelSelection -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.finiteMaxError` | `(ι → ℝ) → (ι → ℝ) → ℝ` | For an indexed real vector and a deterministic target vector, the largest absolute coordinate error is the maximum of their coordinatewise absolute differences over a finite nonempty index type. |
| `Stat.tendsto_inProb_finiteMaxError` | `(∀ (i : ι), Causalean.Stat.Tendsto_inProb (fun n ω => empirical n ω i) (fun x => population i) μ) → Causalean.Stat.Tendsto_inProb (fun n ω => Causalean.Stat.finiteMaxError (empirical n ω) population) (fun x => 0) μ` | If empirical loss vectors have coordinatewise population targets under a sampling measure, and each coordinate converges in probability, then the largest absolute coordinate error converges in probability to zero. |
| `Stat.tendsto_measure_finiteMaxError_ge_zero` | `(∀ (i : ι), Causalean.Stat.Tendsto_inProb (fun n ω => empirical n ω i) (fun x => population i) μ) → ∀ {ε : ℝ}, 0 < ε → Filter.Tendsto (fun n => μ {ω \| ε ≤ Causalean.Stat.finiteMaxError (empirical n ω) population}) Filter.atTop (nhds 0)` | If empirical loss vectors have coordinatewise population targets under a sampling measure, and each coordinate converges in probability, then, for a positive tolerance, the probability that the largest coordinate error exceeds that tolerance converges to zero. |
| `Stat.populationMinimizers` | `(ι → ℝ) → Set ι` | For a population-loss vector, the population-minimizer class contains exactly the model indices attaining its smallest loss. |
| `Stat.IsRankedMinimizer` | `(ι → ℕ) → (ι → ℝ) → ι → Prop` | Given a deterministic tie rank, a criterion vector, and a selected model index, the ranked-minimizer condition says that the selected model has a smaller criterion than each competitor, or an equal criterion and no larger rank. |
| `Stat.IsRankedMinimizer.le` | `Causalean.Stat.IsRankedMinimizer rank criterion selected → ∀ (j : ι), criterion selected ≤ criterion j` | If a selected model is a ranked minimizer, then, for each competing model, its criterion value is no larger than the competitor's. |
| `Stat.finite_penalized_argmin_failure_tendsto_zero` | `(∀ (i : ι), Causalean.Stat.Tendsto_inProb (fun n ω => empirical n ω i) (fun x => population i) μ) → (∃ gap, 0 < gap ∧ ∀ i ∈ Causalean.Stat.populationMinimizers population, ∀ j ∉ Causalean.Stat.populationMinimizers population, population i + gap ≤ population j) → (∀ (i : ι), Filter.Tendsto (fun n => penalty n i / ↑n) Filter.atTop (nhds 0)) → Function.Injective rank → (∀ (n : ℕ) (ω : Ω), Causalean.Stat.IsRankedMinimizer rank (fun i => ↑n * empirical n ω i + penalty n i) (selector n ω)) → Filter.Tendsto (fun n => μ {ω \| selector n ω ∉ Causalean.Stat.populationMinimizers population}) Filter.atTop (nhds 0)` | Let empirical losses have population losses under a probability measure, with deterministic penalties, a deterministic tie rank, and a selected model. If each empirical loss converges in probability, population minimizers are separated by a positive gap, each penalty is sublinear, the rank is injective, and the selector is always the ranked minimizer of the penalized empirical criterion, then the probability of selecting outside the population-minimizer class converges to zero. |
| `Stat.finite_penalized_argmin_consistent` | `(∀ (i : ι), Causalean.Stat.Tendsto_inProb (fun n ω => empirical n ω i) (fun x => population i) μ) → (∃ gap, 0 < gap ∧ ∀ i ∈ Causalean.Stat.populationMinimizers population, ∀ j ∉ Causalean.Stat.populationMinimizers population, population i + gap ≤ population j) → (∀ (i : ι), Filter.Tendsto (fun n => penalty n i / ↑n) Filter.atTop (nhds 0)) → Function.Injective rank → (∀ (n : ℕ) (ω : Ω), Causalean.Stat.IsRankedMinimizer rank (fun i => ↑n * empirical n ω i + penalty n i) (selector n ω)) → (∀ (n : ℕ), MeasurableSet {ω \| selector n ω ∈ Causalean.Stat.populationMinimizers population}) → Filter.Tendsto (fun n => μ {ω \| selector n ω ∈ Causalean.Stat.populationMinimizers population}) Filter.atTop (nhds 1)` | Let empirical losses have population losses under a probability measure, with deterministic penalties, a deterministic tie rank, and a selected model. If each empirical loss converges in probability, population minimizers are separated by a positive gap, each penalty is sublinear, the rank is injective, the selector is always the ranked minimizer of the penalized empirical criterion, and each success event is measurable, then the probability of selecting a population minimizer converges to one. |
<!-- /GEN -->

### Gaussian covariance-model selection

`Stat/GaussianCovariance.lean` supplies the Gaussian covariance criterion, compact-model separation, and the population-gap interface used with finite penalized model selection.

<!-- GEN:Causalean.Stat.GaussianCovariance -->
| Decl | Signature | Description |
|---|---|---|
| `Stat.PositiveCovariance` | `(V : Type u_2) → [Fintype V] → Type (max 0 u_2)` | For a finite coordinate type, the positive covariance matrices are real square matrices equipped with a proof of positive definiteness. |
| `Stat.gaussianCovarianceDiscrepancy` | `Matrix V V ℝ → Matrix V V ℝ → ℝ` | For a candidate covariance matrix and target second-moment matrix, the Gaussian covariance discrepancy is log determinant plus inverse-weighted trace. |
| `Stat.normalizedCovarianceDiscrepancy` | `Causalean.Stat.PositiveCovariance V → ℝ` | For positive-definite candidate and target covariances, the normalized Gaussian covariance discrepancy subtracts the criterion's value at the target. |
| `Stat.continuous_gaussianCovarianceDiscrepancy` | `Continuous fun p => Causalean.Stat.gaussianCovarianceDiscrepancy (↑p.1) p.2` | The Gaussian covariance discrepancy varies continuously with its positive-definite candidate and target matrix. |
| `Stat.continuous_normalizedCovarianceDiscrepancy` | `Continuous fun p => Causalean.Stat.normalizedCovarianceDiscrepancy p.1 p.2` | The normalized Gaussian covariance discrepancy varies continuously with both positive-definite covariances. |
| `Stat.normalizedCovarianceDiscrepancy_nonneg` | `0 ≤ Causalean.Stat.normalizedCovarianceDiscrepancy K T` | For positive-definite candidate and target covariances, the normalized Gaussian covariance discrepancy is nonnegative. |
| `Stat.normalizedCovarianceDiscrepancy_eq_zero_iff` | `Causalean.Stat.normalizedCovarianceDiscrepancy K T = 0 ↔ K = T` | For positive-definite candidate and target covariances, the normalized Gaussian covariance discrepancy is zero exactly when the two covariances agree. |
| `Stat.gaussianCovarianceDiscrepancy_le_truth_iff` | `Causalean.Stat.gaussianCovarianceDiscrepancy ↑K ↑T ≤ Causalean.Stat.gaussianCovarianceDiscrepancy ↑T ↑T ↔ K = T` | For positive-definite candidate and target covariances, the candidate has no larger Gaussian discrepancy than the truth exactly when it is the truth. |
| `Stat.IsDiscrepancyAttainedOn` | `Set (Causalean.Stat.PositiveCovariance V) → Matrix V V ℝ → Prop` | For a covariance model and target matrix, discrepancy attainment means that one model member has no larger Gaussian discrepancy than every other member. |
| `Stat.HasCompactDiscrepancySublevel` | `Set (Causalean.Stat.PositiveCovariance V) → Matrix V V ℝ → Prop` | For a covariance model and target matrix, a compact discrepancy sublevel is a nonempty compact cut of the model below some criterion value. |
| `Stat.discrepancyAttainedOn_of_isCompact` | `IsCompact M → M.Nonempty → ∀ (T : Matrix V V ℝ), Causalean.Stat.IsDiscrepancyAttainedOn M T` | Given a compact covariance model, a nonempty model, and a target matrix, the Gaussian discrepancy minimum is attained. |
| `Stat.discrepancyAttainedOn_of_compactSublevel` | `Causalean.Stat.HasCompactDiscrepancySublevel M T → Causalean.Stat.IsDiscrepancyAttainedOn M T` | Given a covariance model with a nonempty compact discrepancy sublevel, the global Gaussian discrepancy minimum is attained. |
| `Stat.exists_positive_gap_of_attained` | `Causalean.Stat.IsDiscrepancyAttainedOn M ↑T → T ∉ M → ∃ gap, 0 < gap ∧ ∀ K ∈ M, gap ≤ Causalean.Stat.normalizedCovarianceDiscrepancy K T` | Given an attained covariance-model discrepancy that omits the positive-definite truth, every model covariance has a common strictly positive normalized gap. |
| `Stat.exists_positive_gap_of_isCompact` | `IsCompact M → M.Nonempty → ∀ {T : Causalean.Stat.PositiveCovariance V}, T ∉ M → ∃ gap, 0 < gap ∧ ∀ K ∈ M, gap ≤ Causalean.Stat.normalizedCovarianceDiscrepancy K T` | Given a compact covariance model, a nonempty model, and a truth outside the model, the model is separated from the truth by a strictly positive population gap. |
| `Stat.exists_stable_positive_gap` | `IsCompact M → M.Nonempty → ∀ {T : Causalean.Stat.PositiveCovariance V}, T ∉ M → ∃ gap, 0 < gap ∧ ∃ U ∈ nhds T, ∀ T' ∈ U, ∀ K ∈ M, gap ≤ Causalean.Stat.normalizedCovarianceDiscrepancy K T'` | Given a compact covariance model, a nonempty model, and a truth outside the model, the strict positive population gap persists for nearby positive-definite truths. |
| `Stat.covarianceModelLoss` | `Set (Causalean.Stat.PositiveCovariance V) → Matrix V V ℝ → ℝ` | For a covariance model and target matrix, the population loss is the infimum Gaussian discrepancy over positive-definite model covariances. |
| `Stat.continuous_covarianceModelLoss` | `IsCompact M → M.Nonempty → Continuous (Causalean.Stat.covarianceModelLoss M)` | Given a compact covariance model that is nonempty, the population loss is continuous in the target second-moment matrix. |
| `Stat.populationMinimizers_covarianceModelLoss_iff` | `(∀ (i : I), IsCompact (models i)) → (∀ (i : I), (models i).Nonempty) → ∀ (T : Causalean.Stat.PositiveCovariance V), (∃ i, T ∈ models i) → ∀ (i : I), (i ∈ Causalean.Stat.populationMinimizers fun j => Causalean.Stat.covarianceModelLoss (models j) ↑T) ↔ T ∈ models i` | Given covariance models that are compact and nonempty, a positive-definite truth contained in some model, and a model index, the population minimizers are exactly the indices whose models contain the truth. |
| `Stat.finiteCovarianceModel_populationGap` | `(∀ (i : I), IsCompact (models i)) → (∀ (i : I), (models i).Nonempty) → ∀ (T : Causalean.Stat.PositiveCovariance V), (∃ i, T ∈ models i) → ∃ gap, 0 < gap ∧ ∀ i ∈ Causalean.Stat.populationMinimizers fun j => Causalean.Stat.covarianceModelLoss (models j) ↑T, ∀ j ∉ Causalean.Stat.populationMinimizers fun k => Causalean.Stat.covarianceModelLoss (models k) ↑T, Causalean.Stat.covarianceModelLoss (models i) ↑T + gap ≤ Causalean.Stat.covarianceModelLoss (models j) ↑T` | Given a finite family of covariance models whose members are compact and nonempty, and a positive-definite true covariance contained in at least one model, the population losses have the positive gap required by finite penalized model selection. |
| `Stat.tendstoInProb_covarianceModelLoss` | `(∀ (i : I), IsCompact (models i)) → (∀ (i : I), (models i).Nonempty) → ∀ (Sn : ℕ → Ω → Matrix V V ℝ) (T : Matrix V V ℝ) (P : MeasureTheory.Measure Ω), (∀ (a b : V), Causalean.Stat.Tendsto_inProb (fun n ω => Sn n ω a b) (fun x => T a b) P) → ∀ (i : I), Causalean.Stat.Tendsto_inProb (fun n ω => Causalean.Stat.covarianceModelLoss (models i) (Sn n ω)) (fun x => Causalean.Stat.covarianceModelLoss (models i) T) P` | Given covariance models that are compact and nonempty, an empirical covariance sequence, a target matrix, a sampling measure, and entrywise convergence in probability, the model losses converge coordinatewise in probability. |
<!-- /GEN -->

### Rational algebraic-locus compilers

`Mathlib/AlgebraicGeometry/RationalMap.lean` clears finite rational-map equality and image-intersection conditions to real polynomial zero loci; `RationalDerivative.lean` compiles a rational scalar's zero-derivative locus.

<!-- GEN:Causalean.Mathlib.AlgebraicGeometry.RationalMap -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.AlgebraicGeometry.RationalMap` | `Type u_5 → Type u_6 → Type (max u_5 u_6)` | A finite-coordinate real rational map stores one numerator and denominator multivariate polynomial for each output coordinate. |
| `Mathlib.AlgebraicGeometry.RationalMap.eval` | `(S → ℝ) → T → ℝ` | Evaluating a rational map substitutes the source coordinates into each numerator and denominator and divides coordinatewise. |
| `Mathlib.AlgebraicGeometry.RationalMap.DefinedOn` | `Set (S → ℝ) → Prop` | A rational map is defined on a domain when every coordinate denominator is nonzero at every point of that domain. |
| `Mathlib.AlgebraicGeometry.RationalMap.ofPolynomial` | `(T → MvPolynomial S ℝ) → Causalean.Mathlib.AlgebraicGeometry.RationalMap S T` | A polynomial coordinate map is viewed as a rational map with denominator one in every coordinate. |
| `Mathlib.AlgebraicGeometry.RationalMap.eval_ofPolynomial` | `(Causalean.Mathlib.AlgebraicGeometry.RationalMap.ofPolynomial p).eval x = fun t => (MvPolynomial.eval x) (p t)` | For a polynomial coordinate map and source assignment, the denominator-one rational representation has ordinary polynomial evaluation. |
| `Mathlib.AlgebraicGeometry.RationalMap.equalityPolynomial` | `Causalean.Mathlib.AlgebraicGeometry.RationalMap S T → T → MvPolynomial S ℝ` | The cleared numerator for equality of one coordinate of two rational maps is the cross-product of their numerators and denominators. |
| `Mathlib.AlgebraicGeometry.RationalMap.eval_eq_iff_equalityPolynomial_eq_zero` | `(MvPolynomial.eval x) (f.den t) ≠ 0 → (MvPolynomial.eval x) (g.den t) ≠ 0 → (f.eval x t = g.eval x t ↔ (MvPolynomial.eval x) (f.equalityPolynomial g t) = 0)` | Given two rational maps, a source assignment, an output coordinate, and nonzero first and second denominators, the rational values agree exactly when the cleared equality polynomial vanishes. |
| `Mathlib.AlgebraicGeometry.conjunctionPolynomial` | `(T → MvPolynomial S ℝ) → MvPolynomial S ℝ` | The conjunction polynomial of finitely many real polynomials is their sum of squares. |
| `Mathlib.AlgebraicGeometry.eval_conjunctionPolynomial_eq_zero_iff` | `(MvPolynomial.eval x) (Causalean.Mathlib.AlgebraicGeometry.conjunctionPolynomial p) = 0 ↔ ∀ (t : T), (MvPolynomial.eval x) (p t) = 0` | For a finite polynomial family and source assignment, the conjunction polynomial vanishes exactly when every constituent polynomial vanishes. |
| `Mathlib.AlgebraicGeometry.conjunctionPolynomial_ne_zero_of_witness` | `(MvPolynomial.eval x) (p t) ≠ 0 → Causalean.Mathlib.AlgebraicGeometry.conjunctionPolynomial p ≠ 0` | Given a finite polynomial family, source assignment, coordinate, and a nonzero value at that coordinate, the conjunction polynomial is nonzero. |
| `Mathlib.AlgebraicGeometry.unionConjunctionPolynomial` | `(B → T → MvPolynomial S ℝ) → MvPolynomial S ℝ` | The union-of-conjunctions polynomial multiplies the sum-of-squares certificate for every branch. |
| `Mathlib.AlgebraicGeometry.eval_unionConjunctionPolynomial_eq_zero_iff` | `(MvPolynomial.eval x) (Causalean.Mathlib.AlgebraicGeometry.unionConjunctionPolynomial p) = 0 ↔ ∃ b, ∀ (t : T), (MvPolynomial.eval x) (p b t) = 0` | For a finite family of finite polynomial systems and source assignment, the union certificate vanishes exactly when one branch vanishes coordinatewise. |
| `Mathlib.AlgebraicGeometry.unionConjunctionPolynomial_ne_zero_of_witnesses` | `(∀ (b : B), (MvPolynomial.eval (witness b)) (p b (coordinate b)) ≠ 0) → Causalean.Mathlib.AlgebraicGeometry.unionConjunctionPolynomial p ≠ 0` | Given a finite polynomial-system family, branchwise witness assignments, branchwise coordinates, and nonzero witness values, the union certificate is nonzero. |
| `Mathlib.AlgebraicGeometry.rationalMap_eq_locus` | `f.DefinedOn D → g.DefinedOn D → {x \| x ∈ D ∧ f.eval x = g.eval x} = D ∩ Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus (Causalean.Mathlib.AlgebraicGeometry.conjunctionPolynomial (f.equalityPolynomial g))` | Given two finite-coordinate rational maps f and g on a common domain where the denominators of the first map do not vanish and the denominators of the second map do not vanish, the whole-output equality condition is one real polynomial zero locus. |
| `Mathlib.AlgebraicGeometry.rationalMap_eq_union_locus` | `(∀ (b : B), (f b).DefinedOn D) → (∀ (b : B), (g b).DefinedOn D) → {x \| x ∈ D ∧ ∃ b, (f b).eval x = (g b).eval x} = D ∩ Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus (Causalean.Mathlib.AlgebraicGeometry.unionConjunctionPolynomial fun b => (f b).equalityPolynomial (g b))` | Given finite families of rational maps on a common domain, with all first and second denominators nonvanishing, the union of their equality conditions is one polynomial zero locus. |
| `Mathlib.AlgebraicGeometry.RationalMatrixMap` | `Type u_5 → Type u_6 → Type u_7 → Type (max u_5 u_7 u_6)` | A rational matrix map is a rational map whose output coordinates are row-column pairs. |
| `Mathlib.AlgebraicGeometry.RationalMatrixMap.evalMatrix` | `(S → ℝ) → Matrix T U ℝ` | Evaluating a rational matrix map and reshaping its pair-indexed output gives an ordinary matrix-valued function. |
| `Mathlib.AlgebraicGeometry.evalPolynomialMatrix` | `Matrix T U (MvPolynomial S ℝ) → (S → ℝ) → Matrix T U ℝ` | Evaluating a matrix of multivariate polynomials substitutes the source point in every matrix entry. |
| `Mathlib.AlgebraicGeometry.polynomialMatrixRationalMap` | `Matrix T U (MvPolynomial S ℝ) → Causalean.Mathlib.AlgebraicGeometry.RationalMatrixMap S T U` | A polynomial matrix is represented as a rational matrix map with denominator one entrywise. |
| `Mathlib.AlgebraicGeometry.polynomialMatrixRationalMap_eval` | `(Causalean.Mathlib.AlgebraicGeometry.polynomialMatrixRationalMap A).evalMatrix x = Causalean.Mathlib.AlgebraicGeometry.evalPolynomialMatrix A x` | For a polynomial matrix and source assignment, the rational-matrix representation agrees with entrywise polynomial evaluation. |
| `Mathlib.AlgebraicGeometry.polynomialMatrixInverseRationalMap` | `Matrix T T (MvPolynomial S ℝ) → Causalean.Mathlib.AlgebraicGeometry.RationalMatrixMap S T T` | The adjugate-over-determinant representation is the rational matrix map associated with the inverse of a square polynomial matrix. |
| `Mathlib.AlgebraicGeometry.polynomialMatrixInverseRationalMap_eval` | `(MvPolynomial.eval x) A.det ≠ 0 → (Causalean.Mathlib.AlgebraicGeometry.polynomialMatrixInverseRationalMap A).evalMatrix x = (Causalean.Mathlib.AlgebraicGeometry.evalPolynomialMatrix A x)⁻¹` | Given a square polynomial matrix, source assignment, and nonzero evaluated determinant, the adjugate-over-determinant map evaluates to the matrix inverse. |
| `Mathlib.AlgebraicGeometry.polynomialMatrixInverseRationalMap_definedOn` | `(∀ x ∈ D, (MvPolynomial.eval x) A.det ≠ 0) → Causalean.Mathlib.AlgebraicGeometry.RationalMap.DefinedOn (Causalean.Mathlib.AlgebraicGeometry.polynomialMatrixInverseRationalMap A) D` | Given a square polynomial matrix, domain, and a nowhere-vanishing evaluated determinant, the inverse representation is defined on the domain. |
| `Mathlib.AlgebraicGeometry.RationalMap.renameSource` | `(S → U) → Causalean.Mathlib.AlgebraicGeometry.RationalMap U T` | Renaming the source variables of a rational map along a coordinate map renames every numerator and denominator polynomial. |
| `Mathlib.AlgebraicGeometry.RationalMap.eval_renameSource` | `(f.renameSource e).eval x = f.eval (x ∘ e)` | For a rational map, coordinate renaming, and renamed-source assignment, the renamed map evaluates as the original map on the pulled-back assignment. |
| `Mathlib.AlgebraicGeometry.RationalMap.leftLift` | `Causalean.Mathlib.AlgebraicGeometry.RationalMap (S ⊕ U) T` | The left lift of a rational map makes it depend on the left coordinates of a disjoint-sum parameter space. |
| `Mathlib.AlgebraicGeometry.RationalMap.rightLift` | `Causalean.Mathlib.AlgebraicGeometry.RationalMap (S ⊕ U) T` | The right lift of a rational map makes it depend on the right coordinates of a disjoint-sum parameter space. |
| `Mathlib.AlgebraicGeometry.sumProductDomain` | `Set (S → ℝ) → Set (U → ℝ) → Set (S ⊕ U → ℝ)` | The sum-coordinate form of a product domain requires the left and right restrictions of one assignment to lie in their respective domains. |
| `Mathlib.AlgebraicGeometry.rationalMap_imageIntersection_locus` | `f.DefinedOn D → g.DefinedOn E → {z \| z ∈ Causalean.Mathlib.AlgebraicGeometry.sumProductDomain D E ∧ f.eval (z ∘ Sum.inl) = g.eval (z ∘ Sum.inr)} = Causalean.Mathlib.AlgebraicGeometry.sumProductDomain D E ∩ Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus (Causalean.Mathlib.AlgebraicGeometry.conjunctionPolynomial (f.leftLift.equalityPolynomial g.rightLift))` | Given finite-coordinate rational maps f and g on domains, with nonvanishing denominators for the first map and the second map, the pairs of parameters at which their images meet form one polynomial zero locus. |
| `Mathlib.AlgebraicGeometry.rationalMatrixMap_imageIntersection_locus` | `Causalean.Mathlib.AlgebraicGeometry.RationalMap.DefinedOn f D → Causalean.Mathlib.AlgebraicGeometry.RationalMap.DefinedOn g E → {z \| z ∈ Causalean.Mathlib.AlgebraicGeometry.sumProductDomain D E ∧ f.evalMatrix (z ∘ Sum.inl) = g.evalMatrix (z ∘ Sum.inr)} = Causalean.Mathlib.AlgebraicGeometry.sumProductDomain D E ∩ Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus (Causalean.Mathlib.AlgebraicGeometry.conjunctionPolynomial ((Causalean.Mathlib.AlgebraicGeometry.RationalMap.leftLift f).equalityPolynomial (Causalean.Mathlib.AlgebraicGeometry.RationalMap.rightLift g)))` | Given rational matrix maps on domains, with nonvanishing denominators for both maps, the parameter pairs at which their matrix images meet form one polynomial zero locus. |
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.AlgebraicGeometry.RationalDerivative -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.AlgebraicGeometry.RationalScalar` | `Type u_2 → Type u_2` | A real rational scalar coordinate is a numerator and denominator multivariate polynomial. |
| `Mathlib.AlgebraicGeometry.RationalScalar.eval` | `(S → ℝ) → ℝ` | For a rational scalar and source assignment, the evaluated scalar is its numerator evaluation divided by its denominator evaluation. |
| `Mathlib.AlgebraicGeometry.RationalScalar.DefinedOn` | `Set (S → ℝ) → Prop` | For a rational scalar and domain, being defined on the domain means that its denominator never vanishes there. |
| `Mathlib.AlgebraicGeometry.RationalScalar.derivativeNumerator` | `S → MvPolynomial S ℝ` | For a rational scalar and source coordinate, the cleared quotient-rule numerator is the polynomial numerator of that coordinate derivative. |
| `Mathlib.AlgebraicGeometry.RationalScalar.IsFormallyNonconstant` | `Prop` | For a rational scalar, formal nonconstancy means that at least one cleared partial-derivative numerator is a nonzero polynomial. |
| `Mathlib.AlgebraicGeometry.RationalScalar.derivativePolynomial` | `MvPolynomial S ℝ` | For a rational scalar, the full derivative certificate polynomial is the sum of squares of all cleared quotient-rule partial numerators. |
| `Mathlib.AlgebraicGeometry.RationalScalar.fderiv_eq_zero_iff_derivativePolynomial_eq_zero` | `(MvPolynomial.eval x) r.den ≠ 0 → (fderiv ℝ r.eval x = 0 ↔ (MvPolynomial.eval x) r.derivativePolynomial = 0)` | Given a rational scalar, source assignment, and nonzero denominator at that assignment, the full Fréchet derivative vanishes exactly when its certificate polynomial vanishes. |
| `Mathlib.AlgebraicGeometry.RationalScalar.derivative_zero_locus` | `r.DefinedOn D → {x \| x ∈ D ∧ fderiv ℝ r.eval x = 0} = D ∩ Causalean.Mathlib.MeasureTheory.mvPolynomialZeroLocus r.derivativePolynomial` | Given a rational scalar coordinate r on a domain where its denominator does not vanish, the points where its full Fréchet derivative vanishes are exactly one real polynomial zero locus within that domain. |
| `Mathlib.AlgebraicGeometry.RationalScalar.derivativePolynomial_ne_zero_of_formallyNonconstant` | `r.IsFormallyNonconstant → r.derivativePolynomial ≠ 0` | Given a rational scalar satisfying formal nonconstancy, the full derivative certificate polynomial is nonzero. |
| `Mathlib.AlgebraicGeometry.RationalScalar.derivativePolynomial_ne_zero_of_witness` | `(MvPolynomial.eval x) (r.derivativeNumerator i) ≠ 0 → r.derivativePolynomial ≠ 0` | Given a rational scalar, source assignment, coordinate, and a nonzero cleared derivative numerator there, the full derivative certificate polynomial is nonzero. |
| `Mathlib.AlgebraicGeometry.RationalScalar.derivativePolynomial_ne_zero_of_nonconstantOn_convex` | `Convex ℝ D → r.DefinedOn D → ∀ (x y : S → ℝ), x ∈ D → y ∈ D → r.eval x ≠ r.eval y → r.derivativePolynomial ≠ 0` | Given a rational scalar on a convex domain, a nowhere-vanishing denominator, two domain points, and distinct rational values, the full derivative certificate polynomial is nonzero. |
<!-- /GEN -->

## 11. `SCM/ID/` — Backdoor / Frontdoor do-calculus assembly theorems

The do-calculus Backdoor and Frontdoor identification theorems live in
`SCM/ID/Backdoor.lean`, `SCM/ID/BackdoorCriterion.lean`, and
`SCM/ID/Frontdoor.lean` (sorry-free), with the adjustment functionals in
`SCM/ID/Adjustment.lean`. See the SCM/ID sections above for the
per-declaration tables.

### `Mathlib/MeasureTheory/Integral/UniformConvergence.lean`

Continuity of finite-measure set integration for families varying uniformly on the integration
set.

<!-- GEN:Causalean.Mathlib.MeasureTheory.Integral.UniformConvergence -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.MeasureTheory.continuous_setIntegral_of_continuous_uniformOn` | `mu K < ⊤ → ∀ (F : X → Y → E), (Continuous fun x => (UniformOnFun.ofFun {K}) (F x)) → (∀ (x : X), MeasureTheory.IntegrableOn (F x) K mu) → Continuous fun x => ∫ (y : Y) in K, F x y ∂mu` | For a measure, a finite-measure integration set, and an integrable family of functions that varies continuously in the topology of uniform convergence on that set, the corresponding set integrals vary continuously. |
<!-- /GEN -->

### `Mathlib/MeasureTheory/UnitInterval/OpenPos.lean`

Open-set positivity of Lebesgue volume on the closed real unit interval.

<!-- GEN:Causalean.Mathlib.MeasureTheory.UnitInterval.OpenPos -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.MeasureTheory.unitIntervalVolumeIsOpenPosMeasure` | `MeasureTheory.volume.IsOpenPosMeasure` | Lebesgue volume on the closed unit interval is positive on every nonempty relatively open set. |
<!-- /GEN -->

### `Mathlib/Topology/UniformConvergence/Affine.lean`

Continuity of affine paths in topologies of uniform convergence on compact sets.

<!-- GEN:Causalean.Mathlib.Topology.UniformConvergence.Affine -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Topology.continuous_uniformOnFun_affine_of_compact` | `IsCompact K → K.Nonempty → ∀ {f g : α → E}, ContinuousOn f K → ContinuousOn g K → Continuous fun t => (UniformOnFun.ofFun {K}) fun x => (1 - t) • f x + t • g x` | For a compact set that is nonempty, the affine interpolation between two endpoint functions continuous on that set is continuous in the topology of uniform convergence on the set. |
| `Mathlib.Topology.continuous_uniformOnFun_of_eq_affine_on_compact` | `IsCompact K → K.Nonempty → ∀ {f g : α → E}, ContinuousOn f K → ContinuousOn g K → ∀ (path : ℝ → α → E), (∀ (t : ℝ), ∀ x ∈ K, path t x = (1 - t) • f x + t • g x) → Continuous fun t => (UniformOnFun.ofFun {K}) (path t)` | For a compact set that is nonempty, a path that agrees there with the affine interpolation of two endpoint functions continuous on the set is continuous in the topology of uniform convergence on the set. |
<!-- /GEN -->

---

## Proof strategies for concrete DAGs

| Goal type | Recommended tactic | Notes |
|---|---|---|
| `v ∈ G.parents w` | `by decide` | Finite membership |
| `G.parents v = ∅` | `by native_decide` | Finset equality |
| `G.isRoot v` / `¬G.isRoot v` | `by native_decide` | Unfolds to `parents = ∅` |
| `G.dSep X Y Z` / `¬G.dSep X Y Z` | `by decide` | Bayes Ball is computable |
| `directlyConfounded v w` | `by decide` | Finite search |
| `v ∈ cComponentOf w` | `by native_decide` | BFS computation |
| `cComponentOf v = S` | `by native_decide` | Finset equality |
| `G.isAncestor u v` | Term-mode `.edge`/`.trans` | More informative than `decide` |
| `¬G.isAncestor v v` | `G.isAncestor_irrefl v` | Direct theorem application |
| `edgeType u v = t` | `rfl` | Definitional equality |


## 10a''''''''. `Mathlib/Analysis/AbsoluteValueMomentPriorDuality/` — absolute-value approximation and moment-prior duality

Reusable approximation-theory infrastructure for the nonsmooth function x ↦ |x| on the unit interval. It defines the intrinsic best uniform polynomial error, proves the exact dual construction of symmetric probability measures with matched polynomial moments, and establishes universal inverse-degree upper and lower bounds. The Fourier certificate is kept in a separate support module; the API module is the consumer-facing import.

### Basic approximation facts

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Basic -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.unitInterval` | `Set ℝ` | The unit interval is the closed set of real numbers from $-1$ through $1$, inclusive. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.uniformApproxErrorAbs` | `Polynomial ℝ → ℝ` | For a real polynomial, its uniform absolute-value approximation error is the supremum, over every real number in the closed interval from $-1$ through $1$, of the absolute difference between the polynomial's value and that number's absolute value. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs` | `ℕ → ℝ` | For a nonnegative integer degree bound, the best uniform absolute-value approximation error is the infimum of the uniform errors of all real polynomials whose degree is at most that bound. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.uniformApproxErrorAbs_eq_sSup` | `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.uniformApproxErrorAbs p = sSup ((fun x => \|\|x\| - Polynomial.eval x p\|) '' Set.Icc (-1) 1)` | For a real polynomial, its uniform absolute-value approximation error is the supremum of its pointwise residual on the unit interval. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.uniformApproxErrorAbs_le_iff` | `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.uniformApproxErrorAbs p ≤ e ↔ ∀ x ∈ Set.Icc (-1) 1, \|\|x\| - Polynomial.eval x p\| ≤ e` | For a real polynomial and a proposed error bound, the bound holds exactly when it bounds every residual on the unit interval. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs_eq_sInf` | `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K = sInf {e \| ∃ p, p.natDegree ≤ K ∧ e = Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.uniformApproxErrorAbs p}` | For a polynomial degree limit, the best absolute-value approximation error is the infimum over all admissible polynomial errors. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs_nonneg` | `0 ≤ Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K` | For a polynomial degree limit, the best approximation error cannot be negative. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs_antitone` | `K ≤ L → Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs L ≤ Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K` | For two degree limits with the first no larger than the second, allowing the larger degree cannot increase the best error. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.exists_bestPolynomialAbs` | `∃ p, p.natDegree ≤ K ∧ Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.uniformApproxErrorAbs p = Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K` | For a polynomial degree limit, some admissible polynomial attains the best absolute-value approximation error. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.exists_bestPolynomialAbs_interval` | `∃ p, p.natDegree ≤ K ∧ ∀ x ∈ Set.Icc (-1) 1, \|\|x\| - Polynomial.eval x p\| ≤ Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K` | For a polynomial degree limit, some admissible polynomial bounds every absolute-value residual by the best error on the unit interval. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs_two_mul_add_one` | `Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs (2 * m + 1) = Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs (2 * m)` | For a nonnegative integer, allowing the odd degree 2m+1 gives the same best error as degree 2m. |
<!-- /GEN -->

### Fourier certificate

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Fejer -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.instFactLtRealOfNatPi_causalean` | `Fact (0 < Real.pi)` | — |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.oneSidedFourierSum` | `ℕ → C(AddCircle Real.pi, ℂ)` | For a nonnegative integer order, the one-sided Fourier sum is the continuous complex-valued function on the circle obtained by summing the Fourier characters with integer frequencies from zero through one less than that order. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerKernel` | `ℕ → AddCircle Real.pi → ℝ` | For a nonnegative integer order and a point on the circle of period π, the normalized Fejér kernel is the squared complex modulus of the one-sided Fourier sum at that point, divided by the order; at order zero, this quotient is defined to be zero. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.continuous_fejerKernel` | `Continuous (Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerKernel n)` | For a Fejér order, the normalized Fejér kernel is continuous. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMean` | `ℕ → C(AddCircle Real.pi, ℂ) → ℂ` | For a nonnegative integer order and a continuous complex-valued function on the circle of period π, the Fejér mean is the Haar integral of the function multiplied by the normalized Fejér kernel of that order. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.integral_fourier` | `∫ (x : AddCircle Real.pi), (fourier k) x ∂AddCircle.haarAddCircle = if k = 0 then 1 else 0` | For a Fourier frequency, its Haar integral is one at frequency zero and zero otherwise. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejer_integrand_expand` | `↑(Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerKernel n t) * (fourier ↑k) t = (↑n)⁻¹ * ∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n, (fourier (↑r - ↑s + ↑k)) t` | For a Fejér order, Fourier frequency, and circle point, the kernel-weighted character has the stated finite Fourier expansion. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMean_fourier_nat` | `0 < n → Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMean n (fourier ↑k) = ↑(if k < n then ↑(n - k) / ↑n else 0)` | For a positive Fejér order and a nonnegative frequency, the Fejér mean has the stated triangular multiplier. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMean_fourier_neg_nat` | `0 < n → Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMean n (fourier (-↑k)) = ↑(if k < n then ↑(n - k) / ↑n else 0)` | For a positive Fejér order and a negative frequency magnitude, the Fejér mean has the same triangular multiplier. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.integral_fejerKernel` | `0 < n → ∫ (t : AddCircle Real.pi), Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerKernel n t ∂AddCircle.haarAddCircle = 1` | For a positive Fejér order, the normalized kernel integrates to one. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMean_norm_le` | `0 < n → ∀ (f : C(AddCircle Real.pi, ℂ)) (E : ℝ), (∀ (t : AddCircle Real.pi), ‖f t‖ ≤ E) → ‖Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMean n f‖ ≤ E` | For a positive Fejér order, a continuous input, and a uniform norm bound, the Fejér mean obeys that bound. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMeanCLM` | `(n : ℕ) → 0 < n → C(AddCircle Real.pi, ℂ) →L[ℂ] ℂ` | For a positive integer order, the continuous-linear Fejér mean functional maps each continuous complex-valued function on the circle of period π to its Fejér mean of that order. |
| `Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMeanCLM_apply` | `(Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMeanCLM n hn) f = Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.fejerMean n f` | For a positive Fejér order and a continuous input, the packaged linear map equals the integral definition. |
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

## 10a'''''''''''. `Mathlib/Analysis/ParametricRationalIntegralAnalyticity/` — analytic polynomial-over-affine integrals

This analysis substrate turns locally uniform denominator separation into real analyticity for finite-measure integrals with fixed-degree polynomial numerators and affine parameter denominators. It exposes the geometric-series and dominated-integration steps as reusable lower-level APIs, then provides local and open-set integral theorems plus a scalar interval example.

### API umbrella

<!-- GEN:Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity -->
_(no documented declarations in Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity)_
<!-- /GEN -->

### Definitions

<!-- GEN:Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.Definitions -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator` | `(α → ℝ) → (α → ℝ) → ℝ → α → ℝ` | Given two real-valued functions, a parameter, and an input point, the affine denominator is given by their displayed linear interpolation at that parameter. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator` | `(N : ℕ) → (Fin (N + 1) → α → ℝ) → ℝ → α → ℝ` | Given a degree bound, coefficient functions, a parameter, and an input point, the polynomial numerator is given by the displayed finite polynomial evaluated at that parameter and point. |
<!-- /GEN -->

### Affine denominator control

<!-- GEN:Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.Affine -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator_uniformly_nonzero_near` | `0 < ε → 0 ≤ L → (∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x\|) → (∀ x ∈ K, \|b x - a x\| ≤ L) → ∃ r > 0, ∀ (t : ℝ), \|t - t₀\| < r → ∀ x ∈ K, ε / 2 ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x\|` | If the separation margin is positive, the slope bound is nonnegative, the affine denominator is separated from zero at the reference parameter, and its slope is uniformly bounded on the integration set, then it remains separated from zero by half that margin on an explicit parameter neighborhood. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator_uniformly_nonzero_on_open_near` | `IsOpen O → 0 < ε → (∀ t ∈ O, ∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x\|) → ∀ {t₀ : ℝ}, t₀ ∈ O → ∃ r > 0, Metric.ball t₀ r ⊆ O ∧ ∀ t ∈ Metric.ball t₀ r, ∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x\|` | If the parameter set is open, the separation margin is positive, the affine denominator is uniformly separated from zero throughout that set and the integration set, and the reference parameter lies in the open set, then some positive ball around it stays in the parameter set and retains the same uniform separation. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator_slope_div_le_inv_radius` | `0 < r → 0 < ε → (∀ (t : ℝ), \|t - t₀\| < r → ∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x\|) → ∀ x ∈ K, \|(b x - a x) / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x\| ≤ r⁻¹` | If the parameter-ball radius and separation margin are positive and the affine denominator is uniformly separated from zero throughout that ball and the integration set, then the affine slope divided by its central denominator is bounded by the reciprocal radius. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator_uniformly_nonzero_near_of_slope_div_bound` | `0 < ε → 0 ≤ Q → (∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x\|) → (∀ x ∈ K, \|(b x - a x) / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x\| ≤ Q) → ∃ r > 0, ∀ (t : ℝ), \|t - t₀\| < r → ∀ x ∈ K, ε / 2 ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x\|` | If the separation margin is positive, the relative-slope bound is nonnegative, the central affine denominator is uniformly separated from zero, and the slope-to-denominator ratio is uniformly bounded, then the denominator remains separated by half the margin on an explicit parameter neighborhood. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator_reciprocal_eq_tsum` | `Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x ≠ 0 → \|(t - t₀) * (b x - a x) / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x\| < 1 → (Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x)⁻¹ = ∑' (n : ℕ), (-(b x - a x) / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x) ^ n / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x * (t - t₀) ^ n` | If the affine denominator at the expansion center is nonzero and the normalized affine perturbation has absolute value below one, then the reciprocal affine denominator equals its centered geometric power series. |
<!-- /GEN -->

### Dominated power-series integration

<!-- GEN:Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.PowerSeries -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.integral_eq_tsum_of_powerSeries_domination` | `0 < r → \|t - t₀\| < r → (∀ (n : ℕ), MeasureTheory.AEStronglyMeasurable (c n) μ) → (∀ (n : ℕ), 0 ≤ M n) → (∀ (n : ℕ), ∀ᵐ (x : α) ∂μ, ‖c n x‖ ≤ M n) → (Summable fun n => M n * r ^ n) → (∀ (s : ℝ), \|s - t₀\| < r → ∀ᵐ (x : α) ∂μ, f s x = ∑' (n : ℕ), c n x * (s - t₀) ^ n) → ∫ (x : α), f t x ∂μ = ∑' (n : ℕ), (∫ (x : α), c n x ∂μ) * (t - t₀) ^ n` | Given a finite measure, an integrand family, its coefficient functions, coefficient envelopes, an expansion center, radius, and evaluation parameter, a positive radius and an evaluation inside it, measurable coefficients, nonnegative envelopes, almost-everywhere coefficient domination, a summable radius-weighted envelope, and an almost-everywhere pointwise power-series expansion, the integral equals the series of coefficient integrals at the evaluation parameter. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.analyticAt_integral_of_powerSeries_domination` | `0 < r → (∀ (n : ℕ), MeasureTheory.AEStronglyMeasurable (c n) μ) → (∀ (n : ℕ), 0 ≤ M n) → (∀ (n : ℕ), ∀ᵐ (x : α) ∂μ, ‖c n x‖ ≤ M n) → (Summable fun n => M n * r ^ n) → (∀ (t : ℝ), \|t - t₀\| < r → ∀ᵐ (x : α) ∂μ, f t x = ∑' (n : ℕ), c n x * (t - t₀) ^ n) → AnalyticAt ℝ (fun t => ∫ (x : α), f t x ∂μ) t₀` | Given a finite measure, an integrand family, its coefficient functions, coefficient envelopes, an expansion center and radius, a positive radius, measurable coefficients, nonnegative envelopes, almost-everywhere coefficient domination, a summable radius-weighted envelope, and an almost-everywhere pointwise power-series expansion throughout that radius, integrating the family produces a real-analytic function at the expansion center. |
<!-- /GEN -->

### Integral analyticity API

<!-- GEN:Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.Main -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.analyticAt_setIntegral_polynomial_div_affine` | `MeasurableSet K → μ K ≠ ⊤ → ∀ (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ) (t₀ ε L : ℝ) (C : Fin (N + 1) → ℝ), 0 < ε → 0 ≤ L → (∀ (i : Fin (N + 1)), Measurable (c i)) → Measurable a → Measurable b → (∀ (i : Fin (N + 1)), ∀ x ∈ K, \|c i x\| ≤ C i) → (∀ x ∈ K, \|b x - a x\| ≤ L) → (∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x\|) → AnalyticAt ℝ (fun t => ∫ (x : α) in K, Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator N c t x / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x ∂μ) t₀` | Given a measure, a measurable integration set of finite measure, a polynomial degree, coefficient functions, and affine endpoint functions, an expansion center, positive separation margin, nonnegative slope bound, and coefficient bounds, positivity and nonnegativity of those bounds, measurability of the coefficients and endpoints, uniform coefficient and slope bounds on the integration set, and uniform separation of the central denominator from zero, the polynomial-over-affine set integral is real analytic at the expansion center. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.analyticOnNhd_setIntegral_polynomial_div_affine` | `MeasurableSet K → μ K ≠ ⊤ → ∀ (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ) (O : Set ℝ) (ε L : ℝ) (C : Fin (N + 1) → ℝ), IsOpen O → 0 < ε → 0 ≤ L → (∀ (i : Fin (N + 1)), Measurable (c i)) → Measurable a → Measurable b → (∀ (i : Fin (N + 1)), ∀ x ∈ K, \|c i x\| ≤ C i) → (∀ x ∈ K, \|b x - a x\| ≤ L) → (∀ t ∈ O, ∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x\|) → AnalyticOnNhd ℝ (fun t => ∫ (x : α) in K, Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator N c t x / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x ∂μ) O` | Given a measure, a measurable integration set of finite measure, a polynomial degree, coefficient functions, and affine endpoint functions, an open parameter set, positive separation margin, nonnegative slope bound, and coefficient bounds, openness and valid numerical bounds, measurability of the coefficients and endpoints, uniform coefficient and slope bounds on the integration set, and uniform denominator separation over the parameter and integration sets, the polynomial-over-affine set integral is real analytic throughout the open parameter set. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.analyticAt_setIntegral_polynomial_div_affine_of_slope_div_bound` | `MeasurableSet K → μ K ≠ ⊤ → ∀ (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ) (t₀ ε Q : ℝ) (C : Fin (N + 1) → ℝ), 0 < ε → 0 ≤ Q → (∀ (i : Fin (N + 1)), Measurable (c i)) → Measurable a → Measurable b → (∀ (i : Fin (N + 1)), ∀ x ∈ K, \|c i x\| ≤ C i) → (∀ x ∈ K, \|(b x - a x) / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x\| ≤ Q) → (∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t₀ x\|) → AnalyticAt ℝ (fun t => ∫ (x : α) in K, Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator N c t x / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x ∂μ) t₀` | Given a measure, a measurable integration set of finite measure, a polynomial degree, coefficient functions, and affine endpoint functions, an expansion center, positive separation margin, nonnegative relative-slope bound, and coefficient bounds, positivity and nonnegativity of those bounds, measurability of the coefficients and endpoints, a uniform coefficient bound, a uniform relative affine-slope bound, and uniform central denominator separation, the polynomial-over-affine set integral is real analytic at the expansion center. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.analyticAt_setIntegral_polynomial_div_affine_of_uniform_nonzero_near` | `MeasurableSet K → μ K ≠ ⊤ → ∀ (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ) (t₀ ε r : ℝ) (C : Fin (N + 1) → ℝ), 0 < ε → 0 < r → (∀ (i : Fin (N + 1)), Measurable (c i)) → Measurable a → Measurable b → (∀ (i : Fin (N + 1)), ∀ x ∈ K, \|c i x\| ≤ C i) → (∀ (t : ℝ), \|t - t₀\| < r → ∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x\|) → AnalyticAt ℝ (fun t => ∫ (x : α) in K, Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator N c t x / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x ∂μ) t₀` | Given a measure, a measurable integration set of finite measure, a polynomial degree, coefficient functions, and affine endpoint functions, a center, positive separation margin and radius, and coefficient bounds, positive numerical bounds, measurability of the coefficients and endpoints, a uniform coefficient bound, and uniform denominator separation throughout the parameter ball, the polynomial-over-affine set integral is real analytic at the ball center. |
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.analyticOnNhd_setIntegral_polynomial_div_affine_of_uniform_nonzero` | `MeasurableSet K → μ K ≠ ⊤ → ∀ (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ) (O : Set ℝ) (ε : ℝ) (C : Fin (N + 1) → ℝ), IsOpen O → 0 < ε → (∀ (i : Fin (N + 1)), Measurable (c i)) → Measurable a → Measurable b → (∀ (i : Fin (N + 1)), ∀ x ∈ K, \|c i x\| ≤ C i) → (∀ t ∈ O, ∀ x ∈ K, ε ≤ \|Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x\|) → AnalyticOnNhd ℝ (fun t => ∫ (x : α) in K, Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator N c t x / Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator a b t x ∂μ) O` | Given a measure, a measurable integration set of finite measure, a polynomial degree, coefficient functions, and affine endpoint functions, an open parameter set, a positive separation margin, and coefficient bounds, openness and positivity, measurability of the coefficients and endpoints, a uniform coefficient bound, and uniform denominator separation throughout the parameter and integration sets, the polynomial-over-affine set integral is real analytic throughout the open parameter set. |
<!-- /GEN -->

### Scalar example

<!-- GEN:Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.Examples -->
| Decl | Signature | Description |
|---|---|---|
| `Mathlib.Analysis.ParametricRationalIntegralAnalyticity.analyticOnNhd_integral_one_add_tx_div_two_add_tx` | `AnalyticOnNhd ℝ (fun t => ∫ (x : ℝ) in Set.Icc 0 1, (1 + t * x) / (2 + t * x)) (Set.Ioo (-1) 1)` | The scalar integral of one plus the parameter times the integration variable, divided by two plus that product, is real analytic on the open interval from minus one to one. |
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

## Mathlib/Probability/CertifiedFiniteMarkovExpectation — certified finite-state Markov expectations

This module family supplies exact-rational certificates for finite Markov kernels: Gaussian threshold probabilities, interval matrix recurrences, contraction and minorization bounds, stationary reward enclosures, and strict policy comparisons.

<!-- GEN:Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.Main -->
_(no documented declarations in Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.Main)_
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
