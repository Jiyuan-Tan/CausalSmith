module
public import Causalean.Graph.AcyclicConstruct
public import Causalean.Graph.Density.FiniteDAG.Positive.Finite
public import Causalean.Stat.FinitePositiveTable.Fixing
public import Causalean.Stat.FinitePositiveTable.TwoRow

/-!
# Positive finite DAG tables and arrowhead removal

This module packages a strictly positive finite table together with normalized parent-local
DAG factors.  It also defines the graph and algebraic objects used by coordinate fixing: the
product of the factors not yet fixed, parent-conditioned fixing steps, and the DAG obtained by
removing every arrowhead into a fixed vertex.

The package deliberately reuses `FinitePositiveTable` for profiles, fibre sums, marginals, and
fixing, and `PositiveFiniteDAGMechanism` for normalized local factors.
-/

@[expose] public section

open Finset
open scoped BigOperators

noncomputable section

namespace Causalean.Stat.FinitePositiveTable.DAG

open Causalean.Graph
open Causalean.Graph.FiniteDensity
open Causalean.Stat.FinitePositiveTable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}

/-- A [DAG](hyp:G) and [strictly positive finite table](hyp:p) have [a normalized
parent-local factorization](hyp:cardinalitiesPositive,mechanism,mass_eq_jointMass) when every
coordinate has at least one state, each vertex carries a strictly positive local factor that
depends only on the vertex and its parents and sums to one over the vertex's own value, and the
table mass of every complete profile is the product of all the local factors at that profile. -/
structure PositiveDAGTableFactorization (G : DAG V) (p : PositiveTable r) where
  /-- Every coordinate alphabet contains at least one state. -/
  cardinalitiesPositive : CardinalitiesPositive r
  /-- The normalized, strictly positive, parent-local factors. -/
  mechanism : PositiveFiniteDAGMechanism G (fun v ↦ Fin (r v))
  /-- The table mass is the product of the local factors. -/
  mass_eq_jointMass : ∀ x, p.mass x = mechanism.jointMass x

namespace PositiveDAGTableFactorization

variable {G : DAG V} {p : PositiveTable r}

/-- A [factorized table](hyp:fac) and [fixed vertex set](hyp:fixed) determine [the truncated
product kernel](goal) [by multiplying, at each complete profile, exactly the local factors of the vertices outside
the fixed set](step:1). -/
def remainingFactorKernel (fac : PositiveDAGTableFactorization G p)
    (fixed : Finset V) : Kernel r :=
  fun x ↦ ∏ v ∈ (Finset.univ \ fixed), fac.mechanism.factor v x

/-- A [DAG](hyp:G) and [vertex list](hyp:vertices) determine [the parent-conditioned fixing
steps](goal) [by pairing each listed vertex, in order, with its DAG parent set as the conditioning
set](step:1). -/
def parentFixingSteps (G : DAG V) (vertices : List V) : List (FixingStep V) :=
  vertices.map fun v ↦ ⟨v, G.parents v⟩

/-- A [DAG](hyp:G), [vertex list](hyp:vertices), and [proof that the vertices are distinct](hyp:hvertices)
give [a valid parent-conditioned fixing sequence: the fixed coordinates are distinct and no step
conditions on its own coordinate](goal). -/
theorem parentFixingSteps_valid (G : DAG V) (vertices : List V)
    (hvertices : vertices.Nodup) :
    FixingSequenceValid (parentFixingSteps G vertices) := by
  /-
  Unfold both definitions.  Mapping `FixingStep.coordinate` over the constructed list is
  definitionally `vertices`; the second conjunct is `v ∉ G.parents v`, which follows from
  `DAG.irrefl` through `DAG.mem_parents`.
  -/
  constructor
  · simpa [parentFixingSteps, List.map_map, Function.comp_def] using hvertices
  · intro s hs
    simp only [parentFixingSteps, List.mem_map] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    exact fun h ↦ G.irrefl v (G.mem_parents.mp h)

/-- A [DAG](hyp:G) and [fixed vertex set](hyp:fixed) determine [the DAG with incoming arrows to
fixed vertices removed](goal): [an edge remains exactly when its target is unfixed](step:1),
[edge decidability is inherited](step:2), and [acyclicity is preserved](step:3). -/
def arrowheadRemovedDAG (G : DAG V) (fixed : Finset V) : DAG V where
  edge u v := G.edge u v ∧ v ∉ fixed
  decEdge := inferInstance
  acyclic := by
    intro v hcycle
    exact G.acyclic v ((Relation.TransGen.mono
      (r := fun u v ↦ G.edge u v ∧ v ∉ fixed) (p := G.edge)
      (fun _ _ h ↦ h.1)) v v hcycle)

/-- A [DAG](hyp:G), [fixed vertex set](hyp:fixed), and [ordered vertex pair](hyp:u,v) satisfy
[the exact edge-survival criterion after arrowhead removal](goal). -/
@[simp] theorem arrowheadRemovedDAG_edge_iff (G : DAG V) (fixed : Finset V) (u v : V) :
    (arrowheadRemovedDAG G fixed).edge u v ↔ G.edge u v ∧ v ∉ fixed := by
  rfl

/-- A [DAG](hyp:G), [fixed vertex set](hyp:fixed), and [proof that a vertex is fixed](hyp:hv)
give [an empty parent set for that vertex after arrowhead removal](goal). -/
theorem arrowheadRemovedDAG_fixed_parents_empty (G : DAG V) (fixed : Finset V)
    {v : V} (hv : v ∈ fixed) :
    (arrowheadRemovedDAG G fixed).parents v = ∅ := by
  ext u
  simp [DAG.mem_parents, hv]

/-- A [DAG](hyp:G), [fixed vertex set](hyp:fixed), and [proof that a vertex remains random](hyp:hv)
give [the original parent set for that vertex after arrowhead removal](goal). -/
theorem arrowheadRemovedDAG_random_parents (G : DAG V) (fixed : Finset V)
    {v : V} (hv : v ∉ fixed) :
    (arrowheadRemovedDAG G fixed).parents v = G.parents v := by
  ext u
  simp [DAG.mem_parents, hv]

/-- A [fixed vertex set](hyp:fixed) has [no vertex in common with its remaining complement](goal). -/
theorem fixed_disjoint_remaining (fixed : Finset V) :
    Disjoint fixed (Finset.univ \ fixed) := by
  rw [Finset.disjoint_left]
  intro v hvFixed hvRemaining
  exact (Finset.mem_sdiff.mp hvRemaining).2 hvFixed

end PositiveDAGTableFactorization

end Causalean.Stat.FinitePositiveTable.DAG
