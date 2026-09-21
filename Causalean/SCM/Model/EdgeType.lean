/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.DAG

/-! # Edge Type Hierarchy

This file records functional restrictions that may be attached to directed edges in
a causal graph, including nonparametric, monotone, linear, and parametric cases.
The hierarchy is separate from the probabilistic semantics of structural causal
models and is used to track functional assumptions.

## Main definitions

* `MonotonicityKind` records the four monotonicity directions.
* `EdgeType` classifies an edge as nonparametric, monotone, linear, or
  parametrically restricted.
* `EdgeType.refinesBool` and `EdgeType.refines` encode the assumption-refinement
  order in which every edge type refines the nonparametric top element.
* `EdgeTypeAssignment` attaches an `EdgeType` label to each ordered edge slot of
  a directed acyclic graph, with `EdgeTypeAssignment.allNonparametric` as the
  default assignment.
-/

@[expose] public section

open Causalean.Graph


namespace Causalean

namespace SCM.Model

/-- [A monotonicity classification](goal) is one of
[nondecreasing](hyp:nonDecreasing), [nonincreasing](hyp:nonIncreasing),
[strictly increasing](hyp:strictlyIncreasing), or
[strictly decreasing](hyp:strictlyDecreasing).

    From the tex: "Monotonic: non-increasing, non-decreasing,
    strictly increasing, or strictly decreasing." -/
inductive MonotonicityKind
  | nonDecreasing
  | nonIncreasing
  | strictlyIncreasing
  | strictlyDecreasing
  deriving DecidableEq

/-- [An edge-type classification](goal) is either
[nonparametric](hyp:nonparametric),
[monotonic with a specified monotonicity classification](hyp:monotonic),
[linear](hyp:linear), or [parametric](hyp:parametric).

    For any two edge-type classifications, the derived equality procedure decides
whether the first classification is equal to the second.

    From the tex (Section 2):
    1. Nonparametric: no assumption on the structural equation.
    2. Monotonic: with a specified monotonicity kind.
    3. Parametric: linear, or another named parametric family.

    `Parametric` is an opaque tag in this layer; downstream developments can
    refine it with a concrete family when they need one. -/
inductive EdgeType
  | nonparametric
  | monotonic (kind : MonotonicityKind)
  | linear
  | parametric
  deriving DecidableEq

end SCM.Model

namespace EdgeType

/-- For two edge-type assumptions, [the Boolean refinement indicator](goal) is true
exactly when the first assumption is at least as restrictive as the second: every assumption
refines the nonparametric class, matching monotonicity kinds refine one another, and linear or
parametric classes refine only their respective matching classes.

    Nonparametric is the weakest assumption: every edge type refines it. A
    linear edge refines the linear and nonparametric classes, but it is not
    automatically monotone: without a sign restriction on its coefficient, the
    linear structural function need not be strictly increasing. Returns `Bool`
    for decidability; use `refines` for the `Prop` version. -/
def refinesBool : SCM.Model.EdgeType → SCM.Model.EdgeType → Bool
  | _, .nonparametric => true
  | .monotonic k₁, .monotonic k₂ => k₁ == k₂
  | .linear, .linear => true
  | .parametric, .parametric => true
  | _, _ => false

/-- For [two edge-type assumptions](hyp:e₁,e₂), [the refinement relation](goal) holds exactly
when their Boolean refinement indicator is true; thus the first assumption is at least as
restrictive as the second.

    Nonparametric is the weakest assumption: every edge type refines it. -/
def refines (e₁ e₂ : SCM.Model.EdgeType) : Prop := refinesBool e₁ e₂ = true

/-- For [each first edge-type assumption](hyp:e₁) and
[each second edge-type assumption](hyp:e₂),
[a decision procedure for whether the first refines the second](goal) is provided. -/
instance decRefines (e₁ e₂ : SCM.Model.EdgeType) : Decidable (refines e₁ e₂) :=
  inferInstanceAs (Decidable (_ = true))

/-- Every edge-type assumption refines itself. -/
theorem refines_refl : (e : SCM.Model.EdgeType) → refines e e
  | .nonparametric => rfl
  | .monotonic k => by cases k <;> rfl
  | .linear => rfl
  | .parametric => rfl

/-- [Every edge-type functional-form assumption `e`](hyp:e) [refines the
nonparametric assumption](goal): nonparametric is the weakest assumption in the
refinement order, so every other assumption is at least as specific as it. -/
theorem refines_nonparametric (e : SCM.Model.EdgeType) : refines e .nonparametric := by
  cases e <;> simp [refines, refinesBool]

end EdgeType

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace SCM.Model

/-- An edge type assignment attaches [a functional-assumption label to each directed edge of a
graph](hyp:edgeType).

    An edge type assignment for a DAG: a function that assigns an `EdgeType`
    to each directed edge.

    From the tex remark: "Edge types (nonparametric, monotonic, linear) can be
    encoded via a function edgeType : E → EdgeType that assigns a type to each
    edge." -/
structure EdgeTypeAssignment (G : DAG V) where
  /-- The edge type of each directed edge `(u, v)`.
      Only meaningful when `G.edge u v` holds. -/
  edgeType : V → V → EdgeType

end SCM.Model

namespace EdgeTypeAssignment

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : DAG V}

/-- For [a directed acyclic graph](hyp:G), [the all-nonparametric edge-type assignment](goal)
labels every ordered pair of its vertices as nonparametric. -/
def allNonparametric (G : DAG V) : SCM.Model.EdgeTypeAssignment G where
  edgeType := fun _ _ => .nonparametric

/-- For [an edge-type assignment](hyp:a) and [a vertex](hyp:v) in its graph, [the incoming
edge-type set](goal) is the finite set of labels assigned to all parents of that vertex. -/
def incomingTypes (a : SCM.Model.EdgeTypeAssignment G) (v : V) :
    Finset SCM.Model.EdgeType :=
  (G.parents v).image (fun u => a.edgeType u v)

/-- For [an edge-type assignment](hyp:a), [full nonparametricity](goal) holds exactly when, for
every ordered pair of vertices joined by a directed edge, the assigned label is nonparametric. -/
def isFullyNonparametric (a : SCM.Model.EdgeTypeAssignment G) : Prop :=
  ∀ u v, G.edge u v → a.edgeType u v = .nonparametric

/-- For
[a finite decidable vertex set and a directed acyclic graph](hyp:V,G)
and [an edge-type assignment on that graph](hyp:a),
[a decision procedure for whether every directed edge has the nonparametric label](goal)
is provided. -/
instance decIsFullyNonparametric (a : SCM.Model.EdgeTypeAssignment G) :
    Decidable (isFullyNonparametric a) :=
  inferInstanceAs (Decidable (∀ u v, G.edge u v → _))

end EdgeTypeAssignment

end Causalean
