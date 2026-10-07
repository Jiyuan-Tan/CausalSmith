/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Optlib.Optimality.Constrained_Problem
public import Optlib.Convex.Farkas

/-!
# First-order KKT optimality conditions

First-order Karush–Kuhn–Tucker necessary conditions for a smooth constrained optimization
problem on ℝⁿ with finitely many equality and inequality constraints, taken from the vendored
optlib development. At a local minimizer satisfying a constraint qualification there exist
Lagrange multipliers for which the Lagrangian is stationary, the inequality multipliers are
nonnegative (dual feasibility), and complementary slackness holds. Only the necessary direction
is available; convex sufficiency and Slater-type qualifications are not part of the vendored
development.

## Main results

* `first_order_neccessary_general` — the KKT conditions when the linearized feasible directions
  coincide with the tangent cone of the feasible set at the minimizer (an Abadie-type
  qualification), for a differentiable objective and continuously differentiable constraints.
* `first_order_neccessary_LICQ` — the same conclusion under the linear-independence constraint
  qualification, for a problem whose domain is the whole space.
* `first_order_neccessary_LinearCQ` — the same conclusion when the active constraints are
  affine, for a problem whose domain is the whole space.
* `Farkas` — Farkas' lemma for finite families of vectors in ℝⁿ: a vector is a combination of
  the equality vectors plus a nonnegative combination of the inequality vectors if and only if no
  direction orthogonal to the former and nonnegative on the latter has negative inner product
  with it.

This file declares nothing of its own; the theorems keep their optlib names in the root namespace.
-/

public section

namespace Causalean.Mathlib.Optimization

end Causalean.Mathlib.Optimization
