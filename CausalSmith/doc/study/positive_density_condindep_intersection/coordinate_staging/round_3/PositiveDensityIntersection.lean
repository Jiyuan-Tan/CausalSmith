/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Positive-density graphoid intersection

Re-exports the measure-level and finite-coordinate forms of graphoid intersection:
under a strictly positive product density, two conditional-independence statements with
interchanged conditioning blocks imply independence from their joint block.
-/

import Causalean.Mathlib.CondIndep.PositiveDensityIntersection.Main
import Causalean.Mathlib.CondIndep.PositiveDensityIntersection.FiniteCoordinates

/-! # Positive-Density Intersection for Conditional Independence

This module packages a graph-independent graphoid intersection theorem.  A finite law with a
strictly positive density relative to a product reference measure turns the two conditional
independence statements that condition on alternate blocks into independence from their combined
block.  It also exports the finite-coordinate projection specialization, whose explicit
pairwise-disjointness assumptions prevent repeated-coordinate degeneracies.
-/
