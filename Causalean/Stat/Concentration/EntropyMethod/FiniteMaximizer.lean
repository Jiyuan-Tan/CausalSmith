/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.MeasureTheory.FiniteMaximizer

/-! # Measurable maximizers over a finite class

A measurable selection of the maximizer of finitely many real-valued measurable functions. For a
nonempty finite index set and one measurable score function per index, `finiteClassMaximizer`
picks, at each point, an index whose score is largest, breaking ties by a fixed enumeration; the
selected index is a measurable function of the point (`measurable_finiteClassMaximizer`) and its
score dominates every other score (`finiteClassMaximizer_spec`). Concentration arguments use
it to write the supremum of a finite class as the value at a measurable random index.

The declarations live in `Causalean.Mathlib.MeasureTheory.FiniteMaximizer`; this file declares
nothing and makes them available under the concentration-theory path.
-/
