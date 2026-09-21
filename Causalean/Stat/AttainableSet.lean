/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Data.Real.Basic

/-! # Identified sets

This file defines the identified set of a real-valued objective as the set
of values attained over its feasible parameter set; it need not be an interval. The definition is
shared by
potential-outcome and structural-causal-model partial identification results.
-/

@[expose] public section

namespace Causalean
namespace Stat
namespace AttainableSet

/-- For [a parameter space](hyp:α), [an objective function](hyp:obj), and [a feasibility
condition on its parameter values](hyp:feasible), the [identified set](goal) is the set of
all objective values attained by feasible parameters. -/
noncomputable def IdentifiedSet {α : Type*} (obj : α → ℝ) (feasible : α → Prop) : Set ℝ :=
  Set.range (fun x : {x // feasible x} => obj x)

/-- Deprecated former name of `IdentifiedSet`. -/
@[deprecated (since := "2026-09-16")] alias IdentifiedInterval := IdentifiedSet

end AttainableSet
end Stat
end Causalean
