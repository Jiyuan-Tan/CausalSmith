/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-way fixed-effect subspace

For `c : Cells I T`, the **two-way fixed-effect subspace** `H_twfe` is the
linear subspace of `(I × T) → ℝ` consisting of arrays of the form
`h (i, t) = a i + b t` for some `a : I → ℝ` and `b : T → ℝ`.

`H_twfe` is a thin specialization of the generic two-axis additive span
`Causalean.Stat.Weighted.twoAxisAdditiveSpan I T`
(itself `Causalean.Stat.Weighted.AdditiveSpan (Prod.fst) (Prod.snd)`).
All algebraic properties (constants membership, finite-dimensionality)
are inherited from the generic API.

## Main definitions

* `Cells.H_twfe : Submodule ℝ ((I × T) → ℝ)` — the two-way fixed-effect
  subspace, defined as `Causalean.Stat.Weighted.twoAxisAdditiveSpan I T`.

## Main lemmas

* `Cells.const_mem_H_twfe` — constants are in `H_twfe`.
* `Cells.H_twfe_finiteDimensional` — `H_twfe` is finite-dimensional.
-/

module
public import Causalean.Panel.Subspace
public import Causalean.Stat.Weighted.AdditiveSpan

/-! # Two-Way Fixed Effects

This file defines the two-way fixed-effect subspace of panel arrays as the set
of unit-plus-period additive functions. It connects the panel notation to the
generic additive-span infrastructure and records basic membership and
finite-dimensionality facts. -/

@[expose] public section

open scoped BigOperators

namespace Causalean
namespace Panel
namespace Cells

variable {I T : Type*}

/-- The two-way fixed-effect subspace.

`h ∈ H_twfe` iff there exist `a : I → ℝ` and `b : T → ℝ` such that
`h (i, t) = a i + b t` for all `(i, t)`.

Definitionally equal to `Causalean.Stat.Weighted.twoAxisAdditiveSpan I T`. -/
def H_twfe : Submodule ℝ (V I T) :=
  Causalean.Stat.Weighted.twoAxisAdditiveSpan I T

/-- [The two-way fixed-effect subspace `H_twfe` equals the generic two-axis additive span over
units and periods](goal). -/
lemma H_twfe_eq :
    H_twfe = Causalean.Stat.Weighted.twoAxisAdditiveSpan I T := rfl

/-- For [any constant `c₀`](hyp:c₀), [the constant array `c₀` belongs to the two-way
fixed-effect subspace `H_twfe`](goal).

Delegates to `AdditiveSpan.const_mem`. -/
lemma const_mem_H_twfe (c₀ : ℝ) :
    (fun _ : I × T => c₀) ∈ H_twfe :=
  Causalean.Stat.Weighted.AdditiveSpan.const_mem (Prod.fst : I × T → I) Prod.snd c₀

variable [Finite I] [Finite T] [DecidableEq I] [DecidableEq T]

/-- `H_twfe` is finite-dimensional: inherits from
`AdditiveSpan.finiteDimensional`. -/
instance H_twfe_finiteDimensional :
    Module.Finite ℝ (H_twfe (I := I) (T := T)) :=
  Causalean.Stat.Weighted.AdditiveSpan.finiteDimensional

end Cells
end Panel
end Causalean
