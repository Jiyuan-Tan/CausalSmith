/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.Bounds
public import Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.Attainment

/-!
# Sharp residual envelope for bounded outcomes

Among all probability laws `μ` on `[0, 1]` with second moment `∫ y² dμ = v²`, how large can the
residual variance of regressing `y²` on `(1, y)` be? For every `v ∈ (0, 1)` the supremum of this
L² projection residual equals the closed form

    ρ(v) = (μᵥ − v²)(v² − μᵥ²) / (4 μᵥ (1 − μᵥ)),

where `μᵥ` is the unique root in `(v², v)` of the first-order-condition quartic, and the supremum
is attained by an extremal three-point law.

## Main results

* `rho_envelope_isLUB` — `rhoEnvelope v` is the least upper bound of `residualSet v`, the set of
  residuals `l2ResidualQuadratic μ` over admissible laws `μ` (proved in this file).
* `l2ResidualQuadratic_le_rho` — the upper bound: every admissible residual is at most `ρ(v)`.
* `rho_envelope_attained` — an admissible law with residual exactly `ρ(v)`.
* `interior_quartic_unique_root` — existence and uniqueness of `μᵥ`.

The least-upper-bound statement combines the upper bound with attainment. The residual
`l2ResidualQuadratic μ` is the closed-form expression in the first four raw moments; its
identification with the minimized L² distance is in `ResidualQuadratic.MeasureBridge`.
-/

public section

namespace Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope

open Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge (l2ResidualQuadratic)
open MeasureTheory

/-- **Measure-level sharp envelope (`IsLUB`).** For [`v` strictly between `0` and `1`](hyp:hv0,hv1),
[`rhoEnvelope v` is the least upper bound of the set of residuals `l2ResidualQuadratic μ` over
admissible laws `μ`](goal).  Equivalently: the sup over all probability measures on `[0,1]` with
`∫ y² ∂μ = v²` of the `L²` residual of `y²` on `span{1, y}` equals the closed form `ρ(v)`, and is
attained (by the extremal three-point law). -/
theorem rho_envelope_isLUB (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    IsLUB (residualSet v) (rhoEnvelope v) := by
  constructor
  · -- `rhoEnvelope v` is an upper bound of the residual set
    rintro r ⟨μ, hμ, rfl⟩
    exact l2ResidualQuadratic_le_rho v μ hμ hv0 hv1
  · -- and it is the least such: any upper bound dominates the attained value
    intro b hb
    obtain ⟨μ, hμ, hres⟩ := rho_envelope_attained v hv0 hv1
    exact hb ⟨μ, hμ, hres.symm⟩

end Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope
