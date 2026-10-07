/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual

/-!
# Residual variance of regressing y² on (1, y)

For a probability law `μ` on the real line with finite fourth moment, the minimal mean squared
error of approximating `y²` by an affine function of `y`,

    r(μ) = min over (b₀, b₁) of ∫ (y² − b₀ − b₁ y)² dμ,

has the closed form `(m₄ − m₂²) − (m₃ − m₁ m₂)² / (m₂ − m₁²)` in the raw moments `mₖ = ∫ yᵏ dμ`
when the variance is positive. The minimizing residual function `q(y) = y² − b₀* − b₁* y` is
orthogonal to `1` and to `y`, and its squared L² norm equals `r(μ)`.

## Main definitions and results

* `MomentAlgebra` — the algebra in moment coordinates: `momentResidual`, and the conditional envelope
  bound `momentResidual_le_envelope` used for bounded outcomes.
* `MeasureBridge` — `l2ResidualQuadratic` (the closed form for a measure), `optIntercept`,
  `optSlope`; `residualQuad_opt_eq` and `l2ResidualQuadratic_le` (the closed form is attained at
  the optimal coefficients and is a lower bound for every affine fit); `iInf_residualQuad`.
* `ProjectionResidual` — `projResidual` with `integral_projResidual`,
  `integral_id_mul_projResidual` (orthogonality to `1` and `y`), `integral_sq_projResidual`
  (`∫ q² dμ = r(μ)`) and `integral_sq_mul_projResidual`.
-/

public section
