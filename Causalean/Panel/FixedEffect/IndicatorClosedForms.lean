/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# TWFE residualization closed forms for structured indicators

For `c : Cells I T` and an indicator array `A : I × T → ℝ` of a structured
predicate, this file collects closed-form expressions for the TWFE residual
`c.tildeX c.H_twfe A` on the observed cells.

The lemmas here are reusable substrate for staggered-adoption and event-study
panel regressions, and are stated generically against `Cells` plus an explicit
cohort-period weights construction (`cohortPeriodCells`). The construction is
defined locally to keep the dependency graph clean: `IndicatorClosedForms` does
not import any Q-instance file.

## Contents

### Trivial absorption (residual = 0; member of `H_twfe`)

* `tildeX_const` — constants.
* `tildeX_unit_indicator` — unit-only indicators `ind(i = i₀)`.
* `tildeX_period_indicator` — period-only indicators `ind(t = t₀)`.

These are independent of the weights: any `Cells I T`.

### Substantive closed forms (residual ≠ 0; not in `H_twfe`)

* `tildeX_product_indicator_balanced` — product `1_{S_I}(i) · 1_{S_T}(t)`
  under balanced weights factorizes into the product of demeaned indicators.
* `cohortPeriodCells` — generic `Cells` instance with all cohort-period cells
  observed and weights `π(g) / S`.
* `tildeX_cell_indicator_cohortPeriod` — cell `ind(g = g₀ ∧ t = t₀)`.
* `tildeX_diagonal_indicator_cohortPeriod` — staggered diagonal
  `ind(g.val = t.val)`.
* `tildeX_triangular_indicator_cohortPeriod` — staggered triangular
  `ind(g.val < t.val)`.

The substantive proofs all use the same pattern: exhibit the finite
unit-plus-period projection candidate, verify the two row/column normal
equations, and conclude by `proj_apply_eq_of_mem_orthogonal`.
-/

module
public import Causalean.Panel.FixedEffect.IndicatorClosedForms.Basic
public import Causalean.Panel.FixedEffect.IndicatorClosedForms.CohortPeriod
public import Causalean.Panel.FixedEffect.IndicatorClosedForms.Staggered

/-! # Indicator Residual Closed Forms

This file proves closed-form two-way fixed-effect residuals for structured
indicator arrays, including unit-only, period-only, rectangular, cohort-period,
diagonal, and triangular indicators. It also provides the exported
row-and-column orthogonality criterion `H_twfe_orthogonal_iff`, the finite
cohort law `CohortLaw`, and the generic cohort-period weighted panel
construction `cohortPeriodCells`, so downstream files can reuse the algebra
without importing a specialized regression instance. -/
