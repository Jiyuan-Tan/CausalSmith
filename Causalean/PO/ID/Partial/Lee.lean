/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.PO.ID.Partial.Lee.Main

/-! # Lee Bounds

Lee's trimming bounds for a treatment effect under sample selection, with a binary treatment and
an outcome observed only for selected units. The always-selected units are those who would be
selected whether treated or not; under monotone selection the selected controls are exactly the
always-selected, while the selected treated are a mixture of always-selected and
helped-into-selection units. Trimming the selected-treated outcome distribution by the ratio of
the two selection probabilities, from above and from below, therefore brackets the
always-selected mean of the treated potential outcome.

The final theorem is `POLeeSystem.lee_bounds_ATT_AS`: under consistency, pair-level random
assignment, selected-cell positivity, integrability, monotone selection, and a finite support
`𝒴` for the observed outcome of selected treated units, the average treatment effect among
always-selected units lies between `lowerTrimMean 𝒴 - m0` and `upperTrimMean 𝒴 - m0`, where `m0`
is the observed mean outcome of selected controls. Only this finite-support form is proved; no
quantile form of the trimmed means is given.

## Main results

* `m0_eq_eventCondExp_Y0_alwaysSelected` — the selected-control mean is the always-selected
  mean of the untreated potential outcome.
* `trimmed_bounds_condExp_Y1_AS` — the trimmed means bracket the always-selected mean of the
  treated potential outcome.
* `lee_bounds_ATT_AS` — the Lee bound on the always-selected treatment effect.
-/
