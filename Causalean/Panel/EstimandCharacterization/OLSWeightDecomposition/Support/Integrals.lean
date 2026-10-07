/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition.Support.Basic

/-! # Finite-cell integral helpers

This module re-exports the finite-cell integral identities alongside their
saturated-control definitions in `Support.Basic`. Orthogonality against finite
linear combinations of cell indicators is provided by the shared
`CellBridge.integral_mul_indicatorSpan_eq_zero_of_cell` theorem. -/

public section
