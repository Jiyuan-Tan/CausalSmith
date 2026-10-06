/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Optimization.Affine.SignCell.CommonSlack
public import Causalean.Mathlib.Optimization.Affine.SignCell.Extrema
public import Causalean.Mathlib.Optimization.Affine.SignCell.Polynomial
public import Causalean.Mathlib.Optimization.Affine.SignCell.Example

/-! # Affine sign-cell result bundle

This auxiliary roll-up groups the common-slack criterion, extrema invariance, degree-one
polynomial compilation, and the mixed-inequality example. The canonical entry point for the
complete affine sign-cell API is `Causalean.Mathlib.Optimization.Affine.SignCell`.
-/

public section
