/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Optimization.Affine.SignCell.Basic
public import Causalean.Mathlib.Optimization.Affine.SignCell.Closure
public import Causalean.Mathlib.Optimization.Affine.SignCell.CommonSlack
public import Causalean.Mathlib.Optimization.Affine.SignCell.Example
public import Causalean.Mathlib.Optimization.Affine.SignCell.Extrema
public import Causalean.Mathlib.Optimization.Affine.SignCell.Main
public import Causalean.Mathlib.Optimization.Affine.SignCell.Polynomial

/-!
Optimization over regions determined by affine sign restrictions, including closure, common-slack, extrema, and polynomial formulations. These results organize piecewise-affine optimization problems into tractable cells.
-/

public section
