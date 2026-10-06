/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.API
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.Basic
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.CircleSchedule
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.ComplexExp
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.ContourEvaluation
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.ContourProgram
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.IntervalExp
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.Names
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.Program
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.Rectangles
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.Transcendental
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.TrigNames

/-!
Certified interval evaluation of complex contour integrals, with rectangle and circle schedules and rigorous transcendental-function bounds. It supports numerical complex analysis with explicit error guarantees.
-/

public section
