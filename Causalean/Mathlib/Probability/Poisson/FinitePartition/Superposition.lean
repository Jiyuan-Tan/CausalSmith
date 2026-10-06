/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Superposition.Canonical
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Superposition.Retention

/-!
Superposition and retention laws for marked Poisson samples on finite partitions. They describe
how independent cell configurations combine and how a smallest-mark prefix recovers an i.i.d.
sample conditional on a sufficient count.
-/

public section
