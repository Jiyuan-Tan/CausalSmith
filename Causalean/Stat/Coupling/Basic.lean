/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Coupling predicate

This module defines the shared predicate for a probability measure whose two
marginals are prescribed. It is polymorphic in both measurable spaces so that
coupling constructions throughout the statistical library can use one common
interface.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory

universe u v

/-- For [measurable spaces `α` and `β`](hyp:α,β), [a measure `π` on their
product and proposed marginal measures `μ` and `ν`](hyp:π,μ,ν), `π` is a
coupling of `μ` and `ν` when it is a probability measure and its first
and second marginals are respectively `μ` and `ν`. -/
structure IsCoupling {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    (π : Measure (α × β)) (μ : Measure α) (ν : Measure β) : Prop where
  /-- A coupling is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure π
  /-- The first marginal of `π` is `μ`. -/
  map_fst : π.map Prod.fst = μ
  /-- The second marginal of `π` is `ν`. -/
  map_snd : π.map Prod.snd = ν

end Causalean.Stat
