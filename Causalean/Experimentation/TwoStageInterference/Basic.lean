/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.TwoStage

/-! # Hudgens–Halloran (2008): two-stage interference setup, estimands, estimators

This file formalizes the design layer for Hudgens & Halloran (2008), "Toward Causal Inference With
Interference."  The population is partitioned into groups; each unit's potential outcome may depend
on treatment assignments within its own group, but not on assignments in other groups.

Randomization is two-stage (Assumption 1): a first-stage design decides which groups receive
allocation strategy ψ versus φ; conditionally, each group is randomized by its assigned within-group
design.  The joint law combines the first-stage design with the per-group product design, so
cross-group independence is structural.

This file fixes the public vocabulary used by the rest of the subtree: assignment spaces
`WAssign` and `StratAssign`, the compound two-stage design `jointDesign`, average-potential-outcome
estimands `indMean`, `groupMean`, `popMean`, `indMarg`, and `popMarg`, causal contrasts
`CE_direct`, `CE_indirect`, `CE_total`, and `CE_overall`, and the estimators `groupEst`,
`popEst`, and `estDirect`.  The unbiasedness and variance theorems for these definitions live in
`Unbiased.lean`, `Effects.lean`, `BetweenGroup.lean`, and `Variance.lean`.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}

/-- Given [a population of groups](hyp:ι), [the number of units in every group](hyp:n) and [a group](hyp:i), the [within-group
assignment space](goal) consists of all assignments that give each unit in that group a treated or
untreated indicator. -/
abbrev WAssign (n : ι → ℕ) (i : ι) := Fin (n i) → Bool

/-- Given [a population of groups](hyp:ι), the [first-stage strategy-assignment space](goal)
consists of all assignments that give each group one of two allocation strategies. -/
abbrev StratAssign (ι : Type*) := ι → Bool

/-- Given [a finite population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
first-stage finite randomization design over the two allocation strategies](hyp:D₁) and [two
within-group finite randomization designs for every group](hyp:ψ,φ), the [joint two-stage
randomization design](goal) first draws the strategy assignment and then, conditionally for each
group, draws its within-group assignment from the first design when that group receives the first
strategy and from the second design otherwise. -/
noncomputable def jointDesign (D₁ : FiniteDesign (StratAssign ι))
    (ψ φ : ∀ i, FiniteDesign (WAssign n i)) :
    FiniteDesign (StratAssign ι × ∀ i, WAssign n i) :=
  compound D₁ (fun s i => if s i then ψ i else φ i)

/-! ### Estimands (population average potential outcomes) -/

/-- Given [a population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
within-group randomization design for every group](hyp:ρ), [the potential outcome of each unit
under every within-group assignment](hyp:Y), [a group](hyp:i), [a unit in that group](hyp:j), and
[a treatment status](hyp:z), the [individual average potential outcome](goal) is that
unit's expected outcome under the group's design conditional on its own treatment having that
status, expressed as the corresponding weighted expectation divided by the probability of that
status. -/
noncomputable def indMean (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (i : ι) (j : Fin (n i)) (z : Bool) : ℝ :=
  (ρ i).E (fun w => if w j = z then Y i j w else 0) / (ρ i).Pr (fun w => w j = z)

/-- Given [a population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
within-group randomization design for every group](hyp:ρ), [the potential outcome of each unit
under every within-group assignment](hyp:Y), [a group](hyp:i), and [a treatment status](hyp:z),
the [group average potential outcome](goal) is the arithmetic mean of the individual
average potential outcomes of all units in that group at that status. -/
noncomputable def groupMean (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (i : ι) (z : Bool) : ℝ :=
  (∑ j, indMean ρ Y i j z) / (n i : ℝ)

/-- Given [a finite population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
within-group randomization design for every group](hyp:ρ), [the potential outcome of each unit
under every within-group assignment](hyp:Y), and [a treatment status](hyp:z), the
[population average potential outcome](goal) is the arithmetic mean, over all groups, of their
group average potential outcomes at that status. -/
noncomputable def popMean (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (z : Bool) : ℝ :=
  (∑ i, groupMean ρ Y i z) / (Fintype.card ι : ℝ)

/-- Given [a population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
within-group randomization design for every group](hyp:ρ), [the potential outcome of each unit
under every within-group assignment](hyp:Y), [a group](hyp:i), and [a unit in that group](hyp:j),
the [marginal individual average potential outcome](goal) is that unit's expected outcome
under its group's design, averaging over its own treatment status. -/
noncomputable def indMarg (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (i : ι) (j : Fin (n i)) : ℝ :=
  (ρ i).E (fun w => Y i j w)

/-- Given [a finite population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
within-group randomization design for every group](hyp:ρ) and [the potential outcome of each unit
under every within-group assignment](hyp:Y), the [population marginal average
potential outcome](goal) is the arithmetic mean, over all groups, of their averages of marginal
individual outcomes. -/
noncomputable def popMarg (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  (∑ i, (∑ j, indMarg ρ Y i j) / (n i : ℝ)) / (Fintype.card ι : ℝ)

/-- Given [a finite population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
within-group randomization design for every group](hyp:ψ), and [the potential outcome of each unit
under every within-group assignment](hyp:Y), the [Hudgens--Halloran direct-effect contrast](goal)
is the population average potential outcome under treatment minus that under control, both evaluated
under the supplied design. -/
noncomputable def CE_direct (ψ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  popMean ψ Y true - popMean ψ Y false

/-- Given [a finite population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
first within-group randomization design for every group](hyp:ψ), [a second such design for every
group](hyp:φ), and [the potential outcome of each unit under every within-group assignment](hyp:Y),
the [indirect, or spillover, causal effect](goal) is the population average potential outcome under
control using the second design minus that using the first design. -/
noncomputable def CE_indirect (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  popMean φ Y false - popMean ψ Y false

/-- Given [a finite population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
first within-group randomization design for every group](hyp:ψ), [a second such design for every
group](hyp:φ), and [the potential outcome of each unit under every within-group assignment](hyp:Y),
the [total causal effect](goal) is the population average potential outcome under control using the
second design minus that under treatment using the first design.

Sign convention note: this is the control-minus-treatment orientation, negated
relative to the Hudgens-Halloran (2008) treatment-minus-control total effect. -/
noncomputable def CE_total (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  popMean φ Y false - popMean ψ Y true

/-- Given [a finite population of groups](hyp:ι), [the number of units in every group](hyp:n), [a
first within-group randomization design for every group](hyp:ψ), [a second such design for every
group](hyp:φ), and [the potential outcome of each unit under every within-group assignment](hyp:Y),
the [overall causal effect](goal) is the population marginal average potential outcome using the
second design minus that using the first design.

Sign convention note: this keeps the file's control-minus-treatment orientation,
negated relative to the Hudgens-Halloran (2008) overall-effect convention. -/
noncomputable def CE_overall (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  popMarg φ Y - popMarg ψ Y

/-! ### Estimators -/

/-- Given [a population of groups](hyp:ι), [the number of units in every group](hyp:n), [the
potential outcome of each unit under every within-group assignment](hyp:Y), [a group](hyp:i), [a
treatment status](hyp:z), [a real denominator](hyp:m), and [a realized within-group assignment](hyp:w),
the [within-group estimator](goal) is the sum of realized outcomes of units in that group
with the specified status, divided by the supplied denominator.  The denominator is intended to be
the design-fixed number of such units. -/
noncomputable def groupEst (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (i : ι) (z : Bool) (m : ℝ) (w : WAssign n i) : ℝ :=
  (∑ j, if w j = z then Y i j w else 0) / m

/-- Given [a finite population of groups](hyp:ι), [the number of units in every group](hyp:n), [the
potential outcome of each unit under every within-group assignment](hyp:Y), [a treatment status](hyp:z),
[a selected allocation strategy](hyp:pick), [a real within-group denominator for every
group](hyp:m), [a real population denominator](hyp:denom), and [a realized joint assignment](hyp:sw),
the [population estimator](goal) is the sum of within-group estimators over groups assigned the
selected strategy, divided by the population denominator.  Each within-group denominator is
intended to be the design-fixed number of units with the specified status. -/
noncomputable def popEst (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (z : Bool) (pick : Bool) (m : ι → ℝ) (denom : ℝ)
    (sw : StratAssign ι × ∀ i, WAssign n i) : ℝ :=
  (∑ i, if sw.1 i = pick then groupEst Y i z (m i) (sw.2 i) else 0) / denom

/-- Given [a finite population of groups](hyp:ι), [the number of units in every group](hyp:n), [the
potential outcome of each unit under every within-group assignment](hyp:Y), [a control denominator
for every group](hyp:m0), [a treatment denominator for every group](hyp:m1), [a real population
denominator](hyp:denom), and [a realized joint assignment](hyp:sw), the [direct-effect estimator](goal)
is the estimated treatment mean minus the estimated control mean among groups assigned the
first allocation strategy. -/
noncomputable def estDirect (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (m0 m1 : ι → ℝ) (denom : ℝ) (sw : StratAssign ι × ∀ i, WAssign n i) : ℝ :=
  popEst Y true true m1 denom sw - popEst Y false true m0 denom sw

end TwoStageInterference
end Experimentation
end Causalean
