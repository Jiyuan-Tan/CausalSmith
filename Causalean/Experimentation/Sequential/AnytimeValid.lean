/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Anytime-valid tests and confidence sequences

The inferential payoff of Ville's inequality.  An **anytime-valid test** at level `α` rejects the
null the first time a test supermartingale's wealth reaches `1/α`; because Ville's inequality bounds
the probability that the wealth *ever* reaches `1/α`, the test's type-I error is at most `α` no
matter when the analyst chooses to stop — inference remains valid under optional stopping.  Dually, a
**confidence sequence** is a time-indexed family of sets that covers the true parameter at all times
simultaneously with probability at least `1 − α`; inverting a family of test supermartingales (keep
the parameter values whose wealth has not yet reached `1/α`) yields one, with miscoverage controlled
by Ville's inequality.
-/

import Causalean.Experimentation.Sequential.Ville

/-!
# Anytime-valid tests and confidence sequences

This file turns Ville's inequality for test supermartingales into reusable sequential-inference
objects.  `rejectionRegion` is the event that wealth ever crosses `1/α`, `IsAnytimeValid` states
level-`α` type-I error control, and `isAnytimeValid_rejectionRegion` proves that control from
Ville's inequality.  The confidence-sequence side defines `IsConfidenceSequence`,
`confSeqOfWealth`, and `isConfidenceSequence_confSeqOfWealth`, the inverted coverage theorem.
-/

open MeasureTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Causalean
namespace Experimentation
namespace Sequential

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ### Anytime-valid testing -/

/-- For [a sample space and a real-valued wealth process indexed by time and outcome](hyp:Ω,M),
and [a real-valued test level](hyp:α), the [sequential-test rejection region](goal) is the event
that the wealth reaches or exceeds $1/α$ at at least one time, with this quotient understood as
zero when $α=0$. -/
def rejectionRegion (M : ℕ → Ω → ℝ) (α : ℝ) : Set Ω := {ω | ∃ n, 1 / α ≤ M n ω}

/-- For [a measurable sample space](hyp:Ω,m0), [an event on that space](hyp:R), [a measure on
the sample space](hyp:μ), and [a real-valued test level](hyp:α), the [property of being
anytime-valid at that level](goal) means that the measure of the event is at most $\max\{α,0\}$.
-/
def IsAnytimeValid (R : Set Ω) (μ : Measure Ω) (α : ℝ) : Prop := μ R ≤ ENNReal.ofReal α

/-- **Anytime-valid type-I error control.** If [the wealth process `M` is a test supermartingale
for the filtration `ℱ` under `μ`](hyp:hM) and [the level `α` is positive](hyp:hα), then [the event
that `M` ever reaches `1/α` has probability at most `α`](goal). -/
theorem isAnytimeValid_rejectionRegion [IsFiniteMeasure μ] {M : ℕ → Ω → ℝ}
    (hM : IsTestSupermartingale M ℱ μ) {α : ℝ} (hα : 0 < α) :
    IsAnytimeValid (rejectionRegion M α) μ α :=
  ville_test hM hα

/-! ### Confidence sequences -/

/-- For [a measurable sample space](hyp:Ω,m0), [a time-indexed coverage predicate on that
space](hyp:cover), [a measure on the sample space](hyp:μ), and [a real-valued level](hyp:α), the
[property of being a confidence sequence at that level](goal) means that the measure of outcomes
on which coverage fails at at least one time is at most $\max\{α,0\}$. -/
def IsConfidenceSequence (cover : ℕ → Ω → Prop) (μ : Measure Ω) (α : ℝ) : Prop :=
  μ {ω | ∃ n, ¬ cover n ω} ≤ ENNReal.ofReal α

/-- For [a sample space and a real-valued wealth process indexed by time and outcome](hyp:Ω,M) and [a real-valued
level](hyp:α), the [wealth-inverted coverage predicate](goal) holds at a given time and outcome
exactly when the wealth at that time is strictly less than $1/α$, with this quotient understood as
zero when $α=0$. -/
def confSeqOfWealth (M : ℕ → Ω → ℝ) (α : ℝ) : ℕ → Ω → Prop := fun n ω => M n ω < 1 / α

/-- **Confidence-sequence coverage.** If [`M` is a test supermartingale for the filtration `ℱ`
under `μ`](hyp:hM) and [the level `α` is positive](hyp:hα), then [the cover obtained by requiring
`M`'s wealth to stay below `1/α` fails at some time with probability at most `α`](goal). -/
theorem isConfidenceSequence_confSeqOfWealth [IsFiniteMeasure μ] {M : ℕ → Ω → ℝ}
    (hM : IsTestSupermartingale M ℱ μ) {α : ℝ} (hα : 0 < α) :
    IsConfidenceSequence (confSeqOfWealth M α) μ α := by
  have hset : {ω | ∃ n, ¬ confSeqOfWealth M α n ω} = {ω | ∃ n, 1 / α ≤ M n ω} := by
    ext ω; simp only [confSeqOfWealth, Set.mem_setOf_eq, not_lt]
  rw [IsConfidenceSequence, hset]
  exact ville_test hM hα

end Sequential
end Experimentation
end Causalean
