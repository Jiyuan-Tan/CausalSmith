/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.Sequential.Ville

/-!
# Anytime-valid tests and confidence sequences

This file turns Ville's inequality for test supermartingales into reusable sequential-inference
objects under probability measures. An anytime-valid test rejects when wealth first reaches
`1/α`; Ville's inequality controls the probability of that event by `α`, regardless of when the
analyst stops. Dually, wealth inversion retains parameter values whose wealth remains below
`1/α`, producing simultaneous coverage at least `1 − α`.

The file defines the crossing event, the anytime-validity and confidence-sequence predicates, and
the two theorems that transfer Ville's probability bound to type-I error and miscoverage control.
-/

@[expose] public section

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

/-- For [a measurable sample space](hyp:Ω,m0), [an event on that space](hyp:R),
[a probability measure on the sample space](hyp:μ), and [a real-valued test level](hyp:α),
[anytime validity at that level](goal) means that the event has measure at most $\max\{α,0\}$.
-/
def IsAnytimeValid (R : Set Ω) (μ : Measure Ω) (α : ℝ) : Prop :=
  μ R ≤ ENNReal.ofReal α

/-- **Anytime-valid type-I error control.** If
[`M` is a test supermartingale under the probability measure](hyp:hM) and
[the level `α` is positive](hyp:α,hα), then
[the crossing event has measure at most `α`](goal). -/
theorem isAnytimeValid_rejectionRegion [IsFiniteMeasure μ] {M : ℕ → Ω → ℝ}
    (hM : IsTestSupermartingale M ℱ μ) {α : ℝ} (hα : 0 < α) :
    IsAnytimeValid (rejectionRegion M α) μ α :=
  ville_test hM hα

/-! ### Confidence sequences -/

/-- For [a measurable sample space](hyp:Ω,m0),
[a time-indexed coverage predicate on that space](hyp:cover),
[a probability measure on the sample space](hyp:μ), and [a real-valued level](hyp:α),
[the confidence-sequence property](goal) means that simultaneous miscoverage has measure at most
$\max\{α,0\}$. -/
def IsConfidenceSequence (cover : ℕ → Ω → Prop) (μ : Measure Ω) (α : ℝ) : Prop :=
  μ {ω | ∃ n, ¬ cover n ω} ≤ ENNReal.ofReal α

/-- For [a sample space and a real-valued wealth process indexed by time and outcome](hyp:Ω,M)
and [a real-valued level](hyp:α), the [wealth-inverted coverage predicate](goal) holds at a given
time and outcome
exactly when the wealth at that time is strictly less than $1/α$, with this quotient understood as
zero when $α=0$. -/
def confSeqOfWealth (M : ℕ → Ω → ℝ) (α : ℝ) : ℕ → Ω → Prop := fun n ω => M n ω < 1 / α

/-- **Confidence-sequence coverage.** If
[`M` is a test supermartingale under the probability measure](hyp:hM) and
[the level `α` is positive](hyp:α,hα), then
[wealth inversion fails to cover at some time with probability at most `α`](goal). -/
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
