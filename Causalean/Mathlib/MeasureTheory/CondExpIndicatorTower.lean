/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Conditioning an indicator across a σ-algebra tower

This file proves that conditioning a function masked by an intermediate-measurable event on a
coarser σ-algebra is unchanged when the function is first replaced by its conditional expectation
at the intermediate level.

For a tower of σ-algebras `m ≤ m'`, an `m'`-measurable set `s`, and integrable `f`, the identity
is:

    μ[1_s · f | m]  =ᵐ  μ[1_s · μ[f | m'] | m].

Proof is the inner `condExp_indicator` (`s` is `m'`-measurable) followed by the
tower `condExp_condExp_of_le`.
-/

public section

open MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m m' m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- [Conditioning an indicator-masked function on a coarser σ-algebra is unchanged when the
function is first replaced by its conditional expectation for an intermediate
σ-algebra](goal), provided [the σ-algebras form a nested tower with a σ-finite trimmed
measure](hyp:hm,hm'), [the masking set is measurable at the intermediate level](hyp:hs), and
[the function is integrable](hyp:hf).

    μ[s.indicator f | m]  =ᵐ[μ]  μ[s.indicator (μ[f | m']) | m].

(Here `s.indicator g = 1_s · g`.) Masking and projecting to the coarser `m` commute with
first taking the conditional expectation for the finer σ-algebra. -/
theorem condExp_setIndicator_condExp_of_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hm : m ≤ m') (hm' : m' ≤ m0) [SigmaFinite (μ.trim hm')]
    {s : Set Ω} (hs : MeasurableSet[m'] s) {f : Ω → E} (hf : Integrable f μ) :
    (μ[s.indicator f | m]) =ᵐ[μ] (μ[s.indicator (μ[f | m']) | m]) := by
  exact (MeasureTheory.condExp_condExp_of_le (μ := μ) (f := s.indicator f) hm hm').symm.trans
    (MeasureTheory.condExp_congr_ae (m := m) (μ := μ)
      (MeasureTheory.condExp_indicator (m := m') (μ := μ) hf hs))

end MeasureTheory
