/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Almost-everywhere equality lifts under overlap

* `ae_eq_of_ae_eq_restrict_arm` — if two `m`-measurable functions agree on
  `μ.restrict E` and every `m`-measurable set null on `E` is globally null,
  they agree μ-a.e. globally.

The supporting lemmas convert restricted a.e. equality to and from equality of
indicators and propagate indicator vanishing through conditional expectation.
-/

module
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Probability.Independence.Conditional

/-! # Almost-Everywhere Lifts Under Overlap

This file proves generic almost-everywhere equality lifting lemmas under an
overlap-style null-set hypothesis.

The exported support lemmas convert between restricted a.e. equality and
indicator equality (`indicator_aeEq_of_aeEq_restrict`,
`aeEq_restrict_of_indicator_aeEq`) and propagate vanishing through conditional
expectation (`condExp_indicator_aeEq_zero`). The main public theorem is
`ae_eq_of_ae_eq_restrict_arm`. -/

public section

namespace Causalean.Mathlib.Probability.Independence.Conditional
open _root_.MeasureTheory
open scoped MeasureTheory ProbabilityTheory

/-- Push an a.e.-equality under `μ.restrict s` to a global equality of
`s`-indicators. -/
lemma indicator_aeEq_of_aeEq_restrict
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    {s : Set Ω} (hs : MeasurableSet s) {β : Type*} [Zero β] {f g : Ω → β}
    (h : f =ᵐ[μ.restrict s] g) :
    s.indicator f =ᵐ[μ] s.indicator g := by
  have h_on : ∀ᵐ ω ∂(μ.restrict s), s.indicator f ω = s.indicator g ω := by
    filter_upwards [h, ae_restrict_mem hs] with ω hω hωs
    rw [Set.indicator_of_mem hωs, Set.indicator_of_mem hωs, hω]
  have h_off : ∀ᵐ ω ∂(μ.restrict sᶜ), s.indicator f ω = s.indicator g ω := by
    rw [ae_restrict_iff' hs.compl]
    filter_upwards with ω hωs
    rw [Set.indicator_of_notMem hωs, Set.indicator_of_notMem hωs]
  exact MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl s h_on h_off

/-- Recover a `μ.restrict s` a.e.-equality from a global equality of
`s`-indicators. -/
lemma aeEq_restrict_of_indicator_aeEq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    {s : Set Ω} (hs : MeasurableSet s) {β : Type*} [Zero β] {f g : Ω → β}
    (h : s.indicator f =ᵐ[μ] s.indicator g) :
    f =ᵐ[μ.restrict s] g := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs]
  filter_upwards [h] with ω hω hωs
  have hf : s.indicator f ω = f ω := Set.indicator_of_mem hωs f
  have hg : s.indicator g ω = g ω := Set.indicator_of_mem hωs g
  simpa [hf, hg] using hω

/-- If an integrable function vanishes after restriction by an `m`-measurable
indicator, so does its conditional expectation. -/
lemma condExp_indicator_aeEq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    {m : MeasurableSpace Ω} {s : Set Ω} (hs : MeasurableSet[m] s)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : Ω → E} (hf : MeasureTheory.Integrable f μ)
    (h : s.indicator f =ᵐ[μ] 0) :
    s.indicator (μ[f | m]) =ᵐ[μ] 0 := by
  have hCE_ind := MeasureTheory.condExp_indicator (m := m) hf hs
  have hLHS_zero : μ[s.indicator f | m] =ᵐ[μ] 0 := by
    refine (MeasureTheory.condExp_congr_ae (m := m) h).trans ?_
    rw [MeasureTheory.condExp_zero (m := m) (μ := μ) (E := E)]
  exact hCE_ind.symm.trans hLHS_zero

/-- **Restricted-set a.e.-equality lift for σ-measurable functions.** For [a
sub-σ-algebra `m`](hyp:m) such that [`m` is coarser than the ambient
σ-algebra](hyp:hm), if [`f` and `g` agree on an `m`-measurable
set](hyp:h_eq_meas), [they agree almost everywhere on the restriction of the measure to a set
`E`](hyp:_h), and [every `m`-measurable set whose intersection with `E` is null is
itself null](hyp:_h_overlap), then
[`f` and `g` agree almost everywhere on the whole space](goal).

Without the null-set transfer hypothesis, the statement is false: `m`-measurable
functions can agree on `E` while differing outside `E` if `E` does not detect all
positive-measure `m`-measurable sets.

The proof applies the hypothesis to the `m`-measurable set where `f` and `g`
differ. -/
theorem ae_eq_of_ae_eq_restrict_arm
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {μ : @MeasureTheory.Measure Ω mΩ}
    {E : Set Ω}
    {β : Type*} {f g : Ω → β}
    (h_eq_meas : MeasurableSet[m] {ω | f ω = g ω})
    (_h : f =ᵐ[μ.restrict E] g)
    (_h_overlap : ∀ s : Set Ω, MeasurableSet[m] s →
        μ (s ∩ E) = 0 → μ s = 0) :
    f =ᵐ[μ] g := by
  let s : Set Ω := {ω | f ω ≠ g ω}
  have hs : MeasurableSet[m] s := by
    simpa [s, Set.compl_setOf] using h_eq_meas.compl
  have hs_ambient : @MeasurableSet Ω mΩ s := hm _ hs
  have hs_arm_zero : μ (s ∩ E) = 0 := by
    have hbad : (μ.restrict E) s = 0 := by
      exact MeasureTheory.ae_iff.mp _h
    rwa [MeasureTheory.Measure.restrict_apply hs_ambient] at hbad
  have hs_zero : μ s = 0 := _h_overlap s hs hs_arm_zero
  exact MeasureTheory.ae_iff.mpr hs_zero

end Causalean.Mathlib.Probability.Independence.Conditional
