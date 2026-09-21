/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Interval Random Sets and Everywhere-Selection Expectations

This file treats an interval-valued random set as measurable lower and upper
endpoint functions and characterizes functions that belong to the interval at
every sample outcome. It proves that the integrals of integrable measurable
everywhere-selections form the interval between the endpoint expectations. This
pointwise interface is stronger than the standard almost-sure selection used to
define the Aumann expectation.

Main declarations:
* `randomInterval` and `IsSelection` encode interval-valued random sets and
  their measurable selections.
* `isSelection_iff_exists_param` parametrizes every selection as
  `L + t * (U - L)` with measurable `t : Ω -> [0,1]`.
* `selectionExpectation_eq_Icc` identifies the everywhere-selection
  expectation with `[∫ L, ∫ U]`.
* `sInf_selectionExpectation` and `sSup_selectionExpectation` recover the sharp
  lower and upper endpoints from the set of selection integrals.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.PartialID.RandomSet

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {L U : Ω → ℝ}

/-- For [a sample space](hyp:Ω), [a lower endpoint function](hyp:L), and [an upper
endpoint function](hyp:U), the
[interval-valued random set](goal) assigns to every sample outcome the set of real numbers
that are at least its lower-endpoint value and at most its upper-endpoint value. -/
def randomInterval (L U : Ω → ℝ) : Ω → Set ℝ := fun ω => Set.Icc (L ω) (U ω)

/-- For [a sample space equipped with a measurable structure](hyp:Ω), [a lower
endpoint function](hyp:L), [an upper endpoint function](hyp:U), and
[a real-valued function on the sample space](hyp:f), the [everywhere measurable-selection
condition](goal) holds precisely when [the function is measurable](step:1) and [at every
sample outcome its value lies in the closed interval between the endpoint values](step:2).

`f` is a measurable everywhere-selection of the interval random set `[L, U]`:
it is measurable and `L ω ≤ f ω ≤ U ω` for every `ω`. -/
def IsSelection (L U f : Ω → ℝ) : Prop :=
  Measurable f ∧ ∀ ω, f ω ∈ Set.Icc (L ω) (U ω)

/-- [A measurable lower endpoint](hyp:hL) is an everywhere-selection whenever
[it is pointwise no larger than the upper endpoint](hyp:hLU), so [the interval
has a measurable everywhere-selection](goal). -/
theorem isSelection_left (hL : Measurable L) (hLU : ∀ ω, L ω ≤ U ω) :
    IsSelection L U L :=
  ⟨hL, fun ω => ⟨le_rfl, hLU ω⟩⟩

/-- **Measurable everywhere-selection of an interval random set.** Under
[measurable endpoints](hyp:hL,hU) with [pointwise ordering](hyp:hLU), [a
function](hyp:f) [belongs to `[L,U]` at every outcome exactly when it has the
form `L + t·(U − L)` for a measurable weight between zero and one](goal). -/
theorem isSelection_iff_exists_param (hL : Measurable L) (hU : Measurable U)
    (hLU : ∀ ω, L ω ≤ U ω) (f : Ω → ℝ) :
    IsSelection L U f ↔
      ∃ t : Ω → ℝ, Measurable t ∧ (∀ ω, t ω ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ ω, f ω = L ω + t ω * (U ω - L ω) := by
  constructor
  · rintro ⟨hf, hmem⟩
    refine ⟨fun ω => (f ω - L ω) * (U ω - L ω)⁻¹,
      (hf.sub hL).mul (hU.sub hL).inv, ?_, ?_⟩
    · intro ω
      simp only [Set.mem_Icc, ← div_eq_mul_inv]
      obtain ⟨hlf, hfu⟩ := hmem ω
      rcases (hLU ω).lt_or_eq with hlt | heq
      · have hw : (0 : ℝ) < U ω - L ω := by linarith
        refine ⟨div_nonneg (by linarith) (le_of_lt hw), ?_⟩
        rw [div_le_one hw]; linarith
      · have hw : U ω - L ω = 0 := by rw [heq]; ring
        rw [hw, div_zero]
        exact ⟨le_rfl, zero_le_one⟩
    · intro ω
      obtain ⟨hlf, hfu⟩ := hmem ω
      rcases (hLU ω).lt_or_eq with hlt | heq
      · have hw : (U ω - L ω) ≠ 0 := by
          have : (0 : ℝ) < U ω - L ω := by linarith
          exact ne_of_gt this
        field_simp
        ring
      · have hwL : L ω = U ω := heq
        have : f ω = L ω := le_antisymm (by rw [hwL]; exact hfu) hlf
        rw [this, ← heq]; ring
  · rintro ⟨t, ht, htmem, hfeq⟩
    have hfm : f = fun ω => L ω + t ω * (U ω - L ω) := funext hfeq
    refine ⟨by rw [hfm]; exact hL.add (ht.mul (hU.sub hL)), ?_⟩
    intro ω
    obtain ⟨ht0, ht1⟩ := htmem ω
    rw [hfeq ω]
    constructor
    · nlinarith [hLU ω]
    · nlinarith [hLU ω]

/-- For [a sample space equipped with a measurable structure](hyp:Ω), [a lower endpoint
function](hyp:L), [an upper endpoint function](hyp:U), and [a measure on the sample
space](hyp:μ), the [everywhere-selection expectation](goal) contains exactly the integrals of
integrable measurable functions that [belong to the endpoint interval at every sample
outcome](step:1).

Unlike the standard Aumann expectation, this definition requires pointwise rather than
almost-sure membership in the random interval. -/
def selectionExpectation (L U : Ω → ℝ) (μ : Measure Ω) : Set ℝ :=
  {r | ∃ f, IsSelection L U f ∧ Integrable f μ ∧ ∫ ω, f ω ∂μ = r}

/-- Monotonicity of the endpoint integrals (used to order the reported bounds). -/
theorem integral_le_integral_of_le (hLint : Integrable L μ) (hUint : Integrable U μ)
    (hLU : ∀ ω, L ω ≤ U ω) : (∫ ω, L ω ∂μ) ≤ ∫ ω, U ω ∂μ :=
  integral_mono_ae hLint hUint (ae_of_all _ hLU)

/-- **Everywhere-selection expectation equals `[∫L, ∫U]`.** For [measurable lower and upper endpoint
functions `L`, `U`](hyp:hL,hU) that are [integrable](hyp:hLint,hUint) and satisfy [`L`
pointwise at most `U`](hyp:hLU), [the integrals of all integrable measurable
everywhere-selections of `[L, U]` form the closed interval `[∫L dμ, ∫U dμ]`](goal).
The forward inclusion is integral monotonicity; the reverse inclusion realizes every
intermediate value with a constant mixing weight, so no atomlessness is needed. -/
theorem selectionExpectation_eq_Icc (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    selectionExpectation L U μ = Set.Icc (∫ ω, L ω ∂μ) (∫ ω, U ω ∂μ) := by
  ext r
  simp only [selectionExpectation, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨f, ⟨hfmeas, hfmem⟩, hfint, hfr⟩
    have hLf : (∫ ω, L ω ∂μ) ≤ ∫ ω, f ω ∂μ :=
      integral_mono_ae hLint hfint (ae_of_all _ (fun ω => (hfmem ω).1))
    have hfU : (∫ ω, f ω ∂μ) ≤ ∫ ω, U ω ∂μ :=
      integral_mono_ae hfint hUint (ae_of_all _ (fun ω => (hfmem ω).2))
    rw [hfr] at hLf hfU
    exact ⟨hLf, hfU⟩
  · rintro ⟨hLr, hrU⟩
    set a := ∫ ω, L ω ∂μ with ha
    set b := ∫ ω, U ω ∂μ with hb
    rcases (integral_le_integral_of_le hLint hUint hLU).lt_or_eq with hlt | heq
    · set c := (r - a) / (b - a) with hc
      have hba : (0 : ℝ) < b - a := by linarith
      have hc0 : 0 ≤ c := div_nonneg (by linarith) (le_of_lt hba)
      have hc1 : c ≤ 1 := by rw [hc, div_le_one hba]; linarith
      refine ⟨fun ω => L ω + c * (U ω - L ω),
        ⟨hL.add (measurable_const.mul (hU.sub hL)), fun ω => ?_⟩,
        hLint.add ((hUint.sub hLint).const_mul c), ?_⟩
      · refine ⟨?_, ?_⟩
        · nlinarith [hLU ω]
        · nlinarith [hLU ω]
      · beta_reduce
        rw [integral_add (f := L) (g := fun ω => c * (U ω - L ω)) hLint
            ((hUint.sub hLint).const_mul c),
          integral_const_mul, integral_sub hUint hLint, ← ha, ← hb, hc]
        field_simp
        ring
    · refine ⟨L, isSelection_left hL hLU, hLint, ?_⟩
      rw [← ha]
      linarith

/-- For [measurable lower and upper endpoint functions `L`, `U`](hyp:hL,hU) that are
[integrable](hyp:hLint,hUint) and satisfy [`L` pointwise at most `U`](hyp:hLU), [the
sharp lower endpoint of the identified set — the infimum of the everywhere-selection
expectation over all measurable selections of the interval-valued random set
`[L, U]` — equals the expectation of the lower endpoint `L`](goal):
`sInf (selectionExpectation L U μ) = ∫ L dμ`. -/
theorem sInf_selectionExpectation (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    sInf (selectionExpectation L U μ) = ∫ ω, L ω ∂μ := by
  rw [selectionExpectation_eq_Icc hL hU hLint hUint hLU]
  exact csInf_Icc (integral_le_integral_of_le hLint hUint hLU)

/-- For [measurable lower and upper endpoint functions `L`, `U`](hyp:hL,hU) that are
[integrable](hyp:hLint,hUint) and satisfy [`L` pointwise at most `U`](hyp:hLU), [the
sharp upper endpoint of the identified set — the supremum of the everywhere-selection
expectation over all measurable selections of the interval-valued random set
`[L, U]` — equals the expectation of the upper endpoint `U`](goal):
`sSup (selectionExpectation L U μ) = ∫ U dμ`. -/
theorem sSup_selectionExpectation (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    sSup (selectionExpectation L U μ) = ∫ ω, U ω ∂μ := by
  rw [selectionExpectation_eq_Icc hL hU hLint hUint hLU]
  exact csSup_Icc (integral_le_integral_of_le hLint hUint hLU)

end Causalean.PartialID.RandomSet
