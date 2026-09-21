/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Event-selected mixtures under a product law

This module defines a two-branch function selected by an independent measurable event and
computes its first moment, second moment, and variance under the product probability law.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Probability

open MeasureTheory ProbabilityTheory

/-- A product of independent square-integrable scalar functions remains square-integrable on
the product space. [The two factors are square-integrable](hyp:hf,hg), and [their coordinatewise
product is square-integrable under the product measure](goal). -/
lemma memLp_mul_prod_two {S K : Type*} [Countable S] [Countable K]
    [MeasurableSpace S] [MeasurableSpace K]
    [MeasurableSingletonClass S] [MeasurableSingletonClass K]
    {muS : Measure S} {muK : Measure K} {f : S → Real} {g : K → Real}
    (hf : MemLp f 2 muS) (hg : MemLp g 2 muK) :
    MemLp (fun z : S × K ↦ f z.1 * g z.2) 2 (muS.prod muK) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_of_countable _).aestronglyMeasurable).2
  apply (hf.integrable_sq.mul_prod hg.integrable_sq).congr
  filter_upwards [] with z
  ring

/-- Given [an event, two branch functions, and a point in the product space](hyp:A,P,H,z),
[the event-selected mixture uses the first branch on the event and the second branch off
the event](goal). -/
noncomputable def eventSelectedMixture {J E : Type*} (A : Set J) (P H : E → Real)
    (z : J × E) : Real :=
  (Prod.fst ⁻¹' A).indicator (fun z ↦ P z.2) z +
    (Prod.fst ⁻¹' A)ᶜ.indicator (fun z ↦ H z.2) z

private noncomputable def eventIndicator {J : Type*} (A : Set J) (j : J) : Real :=
  A.indicator (fun _ ↦ (1 : Real)) j

private lemma integrable_eventIndicator {J : Type*} [MeasurableSpace J]
    (μ : Measure J) [IsFiniteMeasure μ] (A : Set J) (hA : MeasurableSet A) :
    Integrable (eventIndicator A) μ := by
  classical
  apply Integrable.of_bound (measurable_const.indicator hA).aestronglyMeasurable 1
  filter_upwards [] with j
  by_cases hj : j ∈ A <;> simp [hj]

private lemma integral_eventIndicator {J : Type*} [MeasurableSpace J]
    (μ : Measure J) [IsProbabilityMeasure μ] (A : Set J) (hA : MeasurableSet A) :
    ∫ j, eventIndicator A j ∂μ = μ.real A := by
  classical
  unfold eventIndicator
  rw [integral_indicator hA]
  simp [MeasureTheory.measureReal_def]

/-- For [two probability laws, a measurable event, and two integrable branch
functions](hyp:μJ,μE,A,hA,P,H,hP,hH), [the selected function's mean is the event-probability
mixture of the two branch means](goal). -/
lemma integral_eventSelectedMixture {J E : Type*} [MeasurableSpace J] [MeasurableSpace E]
    (μJ : Measure J) (μE : Measure E) [IsProbabilityMeasure μJ]
    [IsProbabilityMeasure μE] (A : Set J) (hA : MeasurableSet A)
    (P H : E → Real) (hP : Integrable P μE) (hH : Integrable H μE) :
    ∫ z, eventSelectedMixture A P H z ∂μJ.prod μE =
      μJ.real A * (∫ e, P e ∂μE) +
        (1 - μJ.real A) * (∫ e, H e ∂μE) := by
  classical
  let I := eventIndicator A
  let Ic : J → Real := fun j ↦ 1 - I j
  have hI : Integrable I μJ := integrable_eventIndicator μJ A hA
  have hIc : Integrable Ic μJ := (integrable_const 1).sub hI
  have hpoint : eventSelectedMixture A P H =
      fun z ↦ I z.1 * P z.2 + Ic z.1 * H z.2 := by
    funext z
    by_cases hz : z.1 ∈ A <;> simp [eventSelectedMixture, I, Ic, eventIndicator, hz]
  rw [hpoint, integral_add (hI.mul_prod hP) (hIc.mul_prod hH),
    integral_prod_mul, integral_prod_mul, integral_eventIndicator μJ A hA]
  have hIcInt : (∫ j, Ic j ∂μJ) = 1 - μJ.real A := by
    dsimp [Ic]
    rw [integral_sub (integrable_const 1) hI, integral_eventIndicator μJ A hA]
    simp
  rw [hIcInt]

/-- For [two probability laws, a measurable event, and two square-integrable branch
functions](hyp:μJ,μE,A,hA,P,H,hP,hH), [the selected function's second moment is the
event-probability mixture of the two branch second moments](goal). -/
lemma integral_eventSelectedMixture_sq {J E : Type*}
    [MeasurableSpace J] [MeasurableSpace E]
    (μJ : Measure J) (μE : Measure E) [IsProbabilityMeasure μJ]
    [IsProbabilityMeasure μE] (A : Set J) (hA : MeasurableSet A)
    (P H : E → Real) (hP : MemLp P 2 μE) (hH : MemLp H 2 μE) :
    ∫ z, eventSelectedMixture A P H z ^ 2 ∂μJ.prod μE =
      μJ.real A * (∫ e, P e ^ 2 ∂μE) +
        (1 - μJ.real A) * (∫ e, H e ^ 2 ∂μE) := by
  have h := integral_eventSelectedMixture μJ μE A hA
    (fun e ↦ P e ^ 2) (fun e ↦ H e ^ 2) hP.integrable_sq hH.integrable_sq
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z.1 ∈ A <;> simp [eventSelectedMixture, hz]

/-- For [two probability laws, a measurable event, and two square-integrable branch
functions](hyp:μJ,μE,A,hA,P,H,hP,hH), [the event-selected mixture is square-integrable
under the product law](goal). -/
lemma memLp_eventSelectedMixture {J E : Type*}
    [MeasurableSpace J] [MeasurableSpace E]
    (μJ : Measure J) (μE : Measure E) [IsProbabilityMeasure μJ]
    [IsProbabilityMeasure μE]
    (A : Set J) (hA : MeasurableSet A) (P H : E → Real)
    (hP : MemLp P 2 μE) (hH : MemLp H 2 μE) :
    MemLp (eventSelectedMixture A P H) 2 (μJ.prod μE) := by
  have hPA : MemLp ((Prod.fst ⁻¹' A).indicator (fun z : J × E ↦ P z.2)) 2
      (μJ.prod μE) :=
    (hP.comp_measurePreserving measurePreserving_snd).indicator
      (hA.preimage measurable_fst)
  have hHA : MemLp ((Prod.fst ⁻¹' A)ᶜ.indicator (fun z : J × E ↦ H z.2)) 2
      (μJ.prod μE) :=
    (hH.comp_measurePreserving measurePreserving_snd).indicator
      (hA.preimage measurable_fst).compl
  exact hPA.add hHA

/-- For [two probability laws, a measurable event, and two square-integrable branch
functions](hyp:μJ,μE,A,hA,P,H,hP,hH), [the selected function's variance is the mixture of
branch variances plus the between-branch mean term](goal). -/
lemma variance_eventSelectedMixture {J E : Type*}
    [MeasurableSpace J] [MeasurableSpace E]
    (μJ : Measure J) (μE : Measure E) [IsProbabilityMeasure μJ]
    [IsProbabilityMeasure μE] (A : Set J) (hA : MeasurableSet A)
    (P H : E → Real) (hP : MemLp P 2 μE) (hH : MemLp H 2 μE) :
    Var[eventSelectedMixture A P H; μJ.prod μE] =
      μJ.real A * Var[P; μE] + (1 - μJ.real A) * Var[H; μE] +
        μJ.real A * (1 - μJ.real A) *
          ((∫ e, P e ∂μE) - ∫ e, H e ∂μE) ^ 2 := by
  rw [variance_eq_sub (memLp_eventSelectedMixture μJ μE A hA P H hP hH)]
  change (∫ z, eventSelectedMixture A P H z ^ 2 ∂μJ.prod μE) -
      (∫ z, eventSelectedMixture A P H z ∂μJ.prod μE) ^ 2 = _
  rw [
    integral_eventSelectedMixture_sq μJ μE A hA P H hP hH,
    integral_eventSelectedMixture μJ μE A hA P H
      (hP.integrable one_le_two) (hH.integrable one_le_two),
    variance_eq_sub hP, variance_eq_sub hH]
  simp only [Pi.pow_apply]
  ring

end Causalean.Mathlib.Probability
