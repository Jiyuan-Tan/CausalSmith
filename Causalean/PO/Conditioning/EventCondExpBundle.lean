/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.Conditioning.Bundle
public import Causalean.PO.Conditioning.EventCondExp

/-! # Bundle-Conditional Event Expectations

This file extends the event-level conditional-expectation workhorse to
conditioning on a finite bundle of potential-outcome variables. It provides the
product and ratio forms needed for dynamic local-average-treatment-effect bridge
arguments.

The theorem `POCFBundle.condExpGiven_mul_of_indicator_ae_eq_CondIndepCFBundle`
turns bundle-conditional independence and an indicator-weighted product
identity into a factorization of bundle conditional expectations.  The theorem
`POCFBundle.condExpRatio_of_indicator_ae_eq_CondIndepCFBundle` divides that
factorization by the conditional event probability under an a.e. nonzero
denominator assumption. -/

public section

open Causalean.Mathlib.Probability.Independence.Conditional

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

noncomputable section

namespace POCFBundle

variable {P : POSystem} (B C : POCFBundle P)

/-- **Bundle product-form workhorse** (analogue of
`POSystem.eventCondExp_of_ae_eq_IndepCF`). Suppose [a factual variable
`a` is conditionally independent, given the σ-algebra of a bundle `C`, of a
counterfactual bundle `B`](hyp:hCI), where [`h` is a measurable
function](hyp:hh_meas) [whose composite with `B`'s joint value is
integrable](hyp:hh_int), and [`{x}` is a measurable singleton](hyp:hx) in the
range of `a`. If [the factual integrand `factualF` times the indicator of
`{a = x}` agrees almost everywhere with `h` composed with `B`'s joint value,
times the same indicator](hyp:hF_eq), then [the bundle conditional
expectation, given `C`, of `factualF` times the indicator of `{a = x}`
factorises almost everywhere as the bundle conditional expectation of `h`
composed with `B`'s joint value, times the bundle conditional expectation of
the indicator of `{a = x}`](goal):

  C.condExpGiven (factualF · 1_{a=x})
    =ᵐ C.condExpGiven (h ∘ B.jointValue) · C.condExpGiven (1_{a=x}).

Used by dynamic-regime bridge arguments that condition on a history bundle. -/
theorem condExpGiven_mul_of_indicator_ae_eq_CondIndepCFBundle
    [StandardBorelSpace P.Ω]
    {α : Type*} [MeasurableSpace α]
    {a : POVar P α}
    (hCI : P.CondIndepCFBundle (RegimedVar.ofFactual a) B C P.μ)
    {factualF : P.Ω → ℝ}
    {h : (∀ i, B.type i) → ℝ} (hh_meas : Measurable h)
    (hh_int : Integrable (fun ω => h (B.jointValue ω)) P.μ)
    {x : α} (hx : MeasurableSet ({x} : Set α))
    (hF_eq : (fun ω => factualF ω * a.indicator x ω) =ᵐ[P.μ]
              fun ω => h (B.jointValue ω) * a.indicator x ω) :
    C.condExpGiven (fun ω => factualF ω * a.indicator x ω) P.μ
        =ᵐ[P.μ]
      fun ω => C.condExpGiven (fun ω' => h (B.jointValue ω')) P.μ ω
        * C.condExpGiven (a.indicator x) P.μ ω := by
  let u : α → ℝ := ({x} : Set α).indicator (fun _ => (1 : ℝ))
  have hu_meas : Measurable u :=
    measurable_const.indicator hx
  have hu_eq : (fun ω => u (a.factual ω)) = a.indicator x := by
    funext ω
    unfold POVar.indicator
    by_cases hω : a.factual ω = x
    · have h1 : a.factual ω ∈ ({x} : Set α) := hω
      have h2 : ω ∈ a.event x := hω
      rw [show u (a.factual ω) = (1 : ℝ) from Set.indicator_of_mem h1 _,
          Set.indicator_of_mem h2]
    · have h1 : a.factual ω ∉ ({x} : Set α) := hω
      have h2 : ω ∉ a.event x := hω
      rw [show u (a.factual ω) = (0 : ℝ) from Set.indicator_of_notMem h1 _,
          Set.indicator_of_notMem h2]
  have huv_int : Integrable
      (fun ω => u (a.factual ω) * h (B.jointValue ω)) P.μ := by
    have hEq : (fun ω => u (a.factual ω) * h (B.jointValue ω)) =
        (fun ω => a.indicator x ω * h (B.jointValue ω)) := by
      funext ω
      rw [congr_fun hu_eq ω]
    rw [hEq]
    refine hh_int.mono
      ((a.measurable_indicator x hx).mul
        (hh_meas.comp B.measurable_jointValue)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases a.indicator_eq_one_or_zero x ω with hω | hω <;> simp [hω]
  have hfact :
      P.μ[fun ω => u (a.factual ω) * h (B.jointValue ω) | C.sigma]
        =ᵐ[P.μ]
          P.μ[fun ω => u (a.factual ω) | C.sigma]
            * P.μ[fun ω => h (B.jointValue ω) | C.sigma] :=
    condExp_mul_of_condIndep (μ := P.μ)
        (m := C.sigma) C.sigma_le
        (f := a.factual) (g := B.jointValue)
        a.measurable_factual B.measurable_jointValue hCI.toCondIndepFun
        (u := u) (v := h) hu_meas hh_meas
        (by
          rw [hu_eq]
          exact a.integrable_indicator x hx) hh_int huv_int
  have hfact' :
      C.condExpGiven (fun ω => h (B.jointValue ω) * a.indicator x ω) P.μ
        =ᵐ[P.μ]
          fun ω => C.condExpGiven (fun ω' => h (B.jointValue ω')) P.μ ω
            * C.condExpGiven (a.indicator x) P.μ ω := by
    unfold POCFBundle.condExpGiven
    have hprod_rw :
        (fun ω => u (a.factual ω) * h (B.jointValue ω)) =
          (fun ω => h (B.jointValue ω) * a.indicator x ω) := by
      funext ω
      rw [congr_fun hu_eq ω]
      ring
    rw [hprod_rw, hu_eq] at hfact
    filter_upwards [hfact] with ω hω
    simpa [Pi.mul_apply, mul_comm] using hω
  exact (C.condExpGiven_congr_ae hF_eq).trans hfact'

/-- **Bundle ratio-form workhorse**: ratio version of
`condExpGiven_mul_of_indicator_ae_eq_CondIndepCFBundle`. Under the same
hypotheses as that theorem — [bundle-conditional independence of `a` from
`B` given `C`](hyp:hCI), [a measurable](hyp:hh_meas) and
[integrable](hyp:hh_int) composite `h ∘ B.jointValue`, [a measurable
singleton `{x}`](hyp:hx), and [an indicator-weighted almost-everywhere
identity](hyp:hF_eq) — plus [an almost-surely nonzero bundle-conditional
probability of `{a = x}`](hyp:hOver), [the conditional ratio
`condExpRatio (factualF · 1_{a=x}) (1_{a=x})` collapses almost everywhere to
the bundle conditional mean of `h ∘ B.jointValue`](goal). -/
theorem condExpRatio_of_indicator_ae_eq_CondIndepCFBundle
    [StandardBorelSpace P.Ω]
    {α : Type*} [MeasurableSpace α]
    {a : POVar P α}
    (hCI : P.CondIndepCFBundle (RegimedVar.ofFactual a) B C P.μ)
    {factualF : P.Ω → ℝ}
    {h : (∀ i, B.type i) → ℝ} (hh_meas : Measurable h)
    (hh_int : Integrable (fun ω => h (B.jointValue ω)) P.μ)
    {x : α} (hx : MeasurableSet ({x} : Set α))
    (hF_eq : (fun ω => factualF ω * a.indicator x ω) =ᵐ[P.μ]
              fun ω => h (B.jointValue ω) * a.indicator x ω)
    (hOver : ∀ᵐ ω ∂P.μ, C.condExpGiven (a.indicator x) P.μ ω ≠ 0) :
    C.condExpRatio (fun ω => factualF ω * a.indicator x ω) (a.indicator x) P.μ
        =ᵐ[P.μ]
      C.condExpGiven (fun ω' => h (B.jointValue ω')) P.μ := by
  refine C.condExpRatio_eq_of_mul ?_ hOver
  filter_upwards [condExpGiven_mul_of_indicator_ae_eq_CondIndepCFBundle B C
    hCI hh_meas hh_int hx hF_eq] with ω hω
  simpa [Pi.mul_apply, mul_comm] using hω

end POCFBundle

end

end PO
end Causalean
