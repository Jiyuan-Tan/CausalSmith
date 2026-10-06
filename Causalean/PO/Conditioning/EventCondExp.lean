/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.Mathlib.Probability.Independence.Integral
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Causalean.PO.Assumptions.IndepCF
public import Causalean.PO.Core.Variable
public import Causalean.Tactic.Attr
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Event-Level Conditional Expectations

This file specializes normalized restricted integrals to potential-outcome variables. It provides
multiplied and quotient drop-of-conditioning identities under independence, a consistency-on-event
identity, and an eventwise relabeling workhorse. The general measure-theoretic definition and
algebra live in `Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge`. -/

@[expose] public section

namespace Causalean
namespace PO

attribute [condexp_simps] Causalean.Mathlib.Probability.eventCondExp_eq

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability

noncomputable section

/-! ### Drop-of-conditioning for `IndepCF`

The `IndepCF` shape gives us `IndepFun rv.value B.jointValue μ`, so the
generic `IndepFun.integral_restrict_preimage_eq_mul` applies directly with
`f := rv.value`, `g := B.jointValue`, `E := {x}`.  We phrase the main lemma
against a `RegimedVar` since that is the exact shape consumed by `IndepCF`. -/

variable {P : POSystem}

/-- **Drop-of-conditioning (multiplied form).**  If a regimed variable `rv` is
independent of the counterfactual bundle `B`, then the integral of
`h ∘ B.jointValue` over the preimage `rv.value ⁻¹' {x}` factors as
`(μ (rv.value ⁻¹' {x})).toReal * ∫ h ∘ B.jointValue ∂μ`.

This is the core identity; the quotient form below divides through by
`(μ (rv.value ⁻¹' {x})).toReal`, which is valid whenever the event has
finite positive measure. -/
theorem POSystem.integral_restrict_value_eq_mul_of_IndepCF
    {α : Type*} [MeasurableSpace α]
    {rv : RegimedVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF rv B μ)
    {h : (∀ i : Fin B.n, B.type i) → ℝ}
    (hh_meas : Measurable h) (x : α) (hx : MeasurableSet ({x} : Set α)) :
    ∫ ω in rv.value ⁻¹' {x}, h (B.jointValue ω) ∂μ
      = (μ (rv.value ⁻¹' {x})).toReal * ∫ ω, h (B.jointValue ω) ∂μ :=
  hInd.toIndepFun.integral_restrict_preimage_eq_mul
    rv.measurable_value.aemeasurable B.measurable_jointValue.aemeasurable
    hx (rv.measurable_value hx)
    hh_meas.aestronglyMeasurable

/-- **Drop-of-conditioning for the factual event.**  Specialisation of
`POSystem.integral_restrict_value_eq_mul_of_IndepCF` to a factual `POVar`,
using `POVar.event` directly. -/
theorem POSystem.integral_event_eq_mul_of_IndepCF
    {α : Type*} [MeasurableSpace α]
    {a : POVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF (RegimedVar.ofFactual a) B μ)
    {h : (∀ i : Fin B.n, B.type i) → ℝ}
    (hh_meas : Measurable h) (x : α) (hx : MeasurableSet ({x} : Set α)) :
    ∫ ω in a.event x, h (B.jointValue ω) ∂μ
      = (μ (a.event x)).toReal * ∫ ω, h (B.jointValue ω) ∂μ := by
  -- `a.event x = (RegimedVar.ofFactual a).value ⁻¹' {x}` by definition, since
  -- `(ofFactual a).value = a.cf Regime.empty = a.factual` and
  -- `a.event x = a.factual ⁻¹' {x}`.
  have hev : a.event x = (RegimedVar.ofFactual a).value ⁻¹' {x} := by
    rfl
  rw [hev]
  simpa using
    (POSystem.integral_restrict_value_eq_mul_of_IndepCF hInd hh_meas x hx)

/-- **Drop-of-conditioning (quotient form).** Suppose [a regimed variable `rv`
is independent of a counterfactual bundle `B`](hyp:hInd), where [`h` is a
measurable function of the bundle's joint value](hyp:hh_meas) and [`{x}` is a
measurable singleton in the range of `rv`](hyp:hx). If [the event `{rv = x}`
has positive](hyp:hμA_ne_zero) and [finite](hyp:hμA_ne_top) measure, then
[the event-level conditional expectation of `h` composed with the bundle's
joint value, given `{rv = x}`, equals the unconditional integral of the same
composite](goal). -/
theorem POSystem.eventCondExp_eq_integral_of_IndepCF
    {α : Type*} [MeasurableSpace α]
    {rv : RegimedVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF rv B μ)
    {h : (∀ i : Fin B.n, B.type i) → ℝ}
    (hh_meas : Measurable h) {x : α}
    (hx : MeasurableSet ({x} : Set α))
    (hμA_ne_zero : μ (rv.value ⁻¹' {x}) ≠ 0)
    (hμA_ne_top : μ (rv.value ⁻¹' {x}) ≠ ⊤) :
    normalizedRestrictedIntegral μ (rv.value ⁻¹' {x}) (fun ω => h (B.jointValue ω))
      = ∫ ω, h (B.jointValue ω) ∂μ := by
  simp only [condexp_simps]
  rw [POSystem.integral_restrict_value_eq_mul_of_IndepCF hInd hh_meas x hx]
  have hpos : (μ (rv.value ⁻¹' {x})).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    exact ⟨hμA_ne_zero, hμA_ne_top⟩
  field_simp

/-- **Drop-of-conditioning on factual events (quotient form).**  Specialisation
of the above to the factual event `a.event x`. -/
theorem POSystem.eventCondExp_event_eq_integral_of_IndepCF
    {α : Type*} [MeasurableSpace α]
    {a : POVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF (RegimedVar.ofFactual a) B μ)
    {h : (∀ i : Fin B.n, B.type i) → ℝ}
    (hh_meas : Measurable h) {x : α}
    (hx : MeasurableSet ({x} : Set α))
    (hμA_ne_zero : μ (a.event x) ≠ 0)
    (hμA_ne_top : μ (a.event x) ≠ ⊤) :
    normalizedRestrictedIntegral μ (a.event x) (fun ω => h (B.jointValue ω))
      = ∫ ω, h (B.jointValue ω) ∂μ := by
  have hev : a.event x = (RegimedVar.ofFactual a).value ⁻¹' {x} := rfl
  rw [hev] at hμA_ne_zero hμA_ne_top ⊢
  exact POSystem.eventCondExp_eq_integral_of_IndepCF
    hInd hh_meas hx hμA_ne_zero hμA_ne_top

/-- **Consistency on an event for `normalizedRestrictedIntegral`.** Given
[a consistent potential-outcome system](hyp:hC), [an outcome variable `y`](hyp:y),
[a conditioning variable `a`](hyp:a), [a level `a₀`](hyp:a₀), and [a measure `μ`](hyp:μ),
if [the event `{a = a₀}` is measurable](hyp:ha₀) and
[`y` and `a` have distinct variable labels](hyp:hvw), then
[the normalized restricted integrals of the counterfactual and factual outcomes are equal](goal).
These totalized quantities are conditional means only when the event has positive finite measure.

This is the shared rewrite underlying Manski `MTR`/`MTS` and, via the finite-partition total law,
the integrated MIV bounds. -/
theorem POVar.eventCondExp_cfUnder_eq_factual_on_event
    {P : POSystem} {β : Type*}
    [MeasurableSpace β]
    (hC : P.Consistency)
    (y : POVar P ℝ) (a : POVar P β) (a₀ : β)
    (ha₀ : MeasurableSet (a.event a₀)) (hvw : y.v ≠ a.v)
    (μ : Measure P.Ω) :
    normalizedRestrictedIntegral μ (a.event a₀) (y.cfUnder a a₀)
      = normalizedRestrictedIntegral μ (a.event a₀) y.factual := by
  simp only [condexp_simps]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun ha₀ ?_
  intro ω hω
  exact POVar.cf_eq_factual_on_event hC y a a₀ hvw hω

/-- **Drop-of-conditioning on an event, given a bundle relabeling of the
integrand.** Suppose [a factual variable `a` is independent of a
counterfactual bundle `B`](hyp:hInd), where [`h` is a measurable function of
the bundle's joint value](hyp:hh_meas) and [`{x}` is a measurable singleton in
the range of `a`](hyp:hx). If [the factual integrand `factualF` agrees,
almost everywhere on the event `{a = x}`, with `h` composed with the bundle's
joint value](hyp:hF_eq), and that event has [positive](hyp:hμA_ne_zero) and
[finite](hyp:hμA_ne_top) measure, then [the event-level conditional
expectation of `factualF` given `{a = x}` equals the unconditional integral of
`h` composed with the bundle's joint value](goal).

This is a generic probability lemma: it does not assume causal consistency.
Callers may derive `hF_eq` from consistency, but this theorem uses only the
supplied almost-everywhere equality. It is the workhorse of LATE-style
first-stage and reduced-form proofs. -/
theorem POSystem.eventCondExp_of_ae_eq_IndepCF
    {α : Type*} [MeasurableSpace α]
    {a : POVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF (RegimedVar.ofFactual a) B μ)
    {factualF : P.Ω → ℝ}
    {h : (∀ i : Fin B.n, B.type i) → ℝ} (hh_meas : Measurable h)
    {x : α}
    (hx : MeasurableSet ({x} : Set α))
    (hF_eq : factualF =ᵐ[μ.restrict (a.event x)] fun ω => h (B.jointValue ω))
    (hμA_ne_zero : μ (a.event x) ≠ 0)
    (hμA_ne_top : μ (a.event x) ≠ ⊤) :
    normalizedRestrictedIntegral μ (a.event x) factualF = ∫ ω, h (B.jointValue ω) ∂μ := by
  simp only [condexp_simps]
  rw [MeasureTheory.integral_congr_ae hF_eq]
  rw [POSystem.integral_event_eq_mul_of_IndepCF hInd hh_meas x hx]
  have hpos : (μ (a.event x)).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    exact ⟨hμA_ne_zero, hμA_ne_top⟩
  field_simp

end

end PO
end Causalean
