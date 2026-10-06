/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Regression-function representatives

A lightweight predicate `IsRegressionFunction μ X g f` saying that `f : ℝ → ℝ`
represents `E[g | X = ·]` via the integral identity on every measurable slice
`X ⁻¹' A`, with `X` required to be almost-everywhere measurable. Used by the
RDD-style identification theorems (sharp and fuzzy).

The general measurable-preimage characterization of conditional expectation
lives in `Causalean.Mathlib.MeasureTheory.CondExpPreimage`. This predicate is a
specialized interface for theorem statements that only require a concrete
regression representative; no adapter between the two interfaces is provided
in this file.
-/

module
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Map

/-! # Regression Function Representatives

This file provides a measure-theoretic predicate saying that a real function is
a concrete representative of a conditional mean of one real random variable
given another. The predicate is used as a lightweight interface in
RDD-style potential-outcome identification statements.

The central structure is `IsRegressionFunction μ X g f`, which requires
almost-everywhere measurability of the conditioning variable, measurability of
the representative, integrability, and equality of slice integrals over every
measurable event in the range of `X`. The file also proves pushforward
integrability of representatives, closure under subtraction, and
almost-everywhere equality of two representatives when the represented
responses are a.e. equal. The general conditional-expectation characterization
for measurable preimages is in `Causalean.Mathlib.MeasureTheory.CondExpPreimage`;
this file does not yet connect the two APIs. -/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory

/-- A regression-function representative for the conditional mean of a response `g`
given a [conditioning variable `X` that is `μ`-almost-everywhere
measurable](hyp:aemeasurable_conditioner): a candidate function `f` on the real
line that is [measurable](hyp:measurable), for which [the response `g` is
integrable](hyp:integrable_response) and [the composite `f ∘ X` is
integrable](hyp:integrable_compose), and such that [the integral of `g` over every
measurable event determined by `X` equals the integral of `f ∘ X` over that same
event](hyp:integral_preimage_eq).

This is a concrete representative of the regression function `E[g | X = x]`,
encoded by the integral identity on every measurable slice of `X`. -/
structure IsRegressionFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (g : Ω → ℝ) (f : ℝ → ℝ) : Prop where
  aemeasurable_conditioner : AEMeasurable X μ
  measurable : Measurable f
  integrable_response : Integrable g μ
  integrable_compose : Integrable (fun ω => f (X ω)) μ
  integral_preimage_eq :
    ∀ A : Set ℝ, MeasurableSet A →
      (∫ ω in X ⁻¹' A, g ω ∂μ) = ∫ ω in X ⁻¹' A, f (X ω) ∂μ

namespace IsRegressionFunction

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ} {g : Ω → ℝ} {f : ℝ → ℝ}

/-- If [`f` represents the conditional mean of `g` given `X`](hyp:h), then
[`f` is integrable under the pushforward measure `μ.map X`](goal). -/
lemma integrable_pushforward (h : IsRegressionFunction μ X g f) :
    Integrable f (μ.map X) := by
  rw [integrable_map_measure h.measurable.aestronglyMeasurable
    h.aemeasurable_conditioner]
  exact h.integrable_compose

end IsRegressionFunction

/-- If [`f₁` represents the conditional mean of `g₁` given `X`](hyp:h₁) and
[`f₂` represents the conditional mean of `g₂` given `X`](hyp:h₂), then [their
difference represents the conditional mean of `g₁ - g₂` given `X`](goal). -/
lemma IsRegressionFunction.sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {g₁ g₂ : Ω → ℝ} {f₁ f₂ : ℝ → ℝ}
    (h₁ : IsRegressionFunction μ X g₁ f₁)
    (h₂ : IsRegressionFunction μ X g₂ f₂) :
    IsRegressionFunction μ X (fun ω => g₁ ω - g₂ ω) (fun x => f₁ x - f₂ x) where
  aemeasurable_conditioner := h₁.aemeasurable_conditioner
  measurable := h₁.measurable.sub h₂.measurable
  integrable_response := h₁.integrable_response.sub h₂.integrable_response
  integrable_compose := h₁.integrable_compose.sub h₂.integrable_compose
  integral_preimage_eq A hA := by
    have h_lhs :
        (∫ ω in X ⁻¹' A, g₁ ω - g₂ ω ∂μ)
          = (∫ ω in X ⁻¹' A, g₁ ω ∂μ) - ∫ ω in X ⁻¹' A, g₂ ω ∂μ :=
      integral_sub h₁.integrable_response.integrableOn
        h₂.integrable_response.integrableOn
    have h_rhs :
        (∫ ω in X ⁻¹' A, f₁ (X ω) - f₂ (X ω) ∂μ)
          = (∫ ω in X ⁻¹' A, f₁ (X ω) ∂μ) - ∫ ω in X ⁻¹' A, f₂ (X ω) ∂μ :=
      integral_sub h₁.integrable_compose.integrableOn
        h₂.integrable_compose.integrableOn
    rw [h_lhs, h_rhs, h₁.integral_preimage_eq A hA, h₂.integral_preimage_eq A hA]

/-- If [two response variables `g₁` and `g₂` are `μ`-almost-everywhere
equal](hyp:hg), and [`f₁` is a regression-function representative of
the conditional mean of `g₁` given `X`](hyp:h₁) while [`f₂` is a
regression-function representative of the conditional mean of `g₂` given
`X`](hyp:h₂), then [`f₁` and `f₂` agree `(μ.map X)`-almost everywhere](goal).

Useful for collapsing two equivalent representatives of the same conditional
expectation. -/
lemma IsRegressionFunction.aeEq_of_aeEq_response
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {g₁ g₂ : Ω → ℝ} {f₁ f₂ : ℝ → ℝ}
    (hg : g₁ =ᵐ[μ] g₂)
    (h₁ : IsRegressionFunction μ X g₁ f₁)
    (h₂ : IsRegressionFunction μ X g₂ f₂) :
    f₁ =ᵐ[μ.map X] f₂ := by
  refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq
    f₁ f₂ h₁.integrable_pushforward h₂.integrable_pushforward ?_
  intro A hA _
  have h_pull₁ :
      (∫ x in A, f₁ x ∂(μ.map X)) = ∫ ω in X ⁻¹' A, f₁ (X ω) ∂μ :=
    setIntegral_map (μ := μ) (g := X) (f := f₁) hA
      h₁.measurable.aestronglyMeasurable h₁.aemeasurable_conditioner
  have h_pull₂ :
      (∫ x in A, f₂ x ∂(μ.map X)) = ∫ ω in X ⁻¹' A, f₂ (X ω) ∂μ :=
    setIntegral_map (μ := μ) (g := X) (f := f₂) hA
      h₂.measurable.aestronglyMeasurable h₂.aemeasurable_conditioner
  have h_eq₁ :
      (∫ ω in X ⁻¹' A, f₁ (X ω) ∂μ) = ∫ ω in X ⁻¹' A, g₁ ω ∂μ :=
    (h₁.integral_preimage_eq A hA).symm
  have h_eq₂ :
      (∫ ω in X ⁻¹' A, f₂ (X ω) ∂μ) = ∫ ω in X ⁻¹' A, g₂ ω ∂μ :=
    (h₂.integral_preimage_eq A hA).symm
  have h_g_eq :
      (∫ ω in X ⁻¹' A, g₁ ω ∂μ) = ∫ ω in X ⁻¹' A, g₂ ω ∂μ :=
    integral_congr_ae (ae_restrict_of_ae hg)
  rw [h_pull₁, h_pull₂, h_eq₁, h_eq₂, h_g_eq]

end PO
end Causalean
