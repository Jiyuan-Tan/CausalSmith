/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# I.i.d. sample model

Causal-agnostic statistical primitive: an i.i.d. sample on a single ambient
measured space, matching Mathlib's `iIndepFun` / `IdentDistrib` idiom rather than
the product-space construction. Probability normalization is supplied separately
when applications require it. See `def:est-iid-sample` in
`doc/basic_concepts/po/estimation.tex`.

This file is intentionally project-agnostic and is a candidate for upstream
contribution to Mathlib.
-/

module
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! # I.i.d. Samples

This file provides the library's causal-agnostic model of an independent and
identically distributed sample relative to arbitrary ambient and population
measures; probability-measure instances are supplied separately when needed. It
also defines sample means of real-valued statistics along the first \(n\) sample
points, supplying the base object used by the limit and inference modules. -/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory

/-- An independent and identically distributed sample with marginal law `P`, realized as
[a sequence of sample points](hyp:Z) given by [measurable maps](hyp:meas) on a single
ambient measured space: [the family is mutually independent](hyp:indep), [identically
distributed](hyp:identDist), and [the law of each point is the measure `P`](hyp:law).
Neither the ambient measure nor `P` is required by this structure to be a probability measure.

* `Z i : Ω → X`             — the `i`-th sample point.
* `meas`                    — measurability of each `Z i`.
* `indep`                   — mutual independence of the family under `μ`.
* `identDist`               — every `Z i` is identically distributed with `Z 0`.
* `law`                     — the law of `Z 0` matches the population law `P`.

Together, `identDist` and `law` give `μ.map (Z i) = P` for all `i`. -/
structure IIDSample (Ω X : Type*) [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (P : Measure X) where
  Z : ℕ → Ω → X
  meas      : ∀ i, Measurable (Z i)
  indep     : iIndepFun Z μ
  identDist : ∀ i, IdentDistrib (Z 0) (Z i) μ μ
  law       : (μ.map (Z 0)) = P

namespace IIDSample

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- Each individual sample point of an i.i.d. sample is a measurable map from the ambient
measured space to the observation space.

This is the `meas` field with the sample index instantiated. The field itself is stated for
all indices at once, which the function-property tactics cannot use; this per-index form is
the one they can. -/
@[fun_prop]
theorem measurable_Z (S : IIDSample Ω X μ P) (i : ℕ) : Measurable (S.Z i) := S.meas i

/-- For [a measurable sample space carrying a measure](hyp:Ω,μ), [a measurable observation space carrying a population measure](hyp:X,P), [an independent and identically distributed sample from that population](hyp:S), [a real-valued statistic of one observation](hyp:f), and [a nonnegative integer sample size](hyp:n), the [sample mean](goal) is the function that assigns each sample-space outcome the average $n^{-1}\sum_{i<n} f(Z_i)$, with the reciprocal convention also applying when $n=0$.

This is the empirical mean over the first `n` observations. -/
noncomputable def sampleMean (S : IIDSample Ω X μ P) (f : X → ℝ) (n : ℕ) :
    Ω → ℝ :=
  fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (S.Z i ω)

/-- For [an i.i.d. sample `S`](hyp:S) [and any sample index `i`](hyp:i), [the pushforward law of
the `i`-th sample point equals the population law `P`](goal). -/
theorem map_eq (S : IIDSample Ω X μ P) (i : ℕ) : μ.map (S.Z i) = P := by
  rw [← (S.identDist i).map_eq, S.law]

end IIDSample
namespace IIDSample

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {μ : Measure Ω} {X : ℕ → Ω → E}

/-- Each [indexed family of random variables](hyp:X) whose coordinates are
[almost-everywhere measurable](hyp:hX) has [a coordinatewise measurable
modification](goal), [chosen by the standard measurable-representative
construction at every index](step:1). -/
noncomputable def measurableModification
    (X : ℕ → Ω → E) (hX : ∀ i, AEMeasurable (X i) μ) : ℕ → Ω → E :=
  fun i => (hX i).mk (X i)

/-- Under [coordinatewise almost-everywhere measurability](hyp:hX), [the
measurable modification at the specified index](hyp:i) [is measurable](goal). -/
@[fun_prop]
theorem measurableModification_measurable
    (hX : ∀ i, AEMeasurable (X i) μ) (i : ℕ) :
    Measurable (measurableModification X hX i) :=
  (hX i).measurable_mk

/-- Under [coordinatewise almost-everywhere measurability](hyp:hX), [the
measurable modification at the specified index](hyp:i) [equals the original
coordinate almost everywhere](goal). -/
theorem measurableModification_ae_eq
    (hX : ∀ i, AEMeasurable (X i) μ) (i : ℕ) :
    measurableModification X hX i =ᵐ[μ] X i :=
  (hX i).ae_eq_mk.symm

/-- [Coordinatewise almost-everywhere measurability](hyp:hX), [mutual
independence of the original coordinates](hyp:hindep), and [a common coordinate
law](hyp:hident) define [an IID sample of measurable representatives with the
original first-coordinate law](goal), [using the representatives](step:1),
[their measurability](step:2), [their independence](step:3), [their identical
distributions](step:4), and [their marginal law](step:5). -/
noncomputable def ofAEMeasurable
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X 0) (X i) μ μ) :
    IIDSample Ω E μ (μ.map (X 0)) where
  Z := measurableModification X hX
  meas := measurableModification_measurable hX
  indep := hindep.congr (fun i => (measurableModification_ae_eq hX i).symm)
  identDist := fun i => by
    refine ⟨(measurableModification_measurable hX 0).aemeasurable,
      (measurableModification_measurable hX i).aemeasurable, ?_⟩
    rw [Measure.map_congr (measurableModification_ae_eq hX 0),
      Measure.map_congr (measurableModification_ae_eq hX i)]
    exact (hident i).map_eq
  law := Measure.map_congr (measurableModification_ae_eq hX 0)

/-- [Coordinatewise almost-everywhere measurability](hyp:hX), [mutual
independence](hyp:hindep), [a common coordinate law](hyp:hident), and [a
specified index](hyp:i) imply [that the corresponding constructed sample
coordinate equals the original coordinate almost everywhere](goal). -/
theorem ofAEMeasurable_ae_eq
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X 0) (X i) μ μ) (i : ℕ) :
    (ofAEMeasurable hX hindep hident).Z i =ᵐ[μ] X i :=
  measurableModification_ae_eq hX i

/-- [Coordinatewise almost-everywhere measurability](hyp:hX), [a real-valued
statistic](hyp:ψ), and [a finite set of indices](hyp:s) imply [that the sum of
the statistic over the measurable modifications equals the original-coordinate
sum almost everywhere](goal). -/
theorem finite_sum_ae_eq
    (hX : ∀ i, AEMeasurable (X i) μ) (ψ : E → ℝ) (s : Finset ℕ) :
    (fun ω => ∑ i ∈ s, ψ (measurableModification X hX i ω)) =ᵐ[μ]
      (fun ω => ∑ i ∈ s, ψ (X i ω)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    filter_upwards [ih, measurableModification_ae_eq hX i] with ω hsum hi
    simp [Finset.sum_insert his, hsum, hi]

/-- [Coordinatewise almost-everywhere measurability](hyp:hX), [mutual
independence](hyp:hindep), [a common coordinate law](hyp:hident), [a
real-valued statistic](hyp:ψ), and [a sample size](hyp:n) imply [that the
measurable sample mean equals the original-coordinate sample mean almost
everywhere](goal). -/
theorem sampleMean_ae_eq
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X 0) (X i) μ μ)
    (ψ : E → ℝ) (n : ℕ) :
    (ofAEMeasurable hX hindep hident).sampleMean ψ n =ᵐ[μ]
      (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ψ (X i ω)) := by
  change (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    ψ (measurableModification X hX i ω)) =ᵐ[μ]
      (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ψ (X i ω))
  filter_upwards [finite_sum_ae_eq hX ψ (Finset.range n)] with ω hω
  exact congrArg ((n : ℝ)⁻¹ * ·) hω

end IIDSample


end Causalean.Stat
