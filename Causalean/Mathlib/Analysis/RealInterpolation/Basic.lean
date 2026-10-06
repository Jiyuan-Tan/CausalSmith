module
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Normalized quadratic real interpolation

Extended endpoint norms encode membership by the value infinity. This module defines
the squared quadratic K-functional and its normalized real interpolation energy,
with exactly the normalization in Chandler-Wilde, Hewett, Moiola (2015), (8)--(9).
Weighted norms are defined on measurable functions modulo null sets. No endpoint
space, interpolation conclusion, or paper-specific statement is assumed here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- [Endpoint norms](hyp:n0,n1), [a positive scale](hyp:t), and [an ambient vector](hyp:v)
determine [the infimum of squared endpoint decomposition costs](goal).
The definition also makes sense at arbitrary real scales. -/
def kFunctionalSq {V : Type*} [AddCommGroup V] (n0 n1 : V → ℝ≥0∞)
    (t : ℝ) (v : V) : ℝ≥0∞ :=
  ⨅ (v0 : V) (v1 : V) (_ : v = v0 + v1),
    n0 v0 ^ 2 + ENNReal.ofReal (t ^ 2) * n1 v1 ^ 2

/-- [An interpolation exponent](hyp:θ) determines [the squared quadratic normalization
constant](goal), equal to twice the sine of π times the exponent divided by π. -/
def normalizationSq (θ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.sin (Real.pi * θ) / Real.pi)

/-- [Endpoint norms](hyp:n0,n1), [an exponent](hyp:θ), and [a vector](hyp:v)
determine [the normalized squared quadratic real interpolation norm](goal).
Integration uses Lebesgue measure on the positive real scales. -/
def kNormSq {V : Type*} [AddCommGroup V] (n0 n1 : V → ℝ≥0∞)
    (θ : ℝ) (v : V) : ℝ≥0∞ :=
  normalizationSq θ * ∫⁻ t in Ioi (0 : ℝ),
    ENNReal.ofReal (t ^ (-1 - 2 * θ)) * kFunctionalSq n0 n1 t v

/-- [A continuous linear embedding](hyp:i) and [an ambient vector](hyp:v) determine
[the endpoint norm extended by infinity outside the embedding's range](goal).
Injectivity is imposed by theorems that identify this value with an endpoint norm. -/
def embeddedNorm {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (i : E →L[ℝ] V)
    (v : V) : ℝ≥0∞ :=
  ⨅ (e : E) (_ : i e = v), ENNReal.ofReal ‖e‖

/-- [A weight](hyp:w), [a measure](hyp:μ), and [a measurable complex function modulo
null sets](hyp:f) determine [its weighted L² norm](goal), allowing infinity. -/
def wNorm {S : Type*} [MeasurableSpace S] (w : S → ℝ≥0∞) (μ : Measure S)
    (f : S →ₘ[μ] ℂ) : ℝ≥0∞ :=
  ENNReal.rpow (∫⁻ x, w x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) (1 / 2)

/-- [Two endpoint weights](hyp:a,b) and [a scale](hyp:t) determine [the harmonic
quadratic minimum weight](goal). Only positive finite weights are used in identities. -/
def harmonicWeight (a b : ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  a * (ENNReal.ofReal (t ^ 2) * b) / (a + ENNReal.ofReal (t ^ 2) * b)

/-- [The square of the weighted L² norm](goal) is the weighted squared energy of
[the function](hyp:f) for [the weight and measure](hyp:w,μ), including infinite energies. -/
theorem wNorm_sq {S : Type*} [MeasurableSpace S] (w : S → ℝ≥0∞)
    (μ : Measure S) (f : S →ₘ[μ] ℂ) :
    wNorm w μ f ^ 2 = ∫⁻ x, w x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  unfold wNorm
  simpa using ENNReal.rpow_inv_natCast_pow (n := 2) (by decide)
    (∫⁻ x, w x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ)

end Causalean.Mathlib.Analysis.RealInterpolation
