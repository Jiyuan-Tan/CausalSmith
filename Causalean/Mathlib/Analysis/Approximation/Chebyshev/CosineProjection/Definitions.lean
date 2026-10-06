module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Normalized cosine projection on the unit interval

Research-independent definitions for uniform design on `[0,1]`. Real functions are
defined on the real line, but all regularity assumptions below concern only the
closed unit interval. The extended norm uses a nonnegative integral, preserving
infinite values; the real norm is used only after integrability has been established.
The rank counts the constant mode: rank one means projection onto constants.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- [Uniform probability on the unit interval](goal) is Lebesgue measure restricted
to the closed interval from zero to one. -/
def uniformMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- [The normalized cosine mode](goal) with [index](hyp:j) at [position](hyp:x)
is one for the zero mode and square root of two times cosine of π times index
times position otherwise. -/
def cosineBasis (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then 1 else Real.sqrt 2 * Real.cos (Real.pi * (j : ℝ) * x)

/-- [The coefficient](goal) of a [function](hyp:f) in [mode](hyp:j) is its
uniform integral against that normalized mode. -/
def cosineCoefficient (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ x, f x * cosineBasis j x ∂uniformMeasure

/-- [The cosine polynomial](goal) at [rank](hyp:k) with [coefficients](hyp:a)
evaluated at [position](hyp:x) sums the modes with indices strictly below the rank. -/
def cosinePolynomial (k : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, a j * cosineBasis j x

/-- [The finite cosine projection](goal) of a [function](hyp:f), at
[rank](hyp:k) and [position](hyp:x), uses its uniform cosine coefficients. -/
def cosineProjection (k : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  cosinePolynomial k (cosineCoefficient f) x

/-- [The cosine span condition](goal) for a [function](hyp:p) at [rank](hyp:k)
means it equals a normalized cosine polynomial everywhere on the unit interval. -/
def InCosineSpan (k : ℕ) (p : ℝ → ℝ) : Prop :=
  ∃ a : ℕ → ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, p x = cosinePolynomial k a x

/-- [The real uniform L² norm](goal) of a [function](hyp:g) is the square root
of the integral of its squared absolute value. For nonintegrable functions the
real integral has Lean's default value; use the extended norm in that case. -/
def l2Norm (g : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ x, |g x| ^ 2 ∂uniformMeasure)

/-- [The extended uniform L² norm](goal) of a [function](hyp:g) is the square
root of the nonnegative integral of its squared absolute value. -/
def extendedL2Norm (g : ℝ → ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (|g x| ^ 2) ∂uniformMeasure) ^ (1 / 2 : ℝ)

/-- [The extended Hölder seminorm](goal) of a [function](hyp:f), with
[exponent](hyp:γ), is the supremum of its absolute increments divided by
distance to that exponent, over distinct points in the closed unit interval. -/
def holderSeminorm (f : ℝ → ℝ) (γ : ℝ) : ℝ≥0∞ :=
  ⨆ x : Set.Icc (0 : ℝ) 1, ⨆ z : Set.Icc (0 : ℝ) 1, ⨆ (_h : x ≠ z),
    ENNReal.ofReal (|f x - f z| / |(x : ℝ) - z| ^ γ)

/-- [A Hölder bound](goal) for a [function](hyp:f), [exponent](hyp:γ), and
[constant](hyp:H) is the increment inequality for every pair in the unit interval. -/
def HasHolderBound (f : ℝ → ℝ) (γ H : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
    |f x - f z| ≤ H * |x - z| ^ γ

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

