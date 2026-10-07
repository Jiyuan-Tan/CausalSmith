module
public import Causalean.Mathlib.Analysis.RealInterpolation.Basic
public import Causalean.Mathlib.Analysis.RealInterpolation.Endpoint
public import Causalean.Mathlib.Analysis.RealInterpolation.Operators
public import Causalean.Mathlib.Analysis.RealInterpolation.Pointwise
public import Causalean.Mathlib.Analysis.RealInterpolation.ScalarIntegral
public import Causalean.Mathlib.Analysis.RealInterpolation.ScaleIntegral
public import Causalean.Mathlib.Analysis.RealInterpolation.ScaleMeasurability
public import Causalean.Mathlib.Analysis.RealInterpolation.SupportedTonelli
public import Causalean.Mathlib.Analysis.RealInterpolation.Weighted
public import Causalean.Mathlib.Analysis.RealInterpolation.WeightedMinimum
public import Causalean.Mathlib.Analysis.RealInterpolation.WeightedSupport

/-!
# Real interpolation by the quadratic K-method, with exact constants

For a pair of Banach spaces continuously embedded in a common vector space, the quadratic
K-functional K(t, v)² is the infimum of ‖v₀‖₀² + t²·‖v₁‖₁² over decompositions v = v₀ + v₁, and
the interpolation norm of exponent θ ∈ (0, 1) integrates t^(−2θ)·K(t, v)² against dt/t with
the normalizing constant 2·sin(πθ)/π (Chandler-Wilde, Hewett and Moiola, 2015). Two exact
statements are proved. A linear map bounded by A₀ and A₁ between the endpoint spaces is bounded
by A₀^(1−θ)·A₁^θ between the interpolation spaces. And the interpolation space between two
weighted L² spaces with weights w₀ and w₁, on an arbitrary measure space, is the weighted L²
space with weight w₀^(1−θ)·w₁^θ, with equal norms.

## Contents

* `RealInterpolation.Basic` — `kFunctionalSq`, `kNormSq`, the weighted norm `wNorm`.
* `RealInterpolation.Endpoint`, `RealInterpolation.Operators` — `exact_interpolation_operators`,
  the operator bound with constant A₀^(1−θ)·A₁^θ.
* `RealInterpolation.Pointwise`, `RealInterpolation.WeightedMinimum` — the K-functional of
  weighted L² spaces is the energy with the harmonic-type weight w₀·t²·w₁/(w₀ + t²·w₁)
  (`kFunctionalSq_wNorm`).
* `RealInterpolation.ScalarIntegral`, `RealInterpolation.ScaleIntegral`,
  `RealInterpolation.ScaleMeasurability` — the beta-integral evaluation of the normalizing
  constant, dilation in the scale variable and measurability in the scale.
* `RealInterpolation.WeightedSupport`, `RealInterpolation.SupportedTonelli` — σ-finiteness of the
  support of a function of finite energy and the Tonelli exchange it permits.
* `RealInterpolation.Weighted` — `weighted_l2_interpolation`, the weighted L² identity.

This file only gathers the modules above.
-/
