module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Data.Real.Sign
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Prawitz's compact spectral smoothing filter

These explicit functions separate the analytic prerequisites of sharp CDF
smoothing from probability laws. Frequencies are in radians. The singular
value at zero is assigned zero; all later integrals are Lebesgue integrals,
so this endpoint convention has no effect on their value.

Reference: Tyurin, arXiv:0912.0726, Prawitz's smoothing inequality and its
displayed filter.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The cotangent weight at frequency t is (1 − t)·cot(πt) + 1/π, with the
cotangent written as cos(πt)/sin(πt). It is the sine-part weight of Prawitz's
approximation to the sign function and is used on 0 < t < 1; at points where
sin(πt) vanishes the quotient is assigned zero. -/
noncomputable def prawitzSineWeight (t : ℝ) : ℝ :=
  (1 - t) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t) + 1 / Real.pi

/-- Prawitz's complex spectral filter at frequency t is zero when t = 0 or
|t| > 1, and otherwise has real part the triangular weight (1 − |t|)/2 and
imaginary part ((1 − |t|)·cot(πt) + sign(t)/π)/2, with cot(πt) written as
cos(πt)/sin(πt). At t = ±1, where the sine vanishes, the quotient is assigned
zero, so the value there is ±i/(2π). -/
noncomputable def prawitzKernel (t : ℝ) : ℂ :=
  if t = 0 ∨ 1 < |t| then 0 else
    ((1 - |t|) / 2 : ℝ) +
      (((1 - |t|) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t) +
        Real.sign t / Real.pi) / 2 : ℝ) * Complex.I

/-- Prawitz's band-limited approximation to the sign function at a point y is
2·∫ over t in [0, 1] of w(t)·sin(ty), where w(t) = (1 − t)·cot(πt) + 1/π is
the cotangent weight. Frequencies are in radians and confined to the unit
band. -/
noncomputable def prawitzSignApprox (y : ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1, prawitzSineWeight t * Real.sin (t * y)

end Causalean.Stat.CLT.BerryEsseen
