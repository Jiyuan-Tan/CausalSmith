module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Data.Real.Sign
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Prawitz's compact spectral smoothing filter

These explicit functions separate the analytic prerequisites of sharp CDF
smoothing from probability laws. Frequencies are in radians. The singular
value at zero is assigned zero; all later integrals are Lebesgue integrals,
so this endpoint convention has no effect on their value.

Reference: Tyurin, arXiv:0912.0726, equation (praineq) and its displayed
filter. The fetched LaTeX source is in `tmp/mnar_round3_sources/arxiv.tex`.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The real cotangent weight on the positive unit frequency interval
determines the sine part of Prawitz's approximation to the sign function. -/
noncomputable def prawitzSineWeight (t : ℝ) : ℝ :=
  (1 - t) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t) + 1 / Real.pi

/-- Prawitz's complex spectral filter is supported on the unit interval;
its real part is triangular and its imaginary part is a cotangent correction. -/
noncomputable def prawitzKernel (t : ℝ) : ℂ :=
  if t = 0 ∨ 1 < |t| then 0 else
    ((1 - |t|) / 2 : ℝ) +
      (((1 - |t|) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t) +
        Real.sign t / Real.pi) / 2 : ℝ) * Complex.I

/-- Integrating the cotangent weight against the sine wave gives
Prawitz's unit-bandwidth approximation to the sign function. -/
noncomputable def prawitzSignApprox (y : ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1, prawitzSineWeight t * Real.sin (t * y)

end Causalean.Stat.CLT.BerryEsseen
