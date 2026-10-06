module
public import Causalean.Stat.CLT.BerryEsseen.SincFourthFubini
public import Causalean.Stat.CLT.BerryEsseen.SincTriangleConvolution

/-! # Fourier transform of fourth-power sinc

The transform of `sinc⁴` is the self-convolution of the squared-sinc
Fourier triangle, divided by `2π`. This identity is the unscaled analytic
input for the compact-frequency probability kernel.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- At [every frequency t](hyp:t), [the Fourier integral of the fourth power of
sinc equals 1/(2π) times the self-convolution at t of the squared-sinc
triangle u ↦ π·max(1 − |u|/2, 0)](goal). In particular this identity holds
at zero and at the support endpoints. -/
theorem sincFourth_fourier_triangleConvolution (t : ℝ) :
    ∫ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          ((Real.sinc x ^ 4 : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) *
        ∫ u : ℝ,
          (Real.pi * max (1 - |u| / 2) 0) *
            (Real.pi * max (1 - |t - u| / 2) 0) : ℝ) : ℂ) := by
  /- Write sinc⁴ as sinc² * sinc² and substitute
  `sincSquared_fourier_inversion` into the second factor. Move its constant
  `1/(2π)` outside the x-integral with `integral_mul_const`, then apply
  `sincSquared_triangle_integral_swap`. For each u, rewrite the inner
  integral by `sincSquared_fourier_triangle (t - u)`. Finally commute the
  real-to-complex cast with the integrable convolution (`integral_ofReal`),
  and use `integral_const_mul` for the outer constant.
  The existing Fubini lemma already handles all double-integrability issues;
  no Fourier-product theorem or new analytic assumption is needed. -/
  calc
    _ = ∫ x : ℝ,
          (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            ((Real.sinc x ^ 2 : ℝ) : ℂ)) *
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ u : ℝ,
                Complex.exp (((-u * x : ℝ) : ℂ) * Complex.I) *
                  ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← sincSquared_fourier_inversion x]
      push_cast
      ring
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x : ℝ,
            (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              ((Real.sinc x ^ 2 : ℝ) : ℂ)) *
              (∫ u : ℝ,
                Complex.exp (((-u * x : ℝ) : ℂ) * Complex.I) *
                  ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u : ℝ,
            ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ) *
              (∫ x : ℝ,
                Complex.exp (((((t - u) * x : ℝ) : ℂ) * Complex.I)) *
                  ((Real.sinc x ^ 2 : ℝ) : ℂ)) := by
      rw [sincSquared_triangle_integral_swap t]
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u : ℝ,
            (((Real.pi * max (1 - |u| / 2) 0) *
              (Real.pi * max (1 - |t - u| / 2) 0) : ℝ) : ℂ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      rw [sincSquared_fourier_triangle (t - u)]
      push_cast
      rfl
    _ = _ := by
      rw [integral_complex_ofReal]
      push_cast
      ring

end Causalean.Stat.CLT.BerryEsseen
