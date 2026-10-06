module
public import Causalean.Stat.CLT.BerryEsseen.TriangularCosineIntegral

/-! # Triangular sine-product coefficients

This exact coefficient evaluation supplies the algebraic part of the Prawitz
Abel-series assembly. The sinc formulation includes coincident frequencies,
so the coefficient at an integer spatial coordinate needs no limiting argument.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- At [any two real frequencies a and b](hyp:a,b), [the triangularly weighted
integral over [0, 1] of (1 − t)·sin(2πat)·sin(2πbt) equals one quarter of
the difference sinc(π(a − b))² − sinc(π(a + b))²](goal). -/
theorem triangular_sine_product_integral (a b : ℝ) :
    (∫ t in (0 : ℝ)..1, (1 - t) * Real.sin (2 * Real.pi * a * t) *
      Real.sin (2 * Real.pi * b * t)) =
    (Real.sinc (Real.pi * (a - b)) ^ 2 -
      Real.sinc (Real.pi * (a + b)) ^ 2) / 4 := by
  have hpoint (t : ℝ) :
      (1 - t) * Real.sin (2 * Real.pi * a * t) * Real.sin (2 * Real.pi * b * t) =
      (1 / 2 : ℝ) * ((1 - t) * Real.cos (2 * Real.pi * (a - b) * t) -
        (1 - t) * Real.cos (2 * Real.pi * (a + b) * t)) := by
    have h := Real.two_mul_sin_mul_sin (2 * Real.pi * a * t) (2 * Real.pi * b * t)
    rw [show 2 * Real.pi * a * t - 2 * Real.pi * b * t =
      2 * Real.pi * (a - b) * t by ring,
      show 2 * Real.pi * a * t + 2 * Real.pi * b * t =
      2 * Real.pi * (a + b) * t by ring] at h
    calc
      _ = (1 / 2 : ℝ) * (1 - t) *
          (2 * Real.sin (2 * Real.pi * a * t) * Real.sin (2 * Real.pi * b * t)) := by ring
      _ = _ := by rw [h]; ring
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((show Continuous (fun t : ℝ => (1 - t) * Real.cos (2 * Real.pi * (a - b) * t))
        by fun_prop).intervalIntegrable 0 1)
      ((show Continuous (fun t : ℝ => (1 - t) * Real.cos (2 * Real.pi * (a + b) * t))
        by fun_prop).intervalIntegrable 0 1),
    triangular_cosine_integral, triangular_cosine_integral]
  ring

end Causalean.Stat.CLT.BerryEsseen
