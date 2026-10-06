module
public import Causalean.Stat.CLT.BerryEsseen.SincSquaredInversion

/-! # Fubini step for the fourth-power sinc transform

The squared-sinc factor and its integrable Fourier triangle give an absolutely
integrable double integral. Swapping its order is the analytic step in the
fourth-power sinc transform, isolated from Fourier normalization.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- At [any frequency t](hyp:t), [the integral over x of the Fourier exponential
times squared sinc times the inverse transform of the triangle
u ↦ π·max(1 − |u|/2, 0) equals the integral over u of the triangle times the
Fourier integral of squared sinc at t − u](goal): the spatial and frequency
integrals may be exchanged. -/
theorem sincSquared_triangle_integral_swap (t : ℝ) :
    (∫ x : ℝ,
      (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        ((Real.sinc x ^ 2 : ℝ) : ℂ)) *
        (∫ u : ℝ,
          Complex.exp (((-u * x : ℝ) : ℂ) * Complex.I) *
            ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ))) =
      ∫ u : ℝ,
        ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ) *
          (∫ x : ℝ,
            Complex.exp (((((t - u) * x : ℝ) : ℂ) * Complex.I)) *
              ((Real.sinc x ^ 2 : ℝ) : ℂ)) := by
  let F : ℝ → ℝ → ℂ := fun x u =>
    (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
      ((Real.sinc x ^ 2 : ℝ) : ℂ)) *
      (Complex.exp (((-u * x : ℝ) : ℂ) * Complex.I) *
        ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ))
  have hmajor : Integrable (fun z : ℝ × ℝ =>
      ‖Real.sinc z.1 ^ 2‖ * ‖Real.pi * max (1 - |z.2| / 2) 0‖)
      (volume.prod volume) :=
    sincSquared_integrable.norm.mul_prod sincTriangle_integrable.norm
  have hF : Integrable (Function.uncurry F) (volume.prod volume) := by
    apply Integrable.mono' hmajor
    · have hc : Continuous (Function.uncurry F) := by
        dsimp [F, Function.uncurry]
        fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards with z
      dsimp [F, Function.uncurry]
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_mul]
  have hswap := integral_integral_swap hF
  calc
    _ = ∫ x : ℝ, ∫ u : ℝ, F x u := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [F]
      rw [integral_const_mul]
    _ = ∫ u : ℝ, ∫ x : ℝ, F x u := hswap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp [F]
      calc
        (∫ x : ℝ, F x u) = ∫ x : ℝ,
            ((Real.pi * max (1 - |u| / 2) 0 : ℝ) : ℂ) *
              (Complex.exp (((((t - u) * x : ℝ) : ℂ) * Complex.I)) *
                ((Real.sinc x ^ 2 : ℝ) : ℂ)) := by
          apply integral_congr_ae
          filter_upwards with x
          have hexp : Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((-u * x : ℝ) : ℂ) * Complex.I) =
              Complex.exp (((((t - u) * x : ℝ) : ℂ) * Complex.I)) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
          dsimp [F]
          rw [← hexp]
          ring
        _ = _ := integral_const_mul _ _

end Causalean.Stat.CLT.BerryEsseen
