module
public import Causalean.Mathlib.Analysis.Fourier.Estimate
public import Causalean.Mathlib.Analysis.Fourier.MultiplierBounds

/-!
# Weighted inverse Gaussian multiplier specialization

This theorem combines the frequency norm bounds with the reusable scaled Fourier
estimate, keeping every profile constant visible. It is independent of subsequent
physical-space averaging, so the frequency specialization can be checked on its own.
The multiplier profile and all inversion hypotheses are supplied by the caller;
the weighted physical-space bound is derived here.
-/

public section

open MeasureTheory Set
open scoped FourierTransform
namespace Causalean.Mathlib.Analysis.Fourier

/-- [A complex frequency profile](hyp:F) with [one continuous derivative and compact spectral support](hyp:hF,hcompact), [a Gaussian scale parameter](hyp:σ), and [integrable inverse transforms of the multiplier and its derivative](hyp:hinv,hinvD) give [admissible compact inverse-Fourier data for the inverse-Gaussian multiplier](goal). -/
theorem inverseGaussian_compactInverseData (F : ℝ → ℂ) (σ : ℝ)
    (hF : ContDiff ℝ 1 F) (hcompact : HasCompactSupport F)
    (hinv : Integrable (𝓕⁻ (inverseGaussian σ F)))
    (hinvD : Integrable (𝓕⁻ (deriv (inverseGaussian σ F)))) :
    CompactInverseData (inverseGaussian σ F) := by
  exact ⟨inverseGaussian_contDiff F σ hF,
    inverseGaussian_hasCompactSupport F σ hcompact, hinv, hinvD⟩

/-- For [a compactly supported continuously differentiable frequency profile F](hyp:F,hF,hcompact), [a moment exponent κ between zero and two](hyp:κ,hκ0,hκ2), [a nonnegative Gaussian scale σ and positive bandwidth h](hyp:σ,h,hσ,hh), and [nonnegative envelope constants a and b](hyp:a,b,ha,hb), suppose [F vanishes outside the interval of radius 3/(πh) around zero, |F| ≤ a·h and |F′| ≤ b·h² everywhere](hyp:hsupport,hbound,hderiv), and [the inverse Fourier transforms of the inverse-Gaussian multiplier of F and of its derivative are integrable](hyp:hinv,hinvD). Then, writing g for the inverse Fourier transform of that multiplier, [|v|^κ·|g(v)|² is integrable and its integral is at most (6/π)·(a² + (2π)⁻²·(b + 12π·a)²)·h^(κ+1)·(1 + σ/h)⁴·exp(36·(σ/h)²)](goal). -/
theorem inverseGaussian_weightedEnergy_le (F : ℝ → ℂ) (κ σ h a b : ℝ)
    (hF : ContDiff ℝ 1 F) (hcompact : HasCompactSupport F)
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) (hh : 0 < h) (hσ : 0 ≤ σ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsupport : Function.support F ⊆ Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)))
    (hbound : ∀ ξ, ‖F ξ‖ ≤ a * h) (hderiv : ∀ ξ, ‖deriv F ξ‖ ≤ b * h ^ 2)
    (hinv : Integrable (𝓕⁻ (inverseGaussian σ F)))
    (hinvD : Integrable (𝓕⁻ (deriv (inverseGaussian σ F)))) :
    Integrable (fun v => |v| ^ κ * ‖𝓕⁻ (inverseGaussian σ F) v‖ ^ 2) ∧
    weightedEnergy κ (𝓕⁻ (inverseGaussian σ F)) ≤
      ((6 / Real.pi) * (a ^ 2 + (2 * Real.pi)⁻¹ ^ 2 *
        (b + 12 * Real.pi * a) ^ 2)) *
      h ^ (κ + 1) * (1 + σ / h) ^ 4 * Real.exp (36 * (σ / h) ^ 2) := by
  have hG := inverseGaussian_compactInverseData F σ hF hcompact hinv hinvD
  refine ⟨(inverse_weightedEnergy_le (inverseGaussian σ F) hG κ hκ0 hκ2).1, ?_⟩
  have he := inverseGaussian_energy_le F σ h a hF.continuous hh ha hsupport hbound
  have heD := inverseGaussian_deriv_energy_le F σ h a b hF hh hσ ha hb
    hsupport hbound hderiv
  have hpoly : 1 ≤ (1 + σ / h) ^ 4 :=
    one_le_pow₀ (by linarith [div_nonneg hσ hh.le])
  have hpow1 : h ^ κ * h = h ^ (κ + 1) := by
    rw [Real.rpow_add hh, Real.rpow_one]
  have hpow3 : h ^ (κ - 2) * h ^ 3 = h ^ (κ + 1) := by
    rw [← Real.rpow_natCast h 3, ← Real.rpow_add hh]
    congr 1
    norm_num
    ring
  have hepoly : (6 / Real.pi) * a ^ 2 * h * Real.exp (36 * (σ / h) ^ 2) ≤
      (6 / Real.pi) * a ^ 2 * h * (1 + σ / h) ^ 4 *
        Real.exp (36 * (σ / h) ^ 2) := by
    have hp := mul_le_mul_of_nonneg_left hpoly
      (show 0 ≤ (6 / Real.pi) * a ^ 2 * h by positivity)
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hp)
      (Real.exp_pos _).le
  calc
    _ ≤ h ^ κ * energy (inverseGaussian σ F) +
        h ^ (κ - 2) * (2 * Real.pi)⁻¹ ^ 2 * energy (deriv (inverseGaussian σ F)) :=
      inverse_weightedEnergy_le_scaled (inverseGaussian σ F) hG κ h hκ0 hκ2 hh
    _ ≤ h ^ κ * ((6 / Real.pi) * a ^ 2 * h * (1 + σ / h) ^ 4 *
          Real.exp (36 * (σ / h) ^ 2)) +
        h ^ (κ - 2) * (2 * Real.pi)⁻¹ ^ 2 *
          ((6 / Real.pi) * (b + 12 * Real.pi * a) ^ 2 * h ^ 3 *
            (1 + σ / h) ^ 4 * Real.exp (36 * (σ / h) ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_left (he.trans hepoly) (by positivity))
        (mul_le_mul_of_nonneg_left heD (by positivity))
    _ = (6 / Real.pi) * a ^ 2 * (h ^ κ * h) * (1 + σ / h) ^ 4 *
          Real.exp (36 * (σ / h) ^ 2) +
        (6 / Real.pi) * (2 * Real.pi)⁻¹ ^ 2 * (b + 12 * Real.pi * a) ^ 2 *
          (h ^ (κ - 2) * h ^ 3) * (1 + σ / h) ^ 4 *
            Real.exp (36 * (σ / h) ^ 2) := by ring
    _ = _ := by rw [hpow1, hpow3]; ring

end Causalean.Mathlib.Analysis.Fourier
