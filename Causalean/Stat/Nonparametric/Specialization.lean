module
public import Causalean.Mathlib.Analysis.Fourier.WeightedSpecialization
public import Causalean.Stat.Nonparametric.GaussianTransfer

/-!
# Inverse Gaussian sinc-six specialization recipe

A caller supplies a compact C¹ profile F with the sinc-six support and two uniform
heights. The sixth convolution of the normalized sinc boxes has exactly the support
radius `3/(πh)` and heights of orders h and h². No paper-specific construction is
imported. Standard absolute integrability of the inverse multiplier, of its derivative
transform, and of the design/noise joint integrand may be supplied.

The recipe derives the whole quantitative estimate, including Gaussian averaging:
`Vq ≤ C h^(κ+1) (1+σ/h)^10 exp(36 (σ/h)^2)` with an explicit C depending
only on the two profile heights. For a real-valued kernel represented by the real
part of the complex inverse transform, `Complex.abs_re_le_norm` transfers the
same upper bound to its squared real variance integral.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped FourierTransform
open Causalean.Mathlib.Analysis.Fourier
namespace Causalean.Stat.Nonparametric

/-- [A compact continuously differentiable frequency profile](hyp:F,hF,hcompact), [a moment exponent in the interval from zero to two](hyp:κ,hκ0,hκ2), [a nonnegative Gaussian noise scale and bandwidth in the stated range](hyp:σ,h,hσ,hσmax,hh,hhmax), [nonnegative envelope constants](hyp:a,b,ha,hb), [sinc-six spectral support and uniform envelope bounds](hyp:hsupport,hbound,hderiv), and [integrable inverse-transform and joint design-noise quantities](hyp:hinv,hinvD,hjoint) imply [the stated explicit Gaussian-shifted variance bound](goal). -/
theorem inverseGaussian_shiftedVariance_le (F : ℝ → ℂ) (κ σ h a b : ℝ)
    (hF : ContDiff ℝ 1 F) (hcompact : HasCompactSupport F)
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) (hh : 0 < h) (hhmax : h ≤ 1 / 4)
    (hσ : 0 ≤ σ) (hσmax : σ ≤ 1 / 4) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsupport : Function.support F ⊆ Icc (-(3 / (Real.pi * h))) (3 / (Real.pi * h)))
    (hbound : ∀ ξ, ‖F ξ‖ ≤ a * h) (hderiv : ∀ ξ, ‖deriv F ξ‖ ≤ b * h ^ 2)
    (hinv : Integrable (𝓕⁻ (inverseGaussian σ F)))
    (hinvD : Integrable (𝓕⁻ (deriv (inverseGaussian σ F))))
    (hjoint : Integrable
      (fun p : ℝ × ℝ => |p.1| ^ κ *
        ‖𝓕⁻ (inverseGaussian σ F) (p.1 + σ * p.2)‖ ^ 2)
      (volume.prod (gaussianReal 0 1))) :
    shiftedVariance κ σ (𝓕⁻ (inverseGaussian σ F)) ≤
      (32 * (6 / Real.pi) * (3 * a ^ 2 + (2 * Real.pi)⁻¹ ^ 2 *
        (b + 12 * Real.pi * a) ^ 2)) *
      h ^ (κ + 1) * (1 + σ / h) ^ 10 * Real.exp (36 * (σ / h) ^ 2) := by
  have hG := inverseGaussian_compactInverseData F σ hF hcompact hinv hinvD
  obtain ⟨hi0, _, heq, _⟩ := inverse_energy_endpoints (inverseGaussian σ F) hG
  obtain ⟨hiκ, hw⟩ := inverseGaussian_weightedEnergy_le F κ σ h a b
    hF hcompact hκ0 hκ2 hh hσ ha hb hsupport hbound hderiv hinv hinvD
  have hv := shiftedVariance_le (𝓕⁻ (inverseGaussian σ F)) κ σ
    hκ0 hκ2 hσ hi0 hiκ hjoint
  rw [heq] at hv
  have he := inverseGaussian_energy_le F σ h a hF.continuous hh ha hsupport hbound
  have hr : 0 ≤ σ / h := div_nonneg hσ hh.le
  have hq : 1 ≤ 1 + σ / h := by linarith
  have hrκ : (σ / h) ^ κ ≤ (1 + σ / h) ^ (2 : ℕ) := by
    calc
      _ ≤ (1 + σ / h) ^ κ := Real.rpow_le_rpow hr (by linarith) hκ0
      _ ≤ (1 + σ / h) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq hκ2
      _ = _ := Real.rpow_natCast _ 2
  have hσeq : σ = h * (σ / h) := by field_simp
  have hscale : σ ^ κ * h = h ^ (κ + 1) * (σ / h) ^ κ := by
    calc
      _ = (h * (σ / h)) ^ κ * h := by rw [← hσeq]
      _ = h ^ (κ + 1) * (σ / h) ^ κ := by
        rw [Real.mul_rpow hh.le hr, Real.rpow_add hh, Real.rpow_one]
        ring
  have hnoise : σ ^ κ * energy (inverseGaussian σ F) ≤
      (6 / Real.pi) * a ^ 2 * h ^ (κ + 1) * (1 + σ / h) ^ 2 *
        Real.exp (36 * (σ / h) ^ 2) := by
    calc
      _ ≤ σ ^ κ * ((6 / Real.pi) * a ^ 2 * h *
          Real.exp (36 * (σ / h) ^ 2)) :=
        mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hσ κ)
      _ = (6 / Real.pi) * a ^ 2 * h ^ (κ + 1) * (σ / h) ^ κ *
          Real.exp (36 * (σ / h) ^ 2) := by
        calc
          _ = (6 / Real.pi) * a ^ 2 * (σ ^ κ * h) *
              Real.exp (36 * (σ / h) ^ 2) := by ring
          _ = _ := by rw [hscale]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrκ (by positivity)) (Real.exp_pos _).le
  have hq4 : (1 + σ / h) ^ (4 : ℕ) ≤ (1 + σ / h) ^ (10 : ℕ) :=
    pow_le_pow_right₀ hq (by norm_num)
  have hq2 : (1 + σ / h) ^ (2 : ℕ) ≤ (1 + σ / h) ^ (10 : ℕ) :=
    pow_le_pow_right₀ hq (by norm_num)
  have hw10 := hw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hq4
      (show 0 ≤ ((6 / Real.pi) * (a ^ 2 + (2 * Real.pi)⁻¹ ^ 2 *
        (b + 12 * Real.pi * a) ^ 2)) * h ^ (κ + 1) by positivity))
    (Real.exp_pos _).le)
  have hn10 := hnoise.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hq2
      (show 0 ≤ (6 / Real.pi) * a ^ 2 * h ^ (κ + 1) by positivity))
    (Real.exp_pos _).le)
  calc
    _ ≤ 32 * (weightedEnergy κ (𝓕⁻ (inverseGaussian σ F)) +
        2 * (σ ^ κ * energy (inverseGaussian σ F))) := by
      simpa only [mul_assoc] using hv
    _ ≤ 32 * ((((6 / Real.pi) * (a ^ 2 + (2 * Real.pi)⁻¹ ^ 2 *
          (b + 12 * Real.pi * a) ^ 2)) *
          h ^ (κ + 1) * (1 + σ / h) ^ 10 * Real.exp (36 * (σ / h) ^ 2)) +
        2 * ((6 / Real.pi) * a ^ 2 * h ^ (κ + 1) * (1 + σ / h) ^ 10 *
          Real.exp (36 * (σ / h) ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hw10 (mul_le_mul_of_nonneg_left hn10 (by norm_num))) (by norm_num)
    _ = _ := by ring

end Causalean.Stat.Nonparametric
