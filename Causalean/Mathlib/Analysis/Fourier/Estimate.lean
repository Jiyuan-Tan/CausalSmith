module
public import Causalean.Mathlib.Analysis.Fourier.FourierEndpoints
public import Causalean.Mathlib.Analysis.Fourier.Interpolation

/-!
# Quantitative weighted inverse-Fourier estimates

The main theorem gives the geometric interpolation bound directly in terms of the
frequency-space squared L² norms of G and G', with the normalization constant visible.
The scale-dependent variant is useful for bandwidth families. Compactness and C¹
regularity, together with standard absolute-integrability inversion hypotheses, suffice.
-/

public section

open MeasureTheory
open scoped FourierTransform
namespace Causalean.Mathlib.Analysis.Fourier

/-- For [a complex frequency multiplier G](hyp:G) with [admissible compact inverse-Fourier data](hyp:hG) and [a moment exponent κ between zero and two](hyp:κ,hκ0,hκ2), [the function |v|^κ·|g(v)|², with g the inverse Fourier transform of G, is integrable, and its integral is at most E₀^(1 − κ/2)·((2π)⁻²·E₁)^(κ/2), where E₀ is the integral of |G|² and E₁ the integral of |G′|²](goal). -/
theorem inverse_weightedEnergy_le (G : ℝ → ℂ) (hG : CompactInverseData G)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) :
    Integrable (fun v => |v| ^ κ * ‖𝓕⁻ G v‖ ^ 2) ∧
    weightedEnergy κ (𝓕⁻ G) ≤
      (energy G) ^ (1 - κ / 2) *
        ((2 * Real.pi)⁻¹ ^ 2 * energy (deriv G)) ^ (κ / 2) := by
  obtain ⟨h0, h2, e0, e2⟩ := inverse_energy_endpoints G hG
  refine ⟨integrable_weightedEnergy (𝓕⁻ G) κ
    hG.integrable_inverse.aestronglyMeasurable hκ0 hκ2 h0 h2, ?_⟩
  simpa only [e0, e2] using weightedEnergy_le_interpolation (𝓕⁻ G) κ
    hκ0 hκ2 h0 h2

/-- [A complex frequency multiplier](hyp:G) with [admissible compact inverse-Fourier data](hyp:hG), [a moment exponent in the interval from zero to two](hyp:κ,hκ0,hκ2), and [a positive reference scale](hyp:h,hh) satisfy [the scale-dependent additive inverse-Fourier weighted-energy bound](goal). -/
theorem inverse_weightedEnergy_le_scaled (G : ℝ → ℂ) (hG : CompactInverseData G)
    (κ h : ℝ) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) (hh : 0 < h) :
    weightedEnergy κ (𝓕⁻ G) ≤
      h ^ κ * energy G + h ^ (κ - 2) * (2 * Real.pi)⁻¹ ^ 2 * energy (deriv G) := by
  obtain ⟨h0, h2, e0, e2⟩ := inverse_energy_endpoints G hG
  simpa only [e0, e2, mul_assoc] using weightedEnergy_le_scaled (𝓕⁻ G) κ h
    hG.integrable_inverse.aestronglyMeasurable hκ0 hκ2 hh h0 h2

end Causalean.Mathlib.Analysis.Fourier
