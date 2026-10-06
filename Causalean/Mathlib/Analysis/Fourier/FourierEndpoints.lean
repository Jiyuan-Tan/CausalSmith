module
public import Causalean.Mathlib.Analysis.Fourier.Basic
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Plancherel and the quadratic inverse-Fourier energy

This module works with ordinary integral transforms, including compact C¹ multipliers
that are not Schwartz functions (the sixth box convolution has only finite smoothness).
The caller may supply absolute integrability of the inverse transforms of G and G'.
These are standard inversion hypotheses, not assumptions of either weighted inequality.

Primary Mathlib sources checked in round 1:
* FourierTransform.lean: `VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip`;
* Inversion.lean: `Continuous.fourier_fourierInv_eq`;
* FourierTransformDeriv.lean: `Real.fourier_deriv`.
Upstream source: https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Analysis/Fourier
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace Causalean.Mathlib.Analysis.Fourier

/-- [Admissible compact inverse-Fourier data for a complex frequency multiplier](hyp:G) consist of [one continuous frequency derivative](hyp:regularity), [compact spectral support](hyp:compactSupport), [an integrable inverse transform](hyp:integrable_inverse), and [an integrable inverse transform of its derivative](hyp:integrable_inverse_deriv). -/
structure CompactInverseData (G : ℝ → ℂ) : Prop where
  regularity : ContDiff ℝ 1 G
  compactSupport : HasCompactSupport G
  integrable_inverse : Integrable (𝓕⁻ G)
  integrable_inverse_deriv : Integrable (𝓕⁻ (deriv G))

/-- [A continuous complex frequency function](hyp:G,hcont) with [an integrable frequency representation](hyp:hG) and [an integrable inverse Fourier transform](hyp:hinv) has [equal finite squared L² energies in frequency and physical space](goal). -/
theorem inverse_plancherel (G : ℝ → ℂ) (hcont : Continuous G)
    (hG : Integrable G) (hinv : Integrable (𝓕⁻ G)) :
    Integrable (fun ξ => ‖G ξ‖ ^ 2) ∧
    Integrable (fun v => ‖𝓕⁻ G v‖ ^ 2) ∧ energy (𝓕⁻ G) = energy G := by
  have hforward : Integrable (𝓕 G) := by
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hinv.comp_neg
  have hinversion := hcont.fourier_fourierInv_eq hG hforward
  have square_integrable (f : ℝ → ℂ) (hf : Integrable f)
      (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) :
      Integrable (fun x => ‖f x‖ ^ 2) := by
    apply (hf.norm.const_mul C).mono' (hf.aestronglyMeasurable.norm.pow 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
  have hsqinv : Integrable (fun x => ‖𝓕⁻ G x‖ ^ 2) :=
    square_integrable _ hinv (∫ x, ‖G x‖) fun x =>
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (-innerₗ ℝ) G x
  have hsqG : Integrable (fun x => ‖G x‖ ^ 2) := by
    apply square_integrable _ hG (∫ x, ‖𝓕⁻ G x‖)
    intro x
    rw [← congrFun hinversion x]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (𝓕⁻ G) x
  refine ⟨hsqG, hsqinv, ?_⟩
  have hflip : -(-innerₗ ℝ).flip = innerₗ ℝ := by
    ext
    simp
  have hsesq := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (innerSL ℂ) Real.continuous_fourierChar
    (show Continuous (fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2) from
      (innerSL ℝ).continuous₂.neg) hG hinv
  rw [hflip] at hsesq
  change (∫ x, inner ℂ (𝓕⁻ G x) (𝓕⁻ G x)) =
    ∫ x, inner ℂ (G x) (𝓕 (𝓕⁻ G) x) at hsesq
  rw [hinversion] at hsesq
  simp only [inner_self_eq_norm_sq_to_K] at hsesq
  exact_mod_cast hsesq

/-- [A complex frequency multiplier](hyp:G) with [an integrable frequency representation](hyp:hG), [a differentiable frequency profile](hyp:hdiff), [an integrable first derivative](hyp:hD), and [a physical-space location](hyp:v) has [the stated inverse-Fourier derivative–multiplication identity](goal). -/
theorem inverse_deriv_eq (G : ℝ → ℂ) (hG : Integrable G)
    (hdiff : Differentiable ℝ G) (hD : Integrable (deriv G)) (v : ℝ) :
    𝓕⁻ (deriv G) v = (-2 * (Real.pi : ℂ) * Complex.I * (v : ℂ)) * 𝓕⁻ G v := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  simpa [smul_eq_mul, mul_neg, neg_mul] using
    congrFun (Real.fourier_deriv hG hdiff hD) (-v)

/-- [A complex frequency multiplier](hyp:G) with [admissible compact inverse-Fourier data](hyp:hG) has [finite ordinary and quadratic physical-space energies with the stated frequency-space identities](goal). -/
theorem inverse_energy_endpoints (G : ℝ → ℂ) (hG : CompactInverseData G) :
    Integrable (fun v => ‖𝓕⁻ G v‖ ^ 2) ∧
    Integrable (fun v => v ^ 2 * ‖𝓕⁻ G v‖ ^ 2) ∧
    energy (𝓕⁻ G) = energy G ∧
    weightedEnergy 2 (𝓕⁻ G) = (2 * Real.pi)⁻¹ ^ 2 * energy (deriv G) := by
  have hc := hG.regularity.continuous
  have hdc := hG.regularity.continuous_deriv (by simp)
  have hi : Integrable G := hc.integrable_of_hasCompactSupport hG.compactSupport
  have hdi : Integrable (deriv G) := hdc.integrable_of_hasCompactSupport hG.compactSupport.deriv
  have hd := hG.regularity.differentiable (by simp)
  obtain ⟨_, hs, he⟩ := inverse_plancherel G hc hi hG.integrable_inverse
  obtain ⟨_, hds, hde⟩ := inverse_plancherel (deriv G) hdc hdi
    hG.integrable_inverse_deriv
  have hpi : (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
  have hmoment (v : ℝ) :
      v ^ 2 * ‖𝓕⁻ G v‖ ^ 2 =
        (2 * Real.pi)⁻¹ ^ 2 * ‖𝓕⁻ (deriv G) v‖ ^ 2 := by
    rw [inverse_deriv_eq G hi hd hdi]
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    rw [mul_pow, mul_pow, mul_pow, sq_abs]
    field_simp
  have hm : Integrable (fun v => v ^ 2 * ‖𝓕⁻ G v‖ ^ 2) := by
    simp_rw [hmoment]
    exact hds.const_mul _
  refine ⟨hs, hm, he, ?_⟩
  rw [weightedEnergy_two]
  simp_rw [hmoment]
  rw [integral_const_mul, ← energy, hde]

end Causalean.Mathlib.Analysis.Fourier
