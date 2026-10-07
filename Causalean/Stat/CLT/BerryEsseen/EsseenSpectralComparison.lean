module
public import Causalean.Stat.CLT.BerryEsseen.EsseenConvolutionDilation
public import Causalean.Stat.CLT.BerryEsseen.EsseenKernelDilation
public import Causalean.Stat.CLT.BerryEsseen.EsseenUnitSpectralComparison

/-! # One-sided spectral comparison with constant 24/π

This module isolates the kernel construction in Esseen's one-sided smoothing
argument. The Fourier estimate for a supplied kernel is proved separately in
`EsseenConvolutionTransfer`.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [an integrable real function H](hyp:hH) whose
[downward increments are bounded by a nonnegative constant L times the
distance](hyp:hL,hdown), [a positive bandwidth T](hyp:hT), any point x, and
[a positive tolerance ε](hyp:hε), [there is a continuous integrable kernel K
with integrable Fourier transform that vanishes outside (−T, T) and has
magnitude at most one, whose convolution with H at x is integrable and
satisfies H(x) ≤ 2·|convolution at x| + 24L/(πT) + ε](goal). -/
theorem exists_esseen_one_sided_spectral_comparator
    (H : ℝ → ℝ) (hH : Integrable H volume)
    (L : ℝ) (hL : 0 ≤ L)
    (hdown : ∀ a b : ℝ, a ≤ b → H a ≤ H b + L * (b - a))
    (T : ℝ) (hT : 0 < T) (x : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ → ℝ,
      Integrable K volume ∧ Continuous K ∧
      Integrable (fun t : ℝ =>
        ∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) volume ∧
      (∀ t : ℝ, T ≤ |t| →
        (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) = 0) ∧
      (∀ t : ℝ,
        ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)‖ ≤ 1) ∧
      Integrable (fun y : ℝ => H (x - y) * K y) volume ∧
      H x ≤ 2 * |∫ y : ℝ, H (x - y) * K y| +
        24 * L / (Real.pi * T) + ε := by
  /- Reduce to `exists_esseen_unit_spectral_comparator` by translation and
  bandwidth scaling. Take a = L/T + ε*π/48 > 0 and
  G(u)=H(x+u/T)/a. Its downward slope is L/(a*T) ≤ 1.
  Apply the unit comparator with tolerance ε/(2*a). Dilate the witness
  using spectral_kernel_dilation_properties and transfer its convolution
  with spectral_convolution_dilation. The total error is
  a*(24/π + ε/(2*a)) = 24*L/(π*T) + ε.
  This covers L=0 without an impossible division by L. -/
  let a : ℝ := L / T + ε * Real.pi / 48
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hLa : L ≤ a * T := by
    dsimp [a]
    have : 0 ≤ ε * Real.pi / 48 * T := by positivity
    rw [add_mul, div_mul_cancel₀ L hT.ne']
    linarith
  let G : ℝ → ℝ := fun u => H (x + u / T) / a
  have hG : Integrable G volume :=
    ((hH.comp_add_left x).comp_div hT.ne').div_const a
  have hGdown : ∀ u v : ℝ, u ≤ v → G u ≤ G v + (v - u) := by
    intro u v huv
    have huv' : x + u / T ≤ x + v / T := by
      exact add_le_add_right ((div_le_div_iff_of_pos_right hT).2 huv) x
    have hd := hdown (x + u / T) (x + v / T) huv'
    have hs : L * ((x + v / T) - (x + u / T)) ≤ a * (v - u) := by
      have hm := mul_le_mul_of_nonneg_right hLa (sub_nonneg.mpr huv)
      apply (le_of_mul_le_mul_right ?_ hT)
      convert hm using 1 <;> field_simp
      ring
    dsimp [G]
    apply (div_le_iff₀ ha).2
    rw [add_mul, div_mul_cancel₀ _ ha.ne']
    linarith
  obtain ⟨K, hKi, hKc, _, hsupp, hnorm, hprod, hpoint⟩ :=
    exists_esseen_unit_spectral_comparator G hG hGdown (ε / (2 * a))
      (by positivity)
  have hprod' : Integrable (fun u : ℝ => H (x - u / T) / a * K u) volume := by
    simpa only [G, neg_div, sub_eq_add_neg] using hprod
  obtain ⟨hdi, hdc, hdf, hds, hdn⟩ :=
    spectral_kernel_dilation_properties K hKi hKc hsupp hnorm T hT
  obtain ⟨hdprod, hdint⟩ := spectral_convolution_dilation H K x a T ha hT hprod'
  refine ⟨fun y => T * K (T * y), hdi, hdc, hdf, hds, hdn, hdprod, ?_⟩
  have hpoint' : H x / a ≤
      2 * |∫ u : ℝ, H (x - u / T) / a * K u| + 24 / Real.pi + ε / (2 * a) := by
    simpa only [G, zero_div, add_zero, neg_div, sub_eq_add_neg] using hpoint
  have hscaled := (mul_le_mul_of_nonneg_left hpoint' ha.le)
  rw [mul_div_cancel₀ _ ha.ne'] at hscaled
  have herr : a * (24 / Real.pi + ε / (2 * a)) =
      24 * L / (Real.pi * T) + ε := by
    dsimp [a]
    field_simp
    ring
  rw [hdint, abs_mul, abs_of_pos ha]
  nlinarith [herr]

end Causalean.Stat.CLT.BerryEsseen
