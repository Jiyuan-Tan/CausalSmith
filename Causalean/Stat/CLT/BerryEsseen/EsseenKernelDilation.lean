module
public import Causalean.Stat.CLT.BerryEsseen.EsseenUnitRegularity

/-! # Dilation of one-sided spectral kernels

The change of variables taking a unit-bandwidth kernel to bandwidth T is
isolated here. These lemmas concern arbitrary kernels and do not assume a
CDF bound or a normal approximation.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- Dilating a real kernel by a positive bandwidth and multiplying by that
bandwidth divides the frequency in its Fourier integral by the bandwidth. -/
theorem spectral_kernel_dilation_fourier
    (K : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (t : ℝ) :
    (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
      ((T * K (T * y) : ℝ) : ℂ)) =
    ∫ u : ℝ, Complex.exp ((((t / T) * u : ℝ) : ℂ) * Complex.I) * (K u : ℂ) := by
  /- Rewrite the integrand as T times f(T*y), where
  f(u) = exp(i*(t/T)*u)*K(u). Apply Measure.integral_comp_mul_left
  and integral_const_mul; positivity cancels T*|T⁻¹|.
  This substitution identity is valid even for a nonintegrable K because
  both Bochner integrals then obey the same change-of-variables theorem. -/
  let f : ℝ → ℂ := fun u =>
    Complex.exp ((((t / T) * u : ℝ) : ℂ) * Complex.I) * (K u : ℂ)
  have hscale (y : ℝ) : (t / T) * (T * y) = t * y := by
    field_simp
  have heq : (fun y : ℝ => Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
      ((T * K (T * y) : ℝ) : ℂ)) = fun y => (T : ℂ) * f (T * y) := by
    funext y
    dsimp only [f]
    rw [hscale]
    simp only [Complex.ofReal_mul]
    ring
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr hT)]
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hT.ne', Complex.ofReal_one, one_mul]
  rfl


/-- For [an integrable](hyp:hK) [continuous](hyp:hKcont) kernel K whose
[Fourier transform vanishes outside (−1, 1)](hyp:hsupp) and
[has magnitude at most one](hyp:hnorm), and [a positive dilation T](hyp:hT),
[the dilated kernel y ↦ T·K(Ty) is integrable and continuous, has an
integrable Fourier transform that vanishes outside (−T, T), and keeps Fourier
magnitude at most one](goal). -/
theorem spectral_kernel_dilation_properties
    (K : ℝ → ℝ) (hK : Integrable K volume) (hKcont : Continuous K)
    (hsupp : ∀ t : ℝ, 1 ≤ |t| →
      (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) = 0)
    (hnorm : ∀ t : ℝ,
      ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) :
    Integrable (fun y : ℝ => T * K (T * y)) volume ∧
    Continuous (fun y : ℝ => T * K (T * y)) ∧
    Integrable (fun t : ℝ => ∫ y : ℝ,
      Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
        ((T * K (T * y) : ℝ) : ℂ)) volume ∧
    (∀ t : ℝ, T ≤ |t| →
      (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
        ((T * K (T * y) : ℝ) : ℂ)) = 0) ∧
    (∀ t : ℝ,
      ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
        ((T * K (T * y) : ℝ) : ℂ)‖ ≤ 1) := by
  /- Use spectral_kernel_dilation_fourier for all Fourier clauses.
  integrable_unit_supported_kernel_fourier supplies the original transform's
  integrability; Integrable.comp_div gives its frequency dilation.
  Physical integrability uses hK.comp_mul_left' and const_mul.
  Support follows from |t/T| = |t|/T and the positive-bandwidth inequality. -/
  refine ⟨(hK.comp_mul_left' hT.ne').const_mul T, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · simp_rw [spectral_kernel_dilation_fourier K T hT]
    exact (integrable_unit_supported_kernel_fourier K hK hsupp hnorm).comp_div hT.ne'
  · intro t ht
    rw [spectral_kernel_dilation_fourier K T hT]
    apply hsupp
    rw [abs_div, abs_of_pos hT]
    exact (le_div_iff₀ hT).2 (by simpa using ht)
  · intro t
    rw [spectral_kernel_dilation_fourier K T hT]
    exact hnorm (t / T)

end Causalean.Stat.CLT.BerryEsseen
