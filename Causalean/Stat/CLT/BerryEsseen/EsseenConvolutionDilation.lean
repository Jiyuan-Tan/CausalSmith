module
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Spatial change of variables for spectral comparison

This elementary integral identity transfers a normalized, translated
unit-bandwidth convolution to the original function and bandwidth.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [a positive amplitude a](hyp:ha) and [a positive dilation T](hyp:hT), if
[the translated, amplitude-normalized product u ↦ H(x − u/T)/a · K(u) is
integrable](hyp:hprod), then [the dilated convolution integrand
y ↦ H(x − y)·T·K(Ty) is integrable and its integral is a times the integral
of the normalized product](goal). -/
theorem spectral_convolution_dilation
    (H K : ℝ → ℝ) (x a T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hprod : Integrable (fun u : ℝ => H (x - u / T) / a * K u) volume) :
    Integrable (fun y : ℝ => H (x - y) * (T * K (T * y))) volume ∧
    (∫ y : ℝ, H (x - y) * (T * K (T * y))) =
      a * ∫ u : ℝ, H (x - u / T) / a * K u := by
  /- Put g(u)=H(x-u/T)/a*K(u). The target integrand is
  (a*T)*g(T*y). Use hprod.comp_mul_left' for integrability;
  integral_const_mul and Measure.integral_comp_mul_left give the identity.
  Cancel (T*y)/T and (a*T)*|T⁻¹| using ha and hT. -/
  let g : ℝ → ℝ := fun u => H (x - u / T) / a * K u
  have heq : (fun y : ℝ => H (x - y) * (T * K (T * y))) =
      fun y => (a * T) * g (T * y) := by
    funext y
    dsimp only [g]
    rw [mul_div_cancel_left₀ y hT.ne']
    field_simp
  rw [heq]
  refine ⟨(hprod.comp_mul_left' hT.ne').const_mul (a * T), ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr hT)]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_assoc a T T⁻¹, mul_inv_cancel₀ hT.ne', mul_one]

end Causalean.Stat.CLT.BerryEsseen
