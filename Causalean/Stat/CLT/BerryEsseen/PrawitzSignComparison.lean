module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSignIntegrability
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSignSeries
public import Causalean.Stat.CLT.BerryEsseen.ReciprocalSquareTail

/-! # Pointwise half-line comparison for Prawitz smoothing

The cotangent sine approximation has a squared-sinc error majorant. This
is a deterministic spatial inequality, not an assumed probability bound.
It includes the discontinuity at zero, so later CDF bounds allow atoms.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The [Prawitz sign approximation is zero at zero](goal). -/
theorem prawitzSignApprox_zero : prawitzSignApprox 0 = 0 := by
  simp [prawitzSignApprox]

/-- Reversing [the spatial argument](hyp:y) [reverses the sign of the
Prawitz approximation](goal). -/
theorem prawitzSignApprox_neg (y : ℝ) : prawitzSignApprox (-y) = -prawitzSignApprox y := by
  simp only [prawitzSignApprox, mul_neg, Real.sin_neg,
    intervalIntegral.integral_neg]

/-- At [every real point y](hyp:y), [the sine integrand defining Prawitz's sign
approximation is integrable on [0, 1], and the error between the sign of y
and Prawitz's sign approximation at y is at most sinc(y/2)²](goal). -/
theorem prawitzSignApprox_integrable_and_error (y : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => prawitzSineWeight t * Real.sin (t * y)) volume 0 1 ∧
    |Real.sign y - prawitzSignApprox y| ≤ Real.sinc (y / 2) ^ 2 := by
  /- Round 4 splits endpoint integrability, the integral-to-series bridge,
  and the elementary tail sandwich into three distinct import leaves.
  Use prawitz_sine_intervalIntegrable for the first conjunct. For y>0,
  set x=y/(2π) and use prawitzSignApprox_reciprocal_sq_identity.
  reciprocal_sq_tail_bounds places S between 1/(x+1) and 1/x,
  hence |x^(-2)+2S-2/x|≤x^(-2). Convert sin(πx)/(πx) to sinc.
  For y<0, use prawitzSignApprox_neg and sinc evenness.
  At y=0 the approximation is zero and sinc is one. Thus the upper
  half-line majorant takes value one at zero, while the lower takes zero;
  integrating both bounds remains valid for atomic probability laws.
  Do not replace this spatial inequality by a CDF/CLT assumption. -/
  refine ⟨prawitz_sine_intervalIntegrable y, ?_⟩
  have hpos (z : ℝ) (hz : 0 < z) :
      |1 - prawitzSignApprox z| ≤ Real.sinc (z / 2) ^ 2 := by
    let x := z / (2 * Real.pi)
    have hx : 0 < x := by dsimp [x]; positivity
    have hscale : 2 * Real.pi * x = z := by
      dsimp [x]
      field_simp
    have htail := reciprocal_sq_tail_bounds x hx
    let S := ∑' n : ℕ, 1 / (x + (n : ℝ) + 1) ^ 2
    have hSlo : 1 / (x + 1) ≤ S := htail.2.1
    have hShi : S ≤ 1 / x := htail.2.2
    have hlo : 1 / x - 1 / x ^ 2 ≤ 1 / (x + 1) := by
      apply (le_div_iff₀ (by positivity : 0 < x + 1)).mpr
      field_simp
      nlinarith
    have hbracket : |1 / x ^ 2 + 2 * S - 2 / x| ≤ 1 / x ^ 2 := by
      rw [abs_le]
      simp only [div_eq_mul_inv] at hSlo hShi hlo ⊢
      constructor <;> linarith
    have hsin : Real.sinc (z / 2) =
        Real.sin (Real.pi * x) / (Real.pi * x) := by
      have he : z / 2 = Real.pi * x := by linarith [hscale]
      rw [he, Real.sinc_of_ne_zero (by positivity : Real.pi * x ≠ 0)]
    rw [← hscale, prawitzSignApprox_reciprocal_sq_identity x hx, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (Real.sin (Real.pi * x) / Real.pi) ^ 2 * (1 / x ^ 2) :=
        mul_le_mul_of_nonneg_left hbracket (sq_nonneg _)
      _ = Real.sinc ((2 * Real.pi * x) / 2) ^ 2 := by
        rw [hscale, hsin]
        field_simp
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have h := hpos (-y) (neg_pos.mpr hy)
    rw [Real.sign_of_neg hy, show -1 - prawitzSignApprox y =
      -(1 + prawitzSignApprox y) by ring, abs_neg]
    simpa [prawitzSignApprox_neg, neg_div, Real.sinc_neg] using h
  · subst y
    simp [prawitzSignApprox_zero]
  · simpa [Real.sign_of_pos hy] using hpos y hy

end Causalean.Stat.CLT.BerryEsseen
