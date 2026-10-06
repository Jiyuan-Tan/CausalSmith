module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-! # Squared-cosecant partial fractions above the real axis

This derivative calculation specializes Mathlib's cotangent partial-fraction
theorem to order one. It is separate from continuity of the reciprocal series
at the real boundary. Together with `ShiftedReciprocalSquareRegularity`, it
provides the real symmetric squared-cosecant identity without a new axiom.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

/-- At [a complex argument z above the real axis](hyp:z,hz),
[the integer reciprocal-square series Σ_{m∈ℤ} 1/(z+m)² multiplied by the
squared sine factor (sin(πz)/π)² equals one](goal). -/
theorem csc_squared_integer_series_upperHalfPlane
    (z : ℂ) (hz : 0 < z.im) :
    (Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) ^ 2 *
      (∑' m : ℤ, 1 / (z + (m : ℂ)) ^ 2) = 1 := by
  /- Lowest independent algebraic leaf. Specialize
  iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow to k=1. Compute the
  derivative of π*cos(πz)/sin(πz) using quotient differentiation and
  Complex.sin_sq_add_cos_sq. Use openness of the upper half-plane to identify
  the within derivative. Its sine is nonzero because z is not a real integer.
  This helper must not use CscSquaredSeries or any real-boundary identity.
  The full real result is downstream, so this restriction does not replace
  or narrow that API. -/
  have hs : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    sin_pi_mul_ne_zero (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd := (((Complex.hasDerivAt_cos ((Real.pi : ℂ) * z)).comp z
    ((hasDerivAt_id z).const_mul (Real.pi : ℂ))).div
    ((Complex.hasDerivAt_sin ((Real.pi : ℂ) * z)).comp z
      ((hasDerivAt_id z).const_mul (Real.pi : ℂ))) hs).const_mul (Real.pi : ℂ)
  have hseries := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow
    (k := 1) (by decide) (z := z) hz
  rw [iteratedDerivWithin_one,
    derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz] at hseries
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one, Nat.reduceAdd] at hseries
  simp only [Function.comp_apply, Pi.div_apply, mul_one] at hd
  simp_rw [Complex.cot_eq_cos_div_sin] at hseries
  rw [hd.deriv] at hseries
  have htrig := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z)
  field_simp [hs, hp] at hseries ⊢
  linear_combination hseries + (Real.pi : ℂ) ^ 2 * htrig

end Causalean.Stat.CLT.BerryEsseen
