module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Endpoint regularity of the Prawitz sine integral

The compact-interval sine integrand has removable endpoint singularities.
This regularity task is independent of the Beurling partial-fraction
identity and the pointwise approximation inequality.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [any real spatial argument y](hyp:y), [the Prawitz sine integrand, the
cotangent weight at t times sin(ty), is integrable on the unit
interval](goal). -/
theorem prawitz_sine_intervalIntegrable (y : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => prawitzSineWeight t * Real.sin (t * y)) volume 0 1 := by
  /- Write sin(ty)=ty*sinc(ty). At zero use sin(πt)=πt*sinc(πt)
  to cancel t; the limit is y/π. At one reflect sin(πt) as
  sin(π(1-t)); the factor (1-t) cancels, and the weight tends to zero.
  Extend continuously with these endpoint values and use equality a.e.
  on (0,1) to obtain interval integrability. The assigned original values
  at the two endpoints need not equal the continuous extension values.
  This leaf does not require any series identity or approximation bound. -/
  have hsin (z : ℝ) : Real.sin z = z * Real.sinc z := by
    by_cases hz : z = 0
    · simp [hz]
    · rw [Real.sinc_of_ne_zero hz, mul_div_cancel₀ _ hz]
  have hne (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
      Real.sinc (Real.pi * t) ≠ 0 := by
    by_cases h : t = 0
    · simp [h]
    · have hp : 0 < Real.pi * t := mul_pos Real.pi_pos (lt_of_le_of_ne ht (Ne.symm h))
      rw [Real.sinc_of_ne_zero hp.ne']
      exact div_ne_zero (Real.sin_pos_of_pos_of_lt_pi hp
        (by nlinarith [Real.pi_pos])).ne' hp.ne'
  let f : ℝ → ℝ := fun t =>
    (1 - t) * Real.cos (Real.pi * t) * y * Real.sinc (t * y) /
      (Real.pi * Real.sinc (Real.pi * t)) + Real.sin (t * y) / Real.pi
  let g : ℝ → ℝ := fun t =>
    Real.cos (Real.pi * t) * Real.sin (t * y) /
      (Real.pi * Real.sinc (Real.pi * (1 - t))) + Real.sin (t * y) / Real.pi
  have hf : ContinuousOn f (Set.uIcc 0 (1 / 2)) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    apply ContinuousOn.add
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro t ht
        exact mul_ne_zero Real.pi_ne_zero (hne t ht.1 ht.2)
    · fun_prop
  have hg : ContinuousOn g (Set.uIcc (1 / 2) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    apply ContinuousOn.add
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro t ht
        exact mul_ne_zero Real.pi_ne_zero (hne (1 - t) (by linarith [ht.2])
          (by linarith [ht.1]))
    · fun_prop
  have hi : IntervalIntegrable (fun t => prawitzSineWeight t * Real.sin (t * y))
      volume 0 (1 / 2) := by
    apply (hf.intervalIntegrable.congr_uIoo ?_)
    intro t ht
    rw [Set.uIoo_of_lt (by norm_num : (0 : ℝ) < 1 / 2)] at ht
    rcases ht with ⟨htl, htr⟩
    have ht0 : t ≠ 0 := ne_of_gt htl
    have hp : Real.pi * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht0
    have hs : Real.sin (Real.pi * t) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
    dsimp [f, prawitzSineWeight]
    rw [Real.sinc_of_ne_zero hp, hsin (t * y)]
    field_simp
  have hj : IntervalIntegrable (fun t => prawitzSineWeight t * Real.sin (t * y))
      volume (1 / 2) 1 := by
    apply (hg.intervalIntegrable.congr_uIoo ?_)
    intro t ht
    rw [Set.uIoo_of_lt (by norm_num : (1 / 2 : ℝ) < 1)] at ht
    rcases ht with ⟨htl, htr⟩
    have hpt : Real.pi * (1 - t) ≠ 0 := mul_ne_zero Real.pi_ne_zero (by linarith)
    have hs : Real.sin (Real.pi * t) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])).ne'
    have hr : Real.sin (Real.pi * (1 - t)) = Real.sin (Real.pi * t) := by
      rw [mul_sub, mul_one, Real.sin_pi_sub]
    dsimp [g, prawitzSineWeight]
    rw [Real.sinc_of_ne_zero hpt, hr]
    field_simp
  exact hi.trans hj

end Causalean.Stat.CLT.BerryEsseen
