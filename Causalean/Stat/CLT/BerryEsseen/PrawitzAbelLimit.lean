module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSignIntegrability
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Abel convergence of the weighted cotangent integral

A nonsingular rational sine kernel converges to cotangent inside the unit
interval. Its multiplier relative to cotangent lies between zero and one,
which supplies an integrable majorant after multiplication by the sine wave.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory Filter Topology

/-- For [any real spatial frequency x](hyp:x), [as the damping ratio r increases
to one, the triangularly weighted integrals over [0, 1] of the rational Abel
kernel 2r·sin(2πt)/(1 − 2r·cos(2πt) + r²) against sin(2πxt) converge to the
weighted integral of the cotangent cot(πt) against sin(2πxt)](goal). -/
theorem prawitz_abel_weighted_integral_tendsto (x : ℝ) :
    Tendsto (fun r : ℝ => ∫ t in (0 : ℝ)..1,
      (1 - t) *
        (2 * r * Real.sin (2 * Real.pi * t) /
          (1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2)) *
        Real.sin (2 * Real.pi * x * t))
      (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (∫ t in (0 : ℝ)..1,
        (1 - t) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t) *
          Real.sin (2 * Real.pi * x * t))) := by
  /- For 0<r<1 and 0<t<1, rewrite the rational factor as cot(πt) times
  4*r*sin(πt)^2 / ((1-r)^2+4*r*sin(πt)^2). This multiplier is in [0,1]
  and tends to one. The absolute weighted cotangent sine integrand is an
  integrable majorant: subtract sin(2πxt)/π from the integrand in
  prawitz_sine_intervalIntegrable (2πx). Endpoint values are irrelevant a.e.
  Use dominated convergence for the restricted interval measure and eventual
  0<r<1; do not presume the undamped cotangent itself is integrable. -/
  let f : ℝ → ℝ := fun t =>
    (1 - t) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t) *
      Real.sin (2 * Real.pi * x * t)
  have hf : IntervalIntegrable f volume 0 1 := by
    have h := (prawitz_sine_intervalIntegrable (2 * Real.pi * x)).sub
      (show IntervalIntegrable (fun t : ℝ => Real.sin (t * (2 * Real.pi * x)) /
        Real.pi) volume 0 1 from
        (show Continuous (fun t : ℝ => Real.sin (t * (2 * Real.pi * x)) / Real.pi)
          by fun_prop).intervalIntegrable 0 1)
    convert h using 1
    funext t
    dsimp [f, prawitzSineWeight]
    rw [show t * (2 * Real.pi * x) = 2 * Real.pi * x * t by ring]
    ring
  have hden (r t : ℝ) :
      1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2 =
        (1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * t) ^ 2 := by
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
      Real.cos_two_mul_eq_one_sub]
    ring
  have hpos (r t : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      0 < 1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2 := by
    rw [hden]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (by linarith)) (by positivity)
  have he : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < r ∧ r < 1 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with r hr hr1
    exact ⟨hr, hr1⟩
  have hid (r t : ℝ) (hr : 0 < r) (hr1 : r < 1)
      (hs : Real.sin (Real.pi * t) ≠ 0) :
      (1 - t) * (2 * r * Real.sin (2 * Real.pi * t) /
        (1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2)) *
        Real.sin (2 * Real.pi * x * t) =
      f t * (4 * r * Real.sin (Real.pi * t) ^ 2 /
        ((1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * t) ^ 2)) := by
    rw [hden, show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.sin_two_mul]
    dsimp [f]
    field_simp
    ring
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖f t‖)
  · exact Filter.Eventually.of_forall fun r =>
      (show Measurable (fun t : ℝ => (1 - t) *
        (2 * r * Real.sin (2 * Real.pi * t) /
          (1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2)) *
        Real.sin (2 * Real.pi * x * t)) by fun_prop).aestronglyMeasurable
  · filter_upwards [he] with r hr
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht htmem
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at htmem
    have hs : Real.sin (Real.pi * t) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, htmem.1])
        (by nlinarith [Real.pi_pos, htmem.2.lt_of_ne ht])).ne'
    rw [hid r t hr.1 hr.2 hs, norm_mul]
    have hd : 0 < (1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * t) ^ 2 := by
      rw [← hden]; exact hpos r t hr.1 hr.2
    have hk : 0 ≤ 4 * r * Real.sin (Real.pi * t) ^ 2 /
        ((1 - r) ^ 2 + 4 * r * Real.sin (Real.pi * t) ^ 2) :=
      div_nonneg (by have := hr.1; positivity) hd.le
    simp only [Real.norm_eq_abs, abs_of_nonneg hk]
    exact mul_le_of_le_one_right (abs_nonneg _) ((div_le_one hd).2 (by nlinarith))
  · exact hf.norm
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht htmem
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at htmem
    have hs : Real.sin (Real.pi * t) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, htmem.1])
        (by nlinarith [Real.pi_pos, htmem.2.lt_of_ne ht])).ne'
    have hd : 1 - 2 * (1 : ℝ) * Real.cos (2 * Real.pi * t) + 1 ^ 2 ≠ 0 := by
      rw [hden]; simpa using mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero 2 hs)
    have hc : ContinuousAt (fun r : ℝ => (1 - t) *
        (2 * r * Real.sin (2 * Real.pi * t) /
          (1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2)) *
        Real.sin (2 * Real.pi * x * t)) 1 := by
      fun_prop (disch := exact hd)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1
    congr 1
    rw [hden, show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.sin_two_mul]
    norm_num only [sub_self, zero_pow, zero_add, mul_one]
    field_simp [hs]
    ring

end Causalean.Stat.CLT.BerryEsseen
