module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernel
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Bounds on Prawitz's principal spectral correction

The difference from the singular Fourier transform of a half-line is
uniformly bounded. Its bound supplies an integrable Gaussian smoothing
penalty, with much smaller constants than baseline Esseen smoothing.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

/-- The tangent bound also controls cotangent throughout the positive half-period. -/
private theorem mul_cos_le_sin (x : ℝ) (hx : 0 < x) (hxpi : x < Real.pi) :
    x * Real.cos x ≤ Real.sin x := by
  by_cases hh : x < Real.pi / 2
  · have hc := Real.cos_pos_of_mem_Ioo (show x ∈ Set.Ioo (-(Real.pi / 2))
        (Real.pi / 2) from ⟨by linarith [Real.pi_pos], hh⟩)
    have h := Real.le_tan hx.le hh
    rw [Real.tan_eq_sin_div_cos] at h
    exact (le_div_iff₀ hc).mp h
  · have hc := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hh)
        (show x ≤ Real.pi + Real.pi / 2 by linarith [Real.pi_pos])
    exact (mul_nonpos_of_nonneg_of_nonpos hx.le hc).trans
      (Real.sin_pos_of_mem_Ioo ⟨hx, hxpi⟩).le

/-- Squared real and imaginary corrections on the positive unit band. -/
private theorem correction_sq_le (t : ℝ) (ht : 0 < t) (hband : t ≤ 1) :
    (1 - t) ^ 2 +
      ((1 - t) * (1 / (Real.pi * t) -
        Real.cos (Real.pi * t) / Real.sin (Real.pi * t))) ^ 2 ≤ 1 := by
  by_cases he : t = 1
  · subst t
    norm_num
  have ht1 : t < 1 := lt_of_le_of_ne hband he
  have hx : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hxpi : Real.pi * t < Real.pi := by nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi * t) := Real.sin_pos_of_mem_Ioo ⟨hx, hxpi⟩
  have hcot : Real.cos (Real.pi * t) / Real.sin (Real.pi * t) ≤
      1 / (Real.pi * t) := by
    apply (div_le_div_iff₀ hs hx).mpr
    simpa [mul_comm] using mul_cos_le_sin (Real.pi * t) hx hxpi
  let q := (1 - t) * (1 / (Real.pi * t) -
    Real.cos (Real.pi * t) / Real.sin (Real.pi * t))
  have hq : 0 ≤ q := mul_nonneg (by linarith) (sub_nonneg.mpr hcot)
  change (1 - t) ^ 2 + q ^ 2 ≤ 1
  -- Below the midpoint, the cosine Taylor bound gives q ≤ 2t(1-t).
  by_cases hh : t ≤ 1 / 2
  · have hc : 0 ≤ Real.cos (Real.pi * t) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have hsin := Real.sin_le hx.le
    have hTaylor : 1 - (Real.pi * t) ^ 2 / 2 ≤ Real.cos (Real.pi * t) :=
      Real.one_sub_sq_div_two_le_cos
    have hlo : 1 / (Real.pi * t) - Real.pi * t / 2 ≤
        Real.cos (Real.pi * t) / Real.sin (Real.pi * t) := by
      have hratio : Real.cos (Real.pi * t) / (Real.pi * t) ≤
          Real.cos (Real.pi * t) / Real.sin (Real.pi * t) :=
        div_le_div_of_nonneg_left hc hs hsin
      have hbase : 1 / (Real.pi * t) - Real.pi * t / 2 ≤
          Real.cos (Real.pi * t) / (Real.pi * t) := by
        apply (le_div_iff₀ hx).mpr
        field_simp
        nlinarith
      exact hbase.trans hratio
    have hqbound : q ≤ 2 * t * (1 - t) := by
      have h := mul_le_mul_of_nonneg_left (show
          1 / (Real.pi * t) - Real.cos (Real.pi * t) / Real.sin (Real.pi * t) ≤
            Real.pi * t / 2 by linarith) (show 0 ≤ 1 - t by linarith)
      have hp := Real.pi_le_four
      have hprod : 0 ≤ t * (1 - t) := by positivity
      dsimp [q]
      nlinarith
    have hsquare : q ^ 2 ≤ (2 * t * (1 - t)) ^ 2 :=
      pow_le_pow_left₀ hq hqbound 2
    have hunit : 4 * t * (1 - t) ≤ 1 := by nlinarith [sq_nonneg (2 * t - 1)]
    have hprod := mul_nonneg (show 0 ≤ t * (1 - t) by positivity)
      (show 0 ≤ 1 - 4 * t * (1 - t) by linarith)
    nlinarith
  -- Above the midpoint, reflect the cotangent bound about π.
  · have hy : 0 < Real.pi * (1 - t) := by positivity
    have hypi : Real.pi * (1 - t) < Real.pi := by nlinarith [Real.pi_pos]
    have hr := mul_cos_le_sin (Real.pi * (1 - t)) hy hypi
    rw [mul_sub, mul_one, Real.cos_pi_sub, Real.sin_pi_sub] at hr
    have hlo : -(1 / (Real.pi * (1 - t))) ≤
        Real.cos (Real.pi * t) / Real.sin (Real.pi * t) := by
      apply (le_div_iff₀ hs).mpr
      have hc : -Real.sin (Real.pi * t) / (Real.pi * (1 - t)) ≤
          Real.cos (Real.pi * t) := (div_le_iff₀ hy).mpr (by nlinarith)
      calc
        _ = -Real.sin (Real.pi * t) / (Real.pi * (1 - t)) := by ring
        _ ≤ Real.cos (Real.pi * t) := hc
    have hqbound : q ≤ 1 / (Real.pi * t) := by
      have h := mul_le_mul_of_nonneg_left (show
          1 / (Real.pi * t) - Real.cos (Real.pi * t) / Real.sin (Real.pi * t) ≤
            1 / (Real.pi * t) + 1 / (Real.pi * (1 - t)) by linarith)
          (show 0 ≤ 1 - t by linarith)
      have heq : (1 - t) * (1 / (Real.pi * t) + 1 / (Real.pi * (1 - t))) =
          1 / (Real.pi * t) := by field_simp; ring
      simpa only [q, heq] using h
    have hden : (3 : ℝ) / 2 ≤ Real.pi * t := by nlinarith [Real.pi_gt_three]
    have hqb : q ≤ 2 / 3 := hqbound.trans ((div_le_iff₀ hx).mpr (by linarith))
    have hsq := pow_le_pow_left₀ hq hqb 2
    have htri : (1 - t) ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith

/-- At each nonzero frequency in the unit band, Prawitz's spectral filter
differs from the half-line principal term by at most one half. -/
theorem prawitzKernel_principal_correction_norm_le
    (t : ℝ) (ht : 0 < |t|) (hband : |t| ≤ 1) :
    ‖prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ ≤ 1 / 2 := by
  have hpos (u : ℝ) (hu : 0 < u) (hub : u ≤ 1) :
      ‖prawitzKernel u - Complex.I / ((2 * Real.pi * u : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    have hne : ¬(u = 0 ∨ 1 < |u|) := by
      simp only [abs_of_pos hu, not_or, not_lt]
      exact ⟨hu.ne', hub⟩
    let z := prawitzKernel u - Complex.I / ((2 * Real.pi * u : ℝ) : ℂ)
    have hre : z.re = (1 - u) / 2 := by
      dsimp only [z]
      rw [prawitzKernel, if_neg hne]
      simp only [abs_of_pos hu,
        Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofReal_re]
      ring
    have him : z.im = -((1 - u) * (1 / (Real.pi * u) -
        Real.cos (Real.pi * u) / Real.sin (Real.pi * u))) / 2 := by
      dsimp only [z]
      rw [prawitzKernel, if_neg hne]
      simp only [abs_of_pos hu, Real.sign_of_pos hu,
        Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofReal_im]
      simp only [zero_add, zero_mul, add_zero, mul_one]
      field_simp
      ring
    have hsq := correction_sq_le u hu hub
    have hnorm : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
      nlinarith
    dsimp [z] at hnorm
    nlinarith [norm_nonneg (prawitzKernel u - Complex.I / ((2 * Real.pi * u : ℝ) : ℂ))]
  rcases lt_or_gt_of_ne (show t ≠ 0 from by simpa using ne_of_gt ht) with hneg | hpositive
  · have hu : 0 < -t := neg_pos.mpr hneg
    have heq : prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ) =
        star (prawitzKernel (-t) - Complex.I / ((2 * Real.pi * (-t) : ℝ) : ℂ)) := by
      have hne : ¬(t = 0 ∨ 1 < |t|) :=
        not_or.mpr ⟨hneg.ne, not_lt.mpr hband⟩
      have hne' : ¬(-t = 0 ∨ 1 < |-t|) := by simpa using hne
      rw [prawitzKernel, if_neg hne, prawitzKernel, if_neg hne']
      apply Complex.ext <;>
        simp only [Real.sign_of_neg hneg,
          Real.sign_of_pos hu, abs_neg, Real.sin_neg, Real.cos_neg, mul_neg,
          Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
          Complex.star_def, Complex.conj_re, Complex.conj_im]
      <;> ring
    rw [heq, norm_star]
    exact hpos (-t) hu (by simpa [abs_of_neg hneg] using hband)
  · exact hpos t hpositive (by simpa [abs_of_pos hpositive] using hband)

/-- At [a nonzero](hyp:ht) frequency t [in the unit band |t| ≤ 1](hyp:hband),
[Prawitz's filter magnitude is at most the reciprocal principal frequency
term 1/(2π|t|) plus one half](goal). -/
theorem prawitzKernel_norm_le
    (t : ℝ) (ht : 0 < |t|) (hband : |t| ≤ 1) :
    ‖prawitzKernel t‖ ≤ 1 / (2 * Real.pi * |t|) + 1 / 2 := by
  have hprincipal :
      ‖Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ =
        1 / (2 * Real.pi * |t|) := by
    simp [abs_of_pos Real.pi_pos]
  have htriangle : ‖prawitzKernel t‖ ≤
      ‖prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ +
        ‖Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ))
        (Complex.I / ((2 * Real.pi * t : ℝ) : ℂ))
  rw [hprincipal] at htriangle
  linarith [prawitzKernel_principal_correction_norm_le t ht hband]

end Causalean.Stat.CLT.BerryEsseen
