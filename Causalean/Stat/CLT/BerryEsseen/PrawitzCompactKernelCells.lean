module
public import Causalean.Stat.CLT.BerryEsseen.CosineCubic
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernelBounds

/-! # Polynomial cell enclosures for the Prawitz filter

These deterministic bounds remove cotangent from frequency-cell certificates.
The reflected upper-band and Jordan lower-band estimates are extracted from
PrawitzBudgetHighCompact without changing their statements or proofs. The
quartic lower-band cell enclosure is the remaining analytic leaf; it uses
only the endpoints of a cell, and retains the full positive half-band.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

/-- On [the upper half of the open kernel band](hyp:s,hs,hs1),
[reflection about π gives a polynomial bound for the squared filter norm](goal).
The assigned endpoint value is excluded. -/
theorem prawitz_high_compact_kernel_sq_upper
    (s : ℝ) (hs : 1 / 2 ≤ s) (hs1 : s < 1) :
    ‖prawitzKernel s‖ ^ 2 ≤
      (1 - s) ^ 2 / 4 + Real.pi ^ 2 * (1 - s) ^ 4 / 16 := by
  have hs0 : 0 < s := by linarith
  let y := Real.pi * (1 - s)
  have hy : 0 < y := by dsimp [y]; positivity
  have hyhalf : y ≤ Real.pi / 2 := by dsimp [y]; nlinarith [Real.pi_pos]
  have hypi : y < Real.pi := by linarith [Real.pi_pos]
  have hsin : 0 < Real.sin y := Real.sin_pos_of_mem_Ioo ⟨hy, hypi⟩
  have hcos : 0 ≤ Real.cos y :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hyhalf⟩
  have hmul : y * Real.cos y ≤ Real.sin y := by
    rcases hyhalf.eq_or_lt with he | hlt
    · rw [he, Real.cos_pi_div_two, Real.sin_pi_div_two]
      norm_num
    · have hcpos : 0 < Real.cos y :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
      have htan := Real.le_tan hy.le hlt
      rw [Real.tan_eq_sin_div_cos] at htan
      exact (le_div_iff₀ hcpos).mp htan
  have hcot : 1 / y - y / 2 ≤ Real.cos y / Real.sin y := by
    have hr : Real.cos y / y ≤ Real.cos y / Real.sin y :=
      div_le_div_of_nonneg_left hcos hsin (Real.sin_le hy.le)
    apply le_trans _ hr
    apply (le_div_iff₀ hy).mpr
    have ht := Real.one_sub_sq_div_two_le_cos (x := y)
    field_simp
    nlinarith
  let q := (1 / Real.pi - (1 - s) * Real.cos y / Real.sin y) / 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    apply div_nonneg _ (by norm_num)
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hsin).mpr
    have hp : 0 < Real.pi := Real.pi_pos
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hp).mpr
    dsimp [y] at hmul
    nlinarith
  have hqupper : q ≤ Real.pi * (1 - s) ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_left hcot (show 0 ≤ 1 - s by linarith)
    have he : (1 - s) * (1 / y - y / 2) =
        1 / Real.pi - Real.pi * (1 - s) ^ 2 / 2 := by
      dsimp [y]
      field_simp [sub_ne_zero.mpr hs1.ne', Real.pi_ne_zero]
    rw [he] at h
    dsimp [q]
    simp only [← mul_div_assoc] at h
    nlinarith
  have hne : ¬(s = 0 ∨ 1 < |s|) := by
    simp only [abs_of_pos hs0, not_or, not_lt]
    exact ⟨hs0.ne', hs1.le⟩
  have hre : (prawitzKernel s).re = (1 - s) / 2 := by
    rw [prawitzKernel, if_neg hne]
    simp only [abs_of_pos hs0, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : (prawitzKernel s).im = q := by
    rw [prawitzKernel, if_neg hne]
    dsimp [q, y]
    rw [mul_sub, mul_one, Real.cos_pi_sub, Real.sin_pi_sub]
    simp only [abs_of_pos hs0, Real.sign_of_pos hs0,
      Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re]
    ring
  have hsq := pow_le_pow_left₀ hq0 hqupper 2
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  nlinarith

/-- On [the positive lower half of the kernel band](hyp:s,hs,hsHalf),
[Jordan's inequality and reflection about π/2 give a squared filter bound
without a trigonometric denominator](goal). -/
theorem prawitz_high_compact_kernel_sq_lower
    (s : ℝ) (hs : 0 < s) (hsHalf : s ≤ 1 / 2) :
    ‖prawitzKernel s‖ ^ 2 ≤ (1 - s) ^ 2 / 4 +
      (((1 - s) * Real.pi * (1 / 2 - s) / (2 * s) + 1 / Real.pi) / 2) ^ 2 := by
  have hp : 0 < Real.pi * s := mul_pos Real.pi_pos hs
  have hhalf : Real.pi * s ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * s) :=
    Real.sin_pos_of_mem_Ioo ⟨hp, by nlinarith [Real.pi_pos]⟩
  have hcos : 0 ≤ Real.cos (Real.pi * s) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hhalf⟩
  have hsinLower : 2 * s ≤ Real.sin (Real.pi * s) := by
    have h := Real.mul_le_sin hp.le hhalf
    convert h using 1
    field_simp
  have hcosUpper : Real.cos (Real.pi * s) ≤ Real.pi * (1 / 2 - s) := by
    have h := Real.sin_le (show 0 ≤ Real.pi / 2 - Real.pi * s by linarith)
    rw [Real.sin_pi_div_two_sub] at h
    nlinarith
  have hcot : Real.cos (Real.pi * s) / Real.sin (Real.pi * s) ≤
      Real.pi * (1 / 2 - s) / (2 * s) := by
    calc
      _ ≤ Real.cos (Real.pi * s) / (2 * s) :=
        div_le_div_of_nonneg_left hcos (by positivity) hsinLower
      _ ≤ _ := div_le_div_of_nonneg_right hcosUpper (by positivity)
  let q := ((1 - s) * Real.cos (Real.pi * s) /
    Real.sin (Real.pi * s) + 1 / Real.pi) / 2
  have hq0 : 0 ≤ q := by
    have h1s : 0 ≤ 1 - s := by linarith
    dsimp [q]
    positivity
  have hqUpper : q ≤
      ((1 - s) * Real.pi * (1 / 2 - s) / (2 * s) + 1 / Real.pi) / 2 := by
    have h := mul_le_mul_of_nonneg_left hcot (show 0 ≤ 1 - s by linarith)
    simp only [← mul_div_assoc] at h
    rw [← mul_assoc] at h
    dsimp [q]
    nlinarith
  have hne : ¬(s = 0 ∨ 1 < |s|) := by
    simp only [abs_of_pos hs, not_or, not_lt]
    exact ⟨hs.ne', by linarith⟩
  have hre : (prawitzKernel s).re = (1 - s) / 2 := by
    rw [prawitzKernel, if_neg hne]
    simp only [abs_of_pos hs, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : (prawitzKernel s).im = q := by
    rw [prawitzKernel, if_neg hne]
    simp only [abs_of_pos hs, Real.sign_of_pos hs,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re]
    dsimp [q]
    ring
  have hsq := pow_le_pow_left₀ hq0 hqUpper 2
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  nlinarith

/-- On [a frequency u in a positive cell [a, b] of the lower half-band
b ≤ 1/2](hyp:u,a,b,ha,hat,htb,hb), [the squared Prawitz filter norm at u is
at most an explicit rational polynomial expression in the cell endpoints a, b
and π](goal). -/
theorem prawitzKernel_lower_cell_taylor_sq_bound
    (u a b : ℝ) (ha : 0 < a) (hat : a ≤ u) (htb : u ≤ b) (hb : b ≤ 1 / 2) :
    ‖prawitzKernel u‖ ^ 2 ≤ (1 - a) ^ 2 / 4 +
      (((1 - a) * (1 - (Real.pi * a) ^ 2 / 2 + (Real.pi * b) ^ 4 / 24) /
        (Real.pi * a * (1 - (Real.pi * b) ^ 2 / 6)) + 1 / Real.pi) / 2) ^ 2 := by
  /- Smallest open kernel obligation, independent of all budgets and smoothing.
  Let x=πu. Real.sin_ge_sub_cube and the endpoint inequalities give
    sin(x) ≥ πa * (1-(πb)^2/6) > 0.
  Positivity follows from b≤1/2 and π<4, so no additional cell-size condition
  is needed. cos_le_quadratic_add_quartic gives
    cos(x) ≤ 1-(πa)^2/2+(πb)^4/24.
  On this half-band cos(x)≥0 and 1-u≥0. Bound the nonnegative imaginary
  component by division, bound the real component by (1-a)/2, and compare
  their squares using Complex.sq_norm and Complex.normSq_apply. The existing
  Jordan estimate below can guide component algebra; it is too loose to
  certify the high-frequency allocation. Do not assume a numerical integral
  budget, and do not add imports of any compact-budget headline. -/
  have hu : 0 < u := lt_of_lt_of_le ha hat
  have huHalf : u ≤ 1 / 2 := htb.trans hb
  have haOne : 0 ≤ 1 - a := by linarith
  have huOne : 0 ≤ 1 - u := by linarith
  have hpa : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  have hpu : 0 < Real.pi * u := mul_pos Real.pi_pos hu
  have hpb : 0 ≤ Real.pi * b :=
    mul_nonneg Real.pi_pos.le (hu.le.trans htb)
  have hpau : Real.pi * a ≤ Real.pi * u :=
    mul_le_mul_of_nonneg_left hat Real.pi_pos.le
  have hpub : Real.pi * u ≤ Real.pi * b :=
    mul_le_mul_of_nonneg_left htb Real.pi_pos.le
  have hpbTwo : Real.pi * b < 2 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hpbSq : (Real.pi * b) ^ 2 < 4 := by
    nlinarith
  have hfactor : 0 < 1 - (Real.pi * b) ^ 2 / 6 := by linarith
  let d := Real.pi * a * (1 - (Real.pi * b) ^ 2 / 6)
  have hd : 0 < d := mul_pos hpa hfactor
  have hsqau := pow_le_pow_left₀ hpa.le hpau 2
  have hsqub := pow_le_pow_left₀ hpu.le hpub 2
  have hfourub := pow_le_pow_left₀ hpu.le hpub 4
  have hsinLower : d ≤ Real.sin (Real.pi * u) := by
    have hmul := mul_le_mul_of_nonneg_left
      (show 1 - (Real.pi * b) ^ 2 / 6 ≤
        1 - (Real.pi * u) ^ 2 / 6 by linarith) hpu.le
    have hend := mul_le_mul_of_nonneg_right hpau hfactor.le
    have ht := Real.sin_ge_sub_cube hpu.le
    dsimp [d]
    nlinarith only [hmul, hend, ht]
  have hsin : 0 < Real.sin (Real.pi * u) := hd.trans_le hsinLower
  have hcos : 0 ≤ Real.cos (Real.pi * u) :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  let c := 1 - (Real.pi * a) ^ 2 / 2 + (Real.pi * b) ^ 4 / 24
  have hcosUpper : Real.cos (Real.pi * u) ≤ c := by
    have ht := cos_le_quadratic_add_quartic (Real.pi * u)
    dsimp [c]
    linarith
  have hc : 0 ≤ c := hcos.trans hcosUpper
  have hcot : Real.cos (Real.pi * u) / Real.sin (Real.pi * u) ≤ c / d := by
    calc
      _ ≤ Real.cos (Real.pi * u) / d :=
        div_le_div_of_nonneg_left hcos hd hsinLower
      _ ≤ _ := div_le_div_of_nonneg_right hcosUpper hd.le
  let q := ((1 - u) * Real.cos (Real.pi * u) /
    Real.sin (Real.pi * u) + 1 / Real.pi) / 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqUpper : q ≤ ((1 - a) * c / d + 1 / Real.pi) / 2 := by
    have h := mul_le_mul
      (show 1 - u ≤ 1 - a by linarith) hcot
      (div_nonneg hcos hsin.le) haOne
    dsimp [q]
    simp only [← mul_div_assoc] at h
    linarith
  have hne : ¬(u = 0 ∨ 1 < |u|) := by
    simp only [abs_of_pos hu, not_or, not_lt]
    exact ⟨hu.ne', by linarith⟩
  have hre : (prawitzKernel u).re = (1 - u) / 2 := by
    rw [prawitzKernel, if_neg hne]
    simp only [abs_of_pos hu, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : (prawitzKernel u).im = q := by
    rw [prawitzKernel, if_neg hne]
    simp only [abs_of_pos hu, Real.sign_of_pos hu,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re]
    dsimp [q]
    ring
  have hsqRe := pow_le_pow_left₀ huOne
    (show 1 - u ≤ 1 - a by linarith) 2
  have hsqIm := pow_le_pow_left₀ hq hqUpper 2
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  change (1 - u) / 2 * ((1 - u) / 2) + q * q ≤
    (1 - a) ^ 2 / 4 + (((1 - a) * c / d + 1 / Real.pi) / 2) ^ 2
  nlinarith only [hsqRe, hsqIm]

end Causalean.Stat.CLT.BerryEsseen
