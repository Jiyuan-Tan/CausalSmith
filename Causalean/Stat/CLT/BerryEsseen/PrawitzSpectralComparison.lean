module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSpatialFourier
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSpectralIntegrability

/-! # Signed spectral assembly for the Prawitz filter

This module compares the expected spatial sign approximation and squared-sinc
majorant directly to the Gaussian sine integral. Gaussian CDF inversion is
independent: it is used only in the later smoothing assembly. Integrability
of the four comparison terms is proved in the separate imported module.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a probability law with finite first moment](hyp:μ,hfirst),
[positive ordered cutoffs U0 ≤ U](hyp:U0,U,hU0,hcut), and
[any threshold x](hyp:x), [the distance between half the expected Prawitz
sign approximation at U(x − y) and the Gaussian sine integral
(1/π)·∫₀^∞ exp(−t²/2)·sin(tx)/t dt, plus half the expected squared sinc of
U(x − y)/2, is at most the sum of the four Prawitz spectral terms
(2/U)·∫₀^{U0} |K(t/U)|·|φ_μ(t) − φ_γ(t)| dt + (2/U)·∫_{U0}^{U} |K(t/U)|·|φ_μ(t)| dt +
2·∫₀^{U0} |K(t/U)/U − i/(2πt)|·exp(−t²/2) dt + (1/π)·∫_{U0}^{∞} exp(−t²/2)/t dt](goal).
The expectations are over y drawn from the law. Here K is the Prawitz spectral filter, φ_μ the characteristic function of the law, and φ_γ
that of the standard Gaussian. -/
theorem prawitz_gaussian_sine_spectral_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun y : ℝ => y) μ)
    (U0 U : ℝ) (hU0 : 0 < U0) (hcut : U0 ≤ U) (x : ℝ) :
    |(∫ y, prawitzSignApprox (U * (x - y)) ∂μ) / 2 -
      (1 / Real.pi) * (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t)| +
      (∫ y, Real.sinc (U * (x - y) / 2) ^ 2 ∂μ) / 2 ≤
      (2 / U) * (∫ t in (0 : ℝ)..U0,
        ‖prawitzKernel (t / U)‖ *
          ‖charFun μ t - charFun (gaussianReal 0 1) t‖) +
      (2 / U) * (∫ t in U0..U,
        ‖prawitzKernel (t / U)‖ * ‖charFun μ t‖) +
      2 * (∫ t in (0 : ℝ)..U0,
        ‖prawitzKernel (t / U) / (U : ℂ) -
          Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
          Real.exp (-(t ^ 2 / 2))) +
      (1 / Real.pi) * (∫ t in Set.Ioi U0,
        Real.exp (-(t ^ 2 / 2)) / t) := by
  have hU : 0 < U := hU0.trans_le hcut
  -- Both signs use a real component of the same complex comparison.
  have hcomplex (K P z w : ℂ) (hP : P.re = 0) :
      |2 * K.im * z.im - 2 * P.im * w.im| + 2 * K.re * z.re ≤
        2 * ‖K‖ * ‖z - w‖ + 2 * ‖K - P‖ * ‖w‖ := by
    have hb (z w : ℂ) : (K * z - P * w).re ≤
        ‖K‖ * ‖z - w‖ + ‖K - P‖ * ‖w‖ := by
      calc
        _ ≤ |(K * z - P * w).re| := le_abs_self _
        _ ≤ ‖K * z - P * w‖ := Complex.abs_re_le_norm _
        _ = ‖K * (z - w) + (K - P) * w‖ := by congr 1; ring
        _ ≤ ‖K * (z - w)‖ + ‖(K - P) * w‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul, norm_mul]
    have hlo := hb z w
    have hhi := hb (star z) (star w)
    rw [← star_sub, norm_star, norm_star] at hhi
    simp only [Complex.sub_re, Complex.mul_re, hP, zero_mul,
      Complex.star_def, Complex.conj_re, Complex.conj_im] at hlo hhi
    have ha : |2 * K.im * z.im - 2 * P.im * w.im| ≤
        2 * ‖K‖ * ‖z - w‖ + 2 * ‖K - P‖ * ‖w‖ - 2 * K.re * z.re := by
      apply abs_le.mpr
      constructor <;> linarith
    linarith
  let z : ℝ → ℂ := fun t =>
    Complex.exp ((t * x : ℝ) * Complex.I) * charFun μ (-t)
  have hzint (t : ℝ) : z t =
      ∫ y, Complex.exp ((t * (x - y) : ℝ) * Complex.I) ∂μ := by
    dsimp [z]
    rw [charFun_apply_real, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hzi (t : ℝ) : Integrable
      (fun y : ℝ => Complex.exp ((t * (x - y) : ℝ) * Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with y
    exact (Complex.norm_exp_ofReal_mul_I _).le
  have hzre (t : ℝ) : (z t).re = ∫ y, Real.cos (t * (x - y)) ∂μ := by
    rw [hzint]
    simpa only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] using (integral_re (hzi t)).symm
  have hzim (t : ℝ) : (z t).im = ∫ y, Real.sin (t * (x - y)) ∂μ := by
    rw [hzint]
    simpa only [RCLike.im_to_complex, Complex.exp_ofReal_mul_I_im] using (integral_im (hzi t)).symm
  have hzcont : Continuous z := by
    dsimp [z]
    exact (show Continuous (fun t : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) by
      fun_prop).mul ((continuous_charFun (μ := μ)).comp continuous_neg)
  let S : ℝ → ℝ := fun t => prawitzSineWeight (t / U) * (z t).im / U
  let C : ℝ → ℝ := fun t => (1 - t / U) * (z t).re / U
  let G : ℝ → ℝ := fun t =>
    Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t / Real.pi
  have hS : IntervalIntegrable S volume 0 U := by
    have hi := (prawitz_sine_joint_integrable μ hfirst U x).integral_prod_left
    simp only [integral_const_mul] at hi
    have hi' : IntervalIntegrable (fun t : ℝ => prawitzSineWeight t *
        (∫ y, Real.sin (t * (U * (x - y))) ∂μ)) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hi
    have hh := hi'.comp_mul_left (c := U⁻¹)
    simp only [div_inv_eq_mul, one_mul, zero_mul] at hh
    convert hh.div_const U using 1
    funext t
    dsimp [S]
    rw [hzim]
    congr 1
    congr 1
    · rw [div_eq_mul_inv, mul_comm]
    · congr 1
      funext y
      congr 1
      field_simp
  have hC : IntervalIntegrable C volume 0 U := by
    apply Continuous.intervalIntegrable
    dsimp [C]
    exact ((continuous_const.sub (continuous_id.div_const U)).mul
      (Complex.continuous_re.comp hzcont)).div_const U
  have hG : IntegrableOn G (Set.Ioi 0) := by
    have hg : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) := by
      convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
      funext t
      congr 1
      ring
    have hi : IntegrableOn (fun t : ℝ =>
        Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t) (Set.Ioi 0) := by
      apply (hg.integrableOn.const_mul |x|).mono'
        (show Measurable (fun t : ℝ =>
          Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t) by
          fun_prop).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      simp only [Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos ht0]
      have hs : |Real.sin (t * x)| / t ≤ |x| := by
        apply (div_le_iff₀ ht).mpr
        simpa [abs_mul, abs_of_pos ht0, mul_comm] using Real.abs_sin_le_abs (x := t * x)
      calc
        _ = Real.exp (-(t ^ 2 / 2)) * (|Real.sin (t * x)| / t) := by ring
        _ ≤ Real.exp (-(t ^ 2 / 2)) * |x| := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
        _ = _ := by ring
    exact hi.div_const Real.pi
  have hA : (∫ y, prawitzSignApprox (U * (x - y)) ∂μ) / 2 =
      ∫ t in (0 : ℝ)..U, S t := by
    rw [prawitz_sign_expectation_fubini μ hfirst]
    dsimp [S]
    rw [intervalIntegral.integral_div]
    have hh := intervalIntegral.integral_comp_div
      (a := 0) (b := U) (fun t : ℝ => prawitzSineWeight t *
        (∫ y, Real.sin (t * (U * (x - y))) ∂μ)) hU.ne'
    simp only [zero_div, div_self hU.ne', smul_eq_mul] at hh
    have he : (fun t : ℝ => prawitzSineWeight (t / U) * (z t).im) =
        (fun t : ℝ => prawitzSineWeight (t / U) *
          (∫ y, Real.sin (t / U * (U * (x - y))) ∂μ)) := by
      funext t
      rw [hzim]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      congr 1
      field_simp
    rw [he, hh]
    field_simp
    simp only [mul_comm U]
  have hB : (∫ y, Real.sinc (U * (x - y) / 2) ^ 2 ∂μ) / 2 =
      ∫ t in (0 : ℝ)..U, C t := by
    rw [prawitz_sinc_expectation_fubini μ]
    dsimp [C]
    rw [intervalIntegral.integral_div]
    have hh := intervalIntegral.integral_comp_div
      (a := 0) (b := U) (fun t : ℝ => (1 - t) *
        (∫ y, Real.cos (t * (U * (x - y))) ∂μ)) hU.ne'
    simp only [zero_div, div_self hU.ne', smul_eq_mul] at hh
    have he : (fun t : ℝ => (1 - t / U) * (z t).re) =
        (fun t : ℝ => (1 - t / U) *
          (∫ y, Real.cos (t / U * (U * (x - y))) ∂μ)) := by
      funext t
      rw [hzre]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      congr 1
      field_simp
    rw [he, hh]
    field_simp
    simp only [mul_comm U]
  let K : ℝ → ℂ := fun t => prawitzKernel (t / U) / (U : ℂ)
  let P : ℝ → ℂ := fun t => Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)
  let w : ℝ → ℂ := fun t =>
    Complex.exp ((t * x : ℝ) * Complex.I) * (Real.exp (-(t ^ 2 / 2)) : ℂ)
  have hgamma (t : ℝ) : charFun (gaussianReal 0 1) t =
      (Real.exp (-(t ^ 2 / 2)) : ℂ) := by
    rw [charFun_gaussianReal, Complex.ofReal_exp]
    congr 1
    push_cast
    norm_num
  have hz_norm (t : ℝ) : ‖z t‖ = ‖charFun μ t‖ := by
    dsimp [z]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, charFun_neg]
    exact norm_star _
  have hw_norm (t : ℝ) : ‖w t‖ = Real.exp (-(t ^ 2 / 2)) := by
    dsimp [w]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hzw_norm (t : ℝ) : ‖z t - w t‖ =
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖ := by
    have he : z t - w t = Complex.exp ((t * x : ℝ) * Complex.I) *
        star (charFun μ t - charFun (gaussianReal 0 1) t) := by
      simp only [z, w, hgamma, charFun_neg, star_sub, Complex.star_def,
        Complex.conj_ofReal, mul_sub]
    rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_star]
  have hK_norm (t : ℝ) : ‖K t‖ = ‖prawitzKernel (t / U)‖ / U := by
    dsimp [K]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hU]
  -- This component formula includes t = U; no endpoint continuity is used.
  have hcomponents (t : ℝ) (ht : 0 < t) (htU : t ≤ U) :
      S t = 2 * (K t).im * (z t).im ∧
      C t = 2 * (K t).re * (z t).re := by
    have ht' : 0 < t / U := div_pos ht hU
    have hband : |t / U| ≤ 1 := by
      rw [abs_of_pos ht']
      exact (div_le_one hU).mpr htU
    have hk : ¬(t / U = 0 ∨ 1 < |t / U|) :=
      not_or.mpr ⟨ht'.ne', not_lt.mpr hband⟩
    dsimp [S, C, K]
    rw [Complex.div_ofReal_im, Complex.div_ofReal_re, prawitzKernel, if_neg hk]
    simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add, sub_zero,
      abs_of_pos ht', Real.sign_of_pos ht', prawitzSineWeight]
    constructor <;> ring
  have hP_re (t : ℝ) : (P t).re = 0 := by
    dsimp [P]
    rw [Complex.div_ofReal_re, Complex.I_re, zero_div]
  have hG_component (t : ℝ) : G t = 2 * (P t).im * (w t).im := by
    simp only [G, P, w, Complex.div_ofReal_im, Complex.I_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, Complex.exp_ofReal_mul_I_im]
    ring
  let L : ℝ → ℝ := fun t => (2 / U) * (‖prawitzKernel (t / U)‖ *
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖) +
      2 * (‖K t - P t‖ * Real.exp (-(t ^ 2 / 2)))
  let H : ℝ → ℝ := fun t =>
    (2 / U) * (‖prawitzKernel (t / U)‖ * ‖charFun μ t‖)
  have hlow_point (t : ℝ) (ht : 0 < t) (htU : t ≤ U) :
      |S t - G t| + C t ≤ L t := by
    obtain ⟨hs, hc⟩ := hcomponents t ht htU
    rw [hs, hc, hG_component]
    have hb := hcomplex (K t) (P t) (z t) (w t) (hP_re t)
    rw [hzw_norm, hw_norm, hK_norm] at hb
    convert hb using 1
    dsimp [L]
    ring
  have hhigh_point (t : ℝ) (ht : 0 < t) (htU : t ≤ U) :
      |S t| + C t ≤ H t := by
    obtain ⟨hs, hc⟩ := hcomponents t ht htU
    rw [hs, hc]
    have hb := hcomplex (K t) 0 (z t) 0 rfl
    simp only [Complex.zero_im, mul_zero, sub_zero, norm_zero, add_zero] at hb
    rw [hz_norm, hK_norm] at hb
    convert hb using 1
    dsimp [H]
    ring
  obtain ⟨h1, h2, h3, h4⟩ := prawitz_four_terms_integrable μ hfirst U0 U hU0 hcut
  have hL : IntervalIntegrable L volume 0 U0 :=
    (h1.const_mul (2 / U)).add (h3.const_mul 2)
  have hH : IntervalIntegrable H volume U0 U := h2.const_mul (2 / U)
  have hSlo : IntervalIntegrable S volume 0 U0 := hS.mono_set (by
    rw [Set.uIcc_of_le hU0.le, Set.uIcc_of_le hU.le]
    exact Set.Icc_subset_Icc le_rfl hcut)
  have hShi : IntervalIntegrable S volume U0 U := hS.mono_set (by
    rw [Set.uIcc_of_le hcut, Set.uIcc_of_le hU.le]
    exact Set.Icc_subset_Icc hU0.le le_rfl)
  have hClo : IntervalIntegrable C volume 0 U0 := hC.mono_set (by
    rw [Set.uIcc_of_le hU0.le, Set.uIcc_of_le hU.le]
    exact Set.Icc_subset_Icc le_rfl hcut)
  have hChi : IntervalIntegrable C volume U0 U := hC.mono_set (by
    rw [Set.uIcc_of_le hcut, Set.uIcc_of_le hU.le]
    exact Set.Icc_subset_Icc hU0.le le_rfl)
  have hGlo : IntervalIntegrable G volume 0 U0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hU0.le).mpr
      (hG.mono_set Set.Ioc_subset_Ioi_self)
  have hGhi : IntegrableOn G (Set.Ioi U0) :=
    hG.mono_set (Set.Ioi_subset_Ioi hU0.le)
  -- The Ioc restrictions remove the zero-frequency value from the comparisons.
  have hlo : |(∫ t in (0 : ℝ)..U0, S t) - (∫ t in (0 : ℝ)..U0, G t)| +
      (∫ t in (0 : ℝ)..U0, C t) ≤ ∫ t in (0 : ℝ)..U0, L t := by
    have hm : (∫ t in (0 : ℝ)..U0, |S t - G t| + C t) ≤
        ∫ t in (0 : ℝ)..U0, L t := by
      rw [intervalIntegral.integral_of_le hU0.le, intervalIntegral.integral_of_le hU0.le]
      apply integral_mono_ae ((hSlo.sub hGlo).abs.add hClo).1 hL.1
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hlow_point t ht.1 (ht.2.trans hcut)
    rw [intervalIntegral.integral_add (hSlo.sub hGlo).abs hClo] at hm
    have hn := intervalIntegral.norm_integral_le_integral_norm
      (f := fun t => S t - G t) (μ := volume) hU0.le
    rw [intervalIntegral.integral_sub hSlo hGlo] at hn
    simp only [Real.norm_eq_abs] at hn
    linarith
  have hhi : |∫ t in U0..U, S t| + (∫ t in U0..U, C t) ≤
      ∫ t in U0..U, H t := by
    have hm : (∫ t in U0..U, |S t| + C t) ≤ ∫ t in U0..U, H t := by
      rw [intervalIntegral.integral_of_le hcut, intervalIntegral.integral_of_le hcut]
      apply integral_mono_ae (hShi.abs.add hChi).1 hH.1
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hhigh_point t (hU0.trans ht.1) ht.2
    rw [intervalIntegral.integral_add hShi.abs hChi] at hm
    have hn := intervalIntegral.norm_integral_le_integral_norm
      (f := S) (μ := volume) hcut
    simp only [Real.norm_eq_abs] at hn
    linarith
  have htail : |∫ t in Set.Ioi U0, G t| ≤
      (1 / Real.pi) * (∫ t in Set.Ioi U0, Real.exp (-(t ^ 2 / 2)) / t) := by
    have hm : (∫ t in Set.Ioi U0, |G t|) ≤
        ∫ t in Set.Ioi U0, (1 / Real.pi) * (Real.exp (-(t ^ 2 / 2)) / t) := by
      apply integral_mono_ae hGhi.abs (h4.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hU0.trans ht
      dsimp [G]
      simp only [abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos ht0, abs_of_pos Real.pi_pos]
      calc
        _ ≤ Real.exp (-(t ^ 2 / 2)) * 1 / t / Real.pi := by
          gcongr
          exact Real.abs_sin_le_one _
        _ = _ := by ring
    rw [integral_const_mul] at hm
    have hn := norm_integral_le_integral_norm (f := G) (μ := volume.restrict (Set.Ioi U0))
    simp only [Real.norm_eq_abs] at hn
    exact hn.trans hm
  rw [hA, hB]
  have hGtotal : (1 / Real.pi) * (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t) =
      (∫ t in (0 : ℝ)..U0, G t) + (∫ t in Set.Ioi U0, G t) := by
    rw [intervalIntegral.integral_interval_add_Ioi hG hGhi]
    dsimp [G]
    rw [integral_div]
    ring
  rw [hGtotal, ← intervalIntegral.integral_add_adjacent_intervals hSlo hShi,
    ← intervalIntegral.integral_add_adjacent_intervals hClo hChi]
  have htri : |((∫ t in (0 : ℝ)..U0, S t) + (∫ t in U0..U, S t)) -
      ((∫ t in (0 : ℝ)..U0, G t) + (∫ t in Set.Ioi U0, G t))| ≤
      |(∫ t in (0 : ℝ)..U0, S t) - (∫ t in (0 : ℝ)..U0, G t)| +
        |∫ t in U0..U, S t| + |∫ t in Set.Ioi U0, G t| := by
    calc
      _ = |((∫ t in (0 : ℝ)..U0, S t) - (∫ t in (0 : ℝ)..U0, G t)) +
          (∫ t in U0..U, S t) - (∫ t in Set.Ioi U0, G t)| := by congr 1; ring
      _ ≤ |((∫ t in (0 : ℝ)..U0, S t) - (∫ t in (0 : ℝ)..U0, G t)) +
          (∫ t in U0..U, S t)| + |∫ t in Set.Ioi U0, G t| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
          (((∫ t in (0 : ℝ)..U0, S t) - (∫ t in (0 : ℝ)..U0, G t)) +
            (∫ t in U0..U, S t)) 0 (∫ t in Set.Ioi U0, G t)
      _ ≤ _ := by
        linarith [abs_add_le ((∫ t in (0 : ℝ)..U0, S t) -
          (∫ t in (0 : ℝ)..U0, G t)) (∫ t in U0..U, S t)]
  have hLval : (∫ t in (0 : ℝ)..U0, L t) =
      (2 / U) * (∫ t in (0 : ℝ)..U0,
        ‖prawitzKernel (t / U)‖ * ‖charFun μ t - charFun (gaussianReal 0 1) t‖) +
      2 * (∫ t in (0 : ℝ)..U0,
        ‖prawitzKernel (t / U) / (U : ℂ) - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
        Real.exp (-(t ^ 2 / 2))) := by
    dsimp [L, K, P]
    rw [intervalIntegral.integral_add (h1.const_mul _) (h3.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hHval : (∫ t in U0..U, H t) =
      (2 / U) * (∫ t in U0..U, ‖prawitzKernel (t / U)‖ * ‖charFun μ t‖) := by
    dsimp [H]
    rw [intervalIntegral.integral_const_mul]
  rw [hLval] at hlo
  rw [hHval] at hhi
  linarith

end Causalean.Stat.CLT.BerryEsseen
