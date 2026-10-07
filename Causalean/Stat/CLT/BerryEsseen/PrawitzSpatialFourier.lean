module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenSmoothing
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernelBounds
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSignComparison

/-! # Spatial and Fourier ingredients for Prawitz smoothing

These atomic half-line sandwiches, integrability results, Fubini identities,
and CDF reduction are proved independently of Gaussian sine inversion and
the signed spectral comparison, which are proved in separate modules.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- The [Prawitz sign approximation is measurable](goal), including its
assigned endpoint values. -/
@[fun_prop]
theorem measurable_prawitzSignApprox : Measurable prawitzSignApprox := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      prawitzSineWeight p.2 * Real.sin (p.2 * p.1)) := by
    unfold prawitzSineWeight
    fun_prop
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
  unfold prawitzSignApprox
  simpa only [intervalIntegral.integral_of_le (by norm_num :
    (0 : ℝ) ≤ 1)] using hi.measurable.const_mul 2

/-- At [every spatial argument](hyp:y), the [sign approximation has absolute
value at most two](goal). -/
theorem prawitzSignApprox_abs_le_two (y : ℝ) : |prawitzSignApprox y| ≤ 2 := by
  have he := (prawitzSignApprox_integrable_and_error y).2
  have hs : Real.sinc (y / 2) ^ 2 ≤ 1 := by
    have h := Real.abs_sinc_le_one (y / 2)
    nlinarith [le_abs_self (Real.sinc (y / 2)), neg_abs_le (Real.sinc (y / 2))]
  have hsign : |Real.sign y| ≤ 1 := by
    rcases lt_trichotomy y 0 with h | h | h
    · simp [Real.sign_of_neg h]
    · simp [h]
    · simp [Real.sign_of_pos h]
  have ht := abs_sub_le (prawitzSignApprox y) (Real.sign y) 0
  rw [sub_zero, sub_zero, abs_sub_comm (prawitzSignApprox y)] at ht
  linarith

/-- At [positive bandwidth](hyp:U,hU), the [closed-half-line indicator at
the threshold and spatial point](hyp:x,y) lies between the two Prawitz
majorants, [with the endpoint included in the upper bound](goal). -/
theorem prawitz_halfLine_indicator_bounds (U : ℝ) (hU : 0 < U) (x y : ℝ) :
    (1 + prawitzSignApprox (U * (x - y)) - Real.sinc (U * (x - y) / 2) ^ 2) / 2 ≤
      (Set.Iic x).indicator (fun _ : ℝ => (1 : ℝ)) y ∧
    (Set.Iic x).indicator (fun _ : ℝ => (1 : ℝ)) y ≤
      (1 + prawitzSignApprox (U * (x - y)) + Real.sinc (U * (x - y) / 2) ^ 2) / 2 := by
  have he := (abs_le.mp (prawitzSignApprox_integrable_and_error (U * (x - y))).2)
  rcases lt_trichotomy y x with h | h | h
  · have hz : 0 < U * (x - y) := mul_pos hU (sub_pos.mpr h)
    rw [Real.sign_of_pos hz] at he
    simp only [Set.indicator_of_mem (show y ∈ Set.Iic x from h.le)]
    constructor <;> linarith [he.1, he.2]
  · subst y
    simp [prawitzSignApprox_zero]
  · have hz : U * (x - y) < 0 := mul_neg_of_pos_of_neg hU (sub_neg.mpr h)
    rw [Real.sign_of_neg hz] at he
    simp only [Set.indicator_of_notMem (show y ∉ Set.Iic x from not_le.mpr h)]
    constructor <;> linarith [he.1, he.2]

/-- For [any probability law](hyp:μ) at [any bandwidth and threshold](hyp:U,x),
both spatial factors are [integrable](goal).
No moment or absence-of-atoms hypothesis is needed for this step. -/
theorem prawitz_spatial_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U x : ℝ) :
    Integrable (fun y : ℝ => prawitzSignApprox (U * (x - y))) μ ∧
    Integrable (fun y : ℝ => Real.sinc (U * (x - y) / 2) ^ 2) μ := by
  constructor
  · apply Integrable.of_bound
      (measurable_prawitzSignApprox.comp (by fun_prop)).aestronglyMeasurable 2
    filter_upwards with y
    exact prawitzSignApprox_abs_le_two _
  · apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with y
    have h := Real.abs_sinc_le_one (U * (x - y) / 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [le_abs_self (Real.sinc (U * (x - y) / 2)),
      neg_abs_le (Real.sinc (U * (x - y) / 2))]

/-- Integrating the spatial majorants for [a probability law](hyp:μ), at
[positive bandwidth](hyp:U,hU) and [any threshold](hyp:x), gives [a CDF
sandwich valid even when the law has an atom at the threshold](goal). -/
theorem prawitz_cdf_spatial_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U : ℝ) (hU : 0 < U) (x : ℝ) :
    (1 + (∫ y, prawitzSignApprox (U * (x - y)) ∂μ) -
      (∫ y, Real.sinc (U * (x - y) / 2) ^ 2 ∂μ)) / 2 ≤ (μ (Set.Iic x)).toReal ∧
    (μ (Set.Iic x)).toReal ≤
      (1 + (∫ y, prawitzSignApprox (U * (x - y)) ∂μ) +
        (∫ y, Real.sinc (U * (x - y) / 2) ^ 2 ∂μ)) / 2 := by
  obtain ⟨hA, hB⟩ := prawitz_spatial_integrable μ U x
  have hc : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hi := hc.indicator (measurableSet_Iic (a := x))
  have hlo := integral_mono ((hc.add hA).sub hB |>.div_const 2) hi
    (fun y => (prawitz_halfLine_indicator_bounds U hU x y).1)
  have hhi := integral_mono hi ((hc.add hA).add hB |>.div_const 2)
    (fun y => (prawitz_halfLine_indicator_bounds U hU x y).2)
  simp only [integral_div, integral_add' hc hA, integral_sub' (hc.add hA) hB,
    integral_add' (hc.add hA) hB, integral_const, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, integral_indicator_const (1 : ℝ) measurableSet_Iic, mul_one,
    Measure.real] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- On [the positive unit band](hyp:t,ht,hband), the [sine-weight singularity
is at most reciprocal-linear](goal). -/
theorem prawitzSineWeight_abs_le (t : ℝ) (ht : 0 < t) (hband : t ≤ 1) :
    |prawitzSineWeight t| ≤ 1 / (Real.pi * t) + 1 := by
  have him : (prawitzKernel t).im = prawitzSineWeight t / 2 := by
    rw [prawitzKernel, if_neg (show ¬(t = 0 ∨ 1 < |t|) from
      not_or.mpr ⟨ht.ne', by simpa [abs_of_pos ht] using not_lt.mpr hband⟩)]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_one,
      zero_add, add_zero, prawitzSineWeight, abs_of_pos ht, Real.sign_of_pos ht]
  have hn := prawitzKernel_norm_le t (by simpa [abs_of_pos ht])
    (by simpa [abs_of_pos ht] using hband)
  have hi := Complex.abs_im_le_norm (prawitzKernel t)
  rw [him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hi
  rw [abs_of_pos ht] at hn
  have he : 2 * (1 / (2 * Real.pi * t) + 1 / 2) = 1 / (Real.pi * t) + 1 := by
    field_simp
  linarith

/-- Multiplying by the sine wave cancels the zero-frequency singularity:
on [the positive unit band](hyp:t,ht,hband), the [integrand at spatial
argument](hyp:z) is [bounded linearly in that argument](goal). -/
theorem prawitz_sine_abs_le (t z : ℝ) (ht : 0 < t) (hband : t ≤ 1) :
    |prawitzSineWeight t * Real.sin (t * z)| ≤ (1 / Real.pi + 1) * |z| := by
  have hsin : |Real.sin (t * z)| ≤ t * |z| := by
    simpa [abs_mul, abs_of_pos ht] using (Real.abs_sin_le_abs (x := t * z))
  have hcoef : (1 / (Real.pi * t) + 1) * t = 1 / Real.pi + t := by
    field_simp
  calc
    _ = |prawitzSineWeight t| * |Real.sin (t * z)| := abs_mul _ _
    _ ≤ (1 / (Real.pi * t) + 1) * (t * |z|) :=
      mul_le_mul (prawitzSineWeight_abs_le t ht hband) hsin
        (abs_nonneg _) (by positivity)
    _ = (1 / Real.pi + t) * |z| := by rw [← mul_assoc, hcoef]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

/-- With [a finite first moment](hyp:μ,hfirst), the [Prawitz sine integrand
at any bandwidth and threshold](hyp:U,x) is [jointly integrable](goal).
This is the cancellation needed for the singular-filter Fubini step. -/
theorem prawitz_sine_joint_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun y : ℝ => y) μ) (U x : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      prawitzSineWeight p.1 * Real.sin (p.1 * (U * (x - p.2))))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ) := by
  have hmajor : Integrable (fun y : ℝ => (1 / Real.pi + 1) * |U * (x - y)|) μ :=
    (((integrable_const x).sub hfirst).const_mul U).norm.const_mul _
  have hprod := hmajor.comp_snd (volume.restrict (Set.Ioc (0 : ℝ) 1))
  apply hprod.mono' (by unfold prawitzSineWeight; fun_prop)
  have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ),
      p.1 ∈ Set.Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Filter.Eventually.of_forall (fun _ => ht)
  filter_upwards [hmem] with p hp
  exact prawitz_sine_abs_le p.1 (U * (x - p.2)) hp.1 hp.2

/-- For [a probability law with finite first moment](hyp:μ,hfirst),
the [expected sign approximation at any bandwidth and threshold](hyp:U,x)
equals [the frequency-first sine integral](goal). -/
theorem prawitz_sign_expectation_fubini (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun y : ℝ => y) μ) (U x : ℝ) :
    (∫ y, prawitzSignApprox (U * (x - y)) ∂μ) =
      2 * ∫ t in (0 : ℝ)..1, prawitzSineWeight t *
        (∫ y, Real.sin (t * (U * (x - y))) ∂μ) := by
  have hi := prawitz_sine_joint_integrable μ hfirst U x
  rw [← Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  have hswap := intervalIntegral_integral_swap
    (f := fun t y => prawitzSineWeight t * Real.sin (t * (U * (x - y)))) hi
  simp only [prawitzSignApprox, integral_const_mul]
  rw [← hswap]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact integral_const_mul _ _

/-- For [any probability law](hyp:μ), the [expected squared-sinc majorant
at any bandwidth and threshold](hyp:U,x) equals [the triangular cosine
integral](goal). -/
theorem prawitz_sinc_expectation_fubini (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U x : ℝ) :
    (∫ y, Real.sinc (U * (x - y) / 2) ^ 2 ∂μ) =
      2 * ∫ t in (0 : ℝ)..1, (1 - t) *
        (∫ y, Real.cos (t * (U * (x - y))) ∂μ) := by
  have hpoint (y : ℝ) : Real.sinc (U * (x - y) / 2) ^ 2 =
      2 * ∫ t in (0 : ℝ)..1, (1 - t) * Real.cos (t * (U * (x - y))) := by
    have h := triangular_cosine_integral (U * (x - y) / (2 * Real.pi))
    have he : 2 * Real.pi * (U * (x - y) / (2 * Real.pi)) = U * (x - y) := by
      field_simp
    have he' : Real.pi * (U * (x - y) / (2 * Real.pi)) = U * (x - y) / 2 := by
      field_simp
    rw [he, he'] at h
    simp only [mul_comm (U * (x - y))] at h
    linarith
  have hi : Integrable (fun p : ℝ × ℝ =>
      (1 - p.1) * Real.cos (p.1 * (U * (x - p.2))))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ),
        p.1 ∈ Set.Ioc (0 : ℝ) 1 := by
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_Ioc.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Filter.Eventually.of_forall (fun _ => ht)
    filter_upwards [hmem] with p hp
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hp.2] : 0 ≤ 1 - p.1)]
    calc
      _ ≤ (1 - p.1) * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (by linarith [hp.2])
      _ ≤ 1 := by linarith [hp.1]
  rw [← Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
  have hswap := intervalIntegral_integral_swap
    (f := fun t y => (1 - t) * Real.cos (t * (U * (x - y)))) hi
  simp_rw [hpoint]
  rw [integral_const_mul, ← hswap]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact integral_const_mul _ _

/-- For [a probability law μ](hyp:μ), [a positive bandwidth U](hyp:U,hU),
[a threshold x](hyp:x), and [a reference value q and error R](hyp:q,R), if
[the distance between one plus the expected Prawitz sign approximation at
U(x − y) and 2q, plus the expected squared sinc of U(x − y)/2, is at most
2R](hyp:hspectral), then [the CDF of μ at x is within R of q](goal).
This isolates the remaining spectral comparison from the atomic endpoint
step. -/
theorem prawitz_cdf_error_of_spectral_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U : ℝ) (hU : 0 < U) (x q R : ℝ)
    (hspectral :
      |1 + (∫ y, prawitzSignApprox (U * (x - y)) ∂μ) - 2 * q| +
        (∫ y, Real.sinc (U * (x - y) / 2) ^ 2 ∂μ) ≤ 2 * R) :
    |(μ (Set.Iic x)).toReal - q| ≤ R := by
  obtain ⟨hlo, hhi⟩ := prawitz_cdf_spatial_bounds μ U hU x
  have hl := neg_abs_le (1 + (∫ y, prawitzSignApprox (U * (x - y)) ∂μ) - 2 * q)
  have hu := le_abs_self (1 + (∫ y, prawitzSignApprox (U * (x - y)) ∂μ) - 2 * q)
  rw [abs_le]
  constructor <;> linarith

end Causalean.Stat.CLT.BerryEsseen
