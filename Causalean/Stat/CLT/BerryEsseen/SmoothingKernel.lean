module
public import Causalean.Stat.CLT.BerryEsseen.SincFourthFourier
public import Causalean.Stat.CLT.BerryEsseen.SincSquaredFourier
public import Causalean.Stat.CLT.BerryEsseen.SincTriangleConvolution
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Probability.CentralLimitTheorem

/-! # A compact-frequency probability smoothing kernel

The fourth power of the sinc function gives a nonnegative density whose
Fourier transform is supported on a bounded interval. These analytic facts
are the first layer of the quantitative CDF smoothing argument.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- At positive bandwidth `T`, this rescaled fourth power of sinc is a
probability smoothing density with Fourier support in `[-T,T]`. -/
noncomputable def sinc4Kernel (T x : ℝ) : ℝ :=
  (3 * T / (8 * Real.pi)) * (Real.sinc (T * x / 4)) ^ 4

/-- The fourth-power sinc kernel is nonnegative at every real argument when
its bandwidth is positive. -/
theorem sinc4Kernel_nonneg (T : ℝ) (hT : 0 < T) (x : ℝ) :
    0 ≤ sinc4Kernel T x := by
  unfold sinc4Kernel
  positivity

/-- The fourth-power sinc kernel is integrable on the real line at every
positive bandwidth. -/
theorem sinc4Kernel_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (sinc4Kernel T) volume := by
  have hsinc : Integrable (fun x : ℝ => Real.sinc x ^ 4) := by
    apply (integrable_inv_one_add_sq.const_mul (4 : ℝ)).mono
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.sinc x ^ 4)]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 4 * (1 + x ^ 2)⁻¹)]
      rw [inv_eq_one_div, mul_one_div]
      apply (le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
      by_cases hx : |x| ≤ 1
      · have ha2 : |x| * |x| ≤ 1 * 1 :=
          mul_self_le_mul_self (abs_nonneg x) hx
        have hx2 : x ^ 2 ≤ 1 := by simpa [sq_abs, pow_two] using ha2
        have hs := Real.abs_sinc_le_one x
        have hsl := neg_abs_le (Real.sinc x)
        have hsr := le_abs_self (Real.sinc x)
        have hs2 : Real.sinc x ^ 2 ≤ 1 := by nlinarith
        have hs4 : Real.sinc x ^ 4 ≤ 1 := by
          nlinarith [mul_self_le_mul_self (sq_nonneg (Real.sinc x)) hs2]
        nlinarith
      · have hxabs : 1 < |x| := lt_of_not_ge hx
        have hx0 : x ≠ 0 := by
          intro h
          subst x
          norm_num at hxabs
        rw [Real.sinc_of_ne_zero hx0, div_pow, div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity : 0 < x ^ 4)).2
        have habs2 : (1 : ℝ) ^ 2 < |x| ^ 2 :=
          (sq_lt_sq₀ (by positivity) (abs_nonneg x)).2 hxabs
        have hx2 : 1 < x ^ 2 := by simpa [sq_abs] using habs2
        have hs := Real.abs_sin_le_one x
        have hsl := neg_abs_le (Real.sin x)
        have hsr := le_abs_self (Real.sin x)
        have hs2 : Real.sin x ^ 2 ≤ 1 := by nlinarith
        have hs4 : Real.sin x ^ 4 ≤ 1 := by
          nlinarith [mul_self_le_mul_self (sq_nonneg (Real.sin x)) hs2]
        calc
          Real.sin x ^ 4 * (1 + x ^ 2) ≤ 1 * (1 + x ^ 2) :=
            mul_le_mul_of_nonneg_right hs4 (by positivity)
          _ ≤ 2 * x ^ 2 := by nlinarith
          _ ≤ 4 * x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 1)]
  have hscaled : Integrable (fun x : ℝ => Real.sinc (T * x / 4) ^ 4) := by
    convert hsinc.comp_mul_left' (by positivity : T / 4 ≠ 0) using 1
    ext x
    congr 1
    ring_nf
  exact hscaled.const_mul (3 * T / (8 * Real.pi))

/-- The integral of the fourth-power sinc kernel is one at every positive
bandwidth, so it defines a probability density. -/
theorem sinc4Kernel_integral_eq_one (T : ℝ) (hT : 0 < T) :
    ∫ x : ℝ, sinc4Kernel T x = 1 := by
  /- Set `t = 0` in `sincFourth_fourier_triangleConvolution`, use
  `sincTriangle_square_integral` to obtain ∫ sinc(x)^4 dx = 2π/3, then scale
  x ↦ T*x/4 via `Measure.integral_comp_mul_left`. Since `T > 0`, the
  Jacobian is `4/T`; the prefactor 3T/(8π) makes the integral one.
  At zero frequency, rewrite `|0-u|` as `|u|` and the convolution
  integrand as the square of the triangle. -/
  have hfourier := sincFourth_fourier_triangleConvolution 0
  have hzero : (∫ x : ℝ, Real.sinc x ^ 4) = 2 * Real.pi / 3 := by
    have htri : (∫ u : ℝ,
        (Real.pi * max (1 - |u| / 2) 0) *
          (Real.pi * max (1 - |(0 : ℝ) - u| / 2) 0)) =
        4 * Real.pi ^ 2 / 3 := by
      convert sincTriangle_square_integral using 1
      congr 1
      ext u
      simp only [zero_sub, abs_neg]
      ring
    rw [htri] at hfourier
    simp only [zero_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
      integral_complex_ofReal] at hfourier
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    apply Complex.ofReal_injective
    convert hfourier using 1 <;> push_cast <;> field_simp <;> ring
  have hscale : (∫ x : ℝ, Real.sinc (T * x / 4) ^ 4) =
      (4 / T) * (∫ x : ℝ, Real.sinc x ^ 4) := by
    have h := Measure.integral_comp_mul_left
      (fun x : ℝ => Real.sinc x ^ 4) (T / 4)
    convert h using 1
    · congr 1; ext x; ring_nf
    · simp only [smul_eq_mul, abs_inv, abs_of_pos (by positivity : 0 < T / 4)]
      field_simp
  unfold sinc4Kernel
  rw [integral_const_mul, hscale, hzero]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- For [a positive bandwidth T](hyp:hT), [the Fourier transform of the
fourth-power sinc kernel vanishes](goal) at [every frequency t with
|t| ≥ T](hyp:ht), that is, outside its bandwidth interval. -/
theorem sinc4Kernel_fourier_eq_zero (T t : ℝ) (hT : 0 < T) (ht : T ≤ |t|) :
    ∫ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          (sinc4Kernel T x : ℂ) = 0 := by
  /- Apply `sincFourth_fourier_triangleConvolution` and
  `sincTriangle_convolution_outside`. Scale x ↦ T*x/4; the triangle
  convolution is zero also at the support endpoints |t| = T. Under this
  change of variables the unscaled Fourier frequency is `4*t/T`, so
  `4 ≤ |4*t/T|` follows from `T ≤ |t|`. Move the real prefactor through
  the complex integral before invoking the unscaled identity. -/
  have hfreq : 4 ≤ |4 * t / T| := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hT]
    apply (le_div_iff₀ hT).2
    nlinarith
  have hbase : (∫ y : ℝ,
      Complex.exp ((((4 * t / T) * y : ℝ) : ℂ) * Complex.I) *
        ((Real.sinc y ^ 4 : ℝ) : ℂ)) = 0 := by
    rw [sincFourth_fourier_triangleConvolution,
      sincTriangle_convolution_outside _ hfreq]
    simp
  let g : ℝ → ℂ := fun y =>
    Complex.exp ((((4 * t / T) * y : ℝ) : ℂ) * Complex.I) *
      ((Real.sinc y ^ 4 : ℝ) : ℂ)
  have hchange : (∫ x : ℝ,
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        ((Real.sinc (T * x / 4) ^ 4 : ℝ) : ℂ)) = 0 := by
    calc
      _ = ∫ x : ℝ, g ((T / 4) * x) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [g]
        have hw : (4 * t / T) * ((T / 4) * x) = t * x := by
          field_simp
        rw [hw]
        congr 1
        congr 1
        ring_nf
      _ = |(T / 4)⁻¹| • ∫ y : ℝ, g y :=
        Measure.integral_comp_mul_left g (T / 4)
      _ = 0 := by
        have hg : (∫ y : ℝ, g y) = 0 := hbase
        simp [hg]
  calc
    _ = ((3 * T / (8 * Real.pi) : ℝ) : ℂ) *
          ∫ x : ℝ,
            Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
              ((Real.sinc (T * x / 4) ^ 4 : ℝ) : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      unfold sinc4Kernel
      push_cast
      ring
    _ = 0 := by rw [hchange, mul_zero]

end Causalean.Stat.CLT.BerryEsseen
