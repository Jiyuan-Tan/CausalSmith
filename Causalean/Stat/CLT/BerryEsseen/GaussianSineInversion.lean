module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Probability.CentralLimitTheorem

/-! # Sine inversion of the standard Gaussian distribution function

This Gaussian-only identity is independent of Prawitz filters and probability
comparison inequalities. The frequency integrand has a removable singularity
at zero, with its Lebesgue endpoint value assigned by real division.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- At [any real threshold](hyp:x), the [Gaussian sine quotient is
integrable on the positive frequency half-line](goal). -/
theorem gaussian_sine_quotient_integrable (x : ℝ) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t) (Set.Ioi 0) := by
  have hg : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) := by
    simpa only [div_eq_mul_inv, one_mul, neg_mul, mul_neg, mul_comm] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))
  have hm : Measurable (fun t : ℝ =>
      Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t) := by fun_prop
  apply (hg.integrableOn.const_mul |x|).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hs : |Real.sin (t * x)| / t ≤ |x| := by
    apply (div_le_iff₀ ht0).mpr
    simpa only [abs_mul, abs_of_pos ht0, mul_comm] using
      (Real.abs_sin_le_abs (x := t * x))
  rw [Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos ht0]
  calc
    _ = Real.exp (-(t ^ 2 / 2)) * (|Real.sin (t * x)| / t) := by ring
    _ ≤ Real.exp (-(t ^ 2 / 2)) * |x| :=
      mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
    _ = _ := by ring

/-- At [every real threshold x](hyp:x), [the standard Gaussian probability of
the half-line `(−∞, x]` equals one half plus 1/π times the integral over
t > 0 of exp(−t²/2)·sin(tx)/t](goal). -/
theorem gaussian_cdf_sine_inversion (x : ℝ) :
    ((gaussianReal 0 1) (Set.Iic x)).toReal =
      1 / 2 + (1 / Real.pi) *
        (∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t) := by
  -- Take the real part of the Gaussian characteristic function, whose
  -- Mathlib proof evaluates the Gaussian Fourier integral.
  have hg : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) := by
    simpa only [div_eq_mul_inv, one_mul, neg_mul, mul_neg, mul_comm] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))
  have hp := integrable_gaussianPDFReal 0 1
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
  have hpdf (t : ℝ) : gaussianPDFReal 0 1 t =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 / 2)) := by
    simp [gaussianPDFReal, neg_div]
  have hchar (y : ℝ) :
      ∫ t : ℝ, gaussianPDFReal 0 1 t * Real.cos (t * y) =
        Real.exp (-(y ^ 2 / 2)) := by
    have hi : Integrable (fun t : ℝ =>
        Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)) (gaussianReal 0 1) := by
      apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
      exact Filter.Eventually.of_forall (fun t => by
        simp only [Complex.norm_exp_ofReal_mul_I, le_refl])
    have h := congrArg Complex.re (charFun_gaussianReal (μ := 0) (v := 1) y)
    rw [charFun_apply_real] at h
    simp_rw [← Complex.ofReal_mul, mul_comm y] at h
    have hre := integral_re hi
    simp only [RCLike.re_to_complex] at hre
    rw [← hre] at h
    simp only [Complex.exp_ofReal_mul_I_re] at h
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)] at h
    simpa only [smul_eq_mul, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
      NNReal.coe_one, Complex.ofReal_one, one_mul, ← Complex.ofReal_pow,
      ← Complex.ofReal_ofNat 2, ← Complex.ofReal_div, ← Complex.ofReal_neg,
      Complex.exp_ofReal_re] using h
  have hfull (y : ℝ) :
      ∫ t : ℝ, Real.exp (-(t ^ 2 / 2)) * Real.cos (t * y) =
        Real.sqrt (2 * Real.pi) * Real.exp (-(y ^ 2 / 2)) := by
    have h := hchar y
    simp_rw [hpdf, mul_assoc] at h
    rw [integral_const_mul] at h
    calc
      _ = Real.sqrt (2 * Real.pi) *
          ((Real.sqrt (2 * Real.pi))⁻¹ *
            ∫ t : ℝ, Real.exp (-(t ^ 2 / 2)) * Real.cos (t * y)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
      _ = _ := by rw [h]
  have hcos (y : ℝ) :
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2 / 2)) * Real.cos (t * y) =
        Real.pi * gaussianPDFReal 0 1 y := by
    have he (t : ℝ) :
        Real.exp (-(|t| ^ 2 / 2)) * Real.cos (|t| * y) =
          Real.exp (-(t ^ 2 / 2)) * Real.cos (t * y) := by
      by_cases ht : 0 ≤ t
      · rw [abs_of_nonneg ht]
      · simp [abs_of_neg (lt_of_not_ge ht), neg_mul, Real.cos_neg]
    have hhalf := integral_comp_abs
      (f := fun t : ℝ => Real.exp (-(t ^ 2 / 2)) * Real.cos (t * y))
    simp_rw [he] at hhalf
    rw [hfull] at hhalf
    rw [hpdf]
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
    have hc : Real.sqrt (2 * Real.pi) / 2 =
        Real.pi * (Real.sqrt (2 * Real.pi))⁻¹ := by
      apply (eq_div_iff hs).mpr
      nlinarith
    calc
      _ = (Real.sqrt (2 * Real.pi) / 2) * Real.exp (-(y ^ 2 / 2)) := by
        linarith [hhalf]
      _ = _ := by rw [hc]; ring
  -- Reflection and total mass one fix the integration constant at zero.
  have hzero : ∫ t in Set.Iic (0 : ℝ), gaussianPDFReal 0 1 t = 1 / 2 := by
    have he (t : ℝ) : gaussianPDFReal 0 1 (-t) = gaussianPDFReal 0 1 t := by
      simp [hpdf]
    have href := integral_comp_neg_Ioi 0 (gaussianPDFReal 0 1)
    simp only [neg_zero, he] at href
    have hsum := intervalIntegral.integral_Iic_add_Ioi
      (b := 0) hp.integrableOn hp.integrableOn
    rw [integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : ℝ≥0) ≠ 0)] at hsum
    linarith
  -- Gaussian domination permits Fubini on the oriented spatial interval.
  have hprod : Integrable
      (Function.uncurry (fun y t : ℝ =>
        Real.exp (-(t ^ 2 / 2)) * Real.cos (t * y)))
      ((volume.restrict (Set.uIoc 0 x)).prod (volume.restrict (Set.Ioi 0))) := by
    have hu : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.uIoc 0 x) :=
      intervalIntegrable_iff.mp intervalIntegrable_const
    have hmajor := hu.mul_prod (hg.integrableOn (s := Set.Ioi 0))
    apply hmajor.mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro p
    change ‖Real.exp (-(p.2 ^ 2 / 2)) * Real.cos (p.2 * p.1)‖ ≤
      1 * Real.exp (-(p.2 ^ 2 / 2))
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs, one_mul]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)
  have hswap := intervalIntegral_integral_swap hprod
  have hinner (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      (∫ y in (0 : ℝ)..x, Real.exp (-(t ^ 2 / 2)) * Real.cos (t * y)) =
        Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left Real.cos (ne_of_gt ht), integral_cos]
    simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul]
    ring
  have hsine :
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2 / 2)) * Real.sin (t * x) / t) =
        Real.pi * ∫ y in (0 : ℝ)..x, gaussianPDFReal 0 1 y := by
    calc
      _ = ∫ t in Set.Ioi (0 : ℝ),
          (∫ y in (0 : ℝ)..x, Real.exp (-(t ^ 2 / 2)) * Real.cos (t * y)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact (hinner t ht).symm
      _ = ∫ y in (0 : ℝ)..x,
          (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2 / 2)) * Real.cos (t * y)) :=
        hswap.symm
      _ = ∫ y in (0 : ℝ)..x, Real.pi * gaussianPDFReal 0 1 y := by
        congr 1
        funext y
        exact hcos y
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      (fun t _ => gaussianPDFReal_nonneg 0 1 t)), hsine]
  have hdiff := intervalIntegral.integral_Iic_sub_Iic
    (a := 0) (b := x) hp.integrableOn hp.integrableOn
  rw [hzero] at hdiff
  rw [← hdiff]
  field_simp
  ring

end Causalean.Stat.CLT.BerryEsseen
