module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourier
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceIntegrable
public import Causalean.Stat.CLT.BerryEsseen.SincKernelInversion
public import Causalean.Stat.CLT.BerryEsseen.SmoothedCDFFourierFubini
public import Causalean.Stat.CLT.BerryEsseen.SmoothingKernel
public import Mathlib.Probability.CentralLimitTheorem

/-! # Fourier control of sinc-smoothed distribution functions

This module isolates the Fourier-analytic part of the scalar Esseen
smoothing argument. The difference of two finite-first-moment CDFs is
integrable; smoothing it by a compact-frequency kernel gives a bound in
terms of their characteristic functions.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [two probability laws with finite first moments](hyp:hμ,hν) and
[a positive bandwidth T](hyp:hT), [the convolution at every point z of their
CDF difference with the fourth-power sinc density is bounded in absolute
value by 1/(2π) times the integral over [−T, T] of their
characteristic-function discrepancy divided by |t|](goal). -/
theorem sinc4_smoothed_cdf_fourier_bound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ => y) μ)
    (hν : Integrable (fun y : ℝ => y) ν)
    (T : ℝ) (hT : 0 < T) (z : ℝ) :
    |∫ y : ℝ,
      ((μ (Set.Iic (z - y))).toReal -
        (ν (Set.Iic (z - y))).toReal) * sinc4Kernel T y| ≤
      (1 / (2 * Real.pi)) *
        (∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t|) := by
  have hchar (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
      (hρ : Integrable (fun y : ℝ => y) ρ) (t : ℝ) :
      ‖charFun ρ t - 1‖ ≤ |t| * ∫ y, |y| ∂ρ := by
    have he : Integrable (fun y : ℝ => Complex.exp ((t * y : ℝ) * Complex.I)) ρ := by
      apply Integrable.of_bound (by fun_prop) 1
      filter_upwards [] with y
      simpa [mul_comm] using (Complex.norm_exp_I_mul_ofReal (t * y)).le
    have hEq : charFun ρ t - 1 =
        ∫ y, (Complex.exp ((t * y : ℝ) * Complex.I) - 1) ∂ρ := by
      rw [charFun_apply_real]
      simp only [← Complex.ofReal_mul]
      rw [integral_sub he (integrable_const 1)]
      simp
    rw [hEq]
    calc
      ‖∫ y, (Complex.exp ((t * y : ℝ) * Complex.I) - 1) ∂ρ‖ ≤
          ∫ y, |t| * |y| ∂ρ := by
        apply norm_integral_le_of_norm_le (hρ.norm.const_mul |t|)
        filter_upwards [] with y
        have hp := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * y)
        simpa [Real.norm_eq_abs, abs_mul, mul_comm] using hp
      _ = |t| * ∫ y, |y| ∂ρ := by rw [integral_const_mul]
  have hquot : IntervalIntegrable
      (fun t : ℝ => ‖charFun μ t - charFun ν t‖ / |t|) volume (-T) T := by
    have hbound (t : ℝ) (ht : t ≠ 0) :
        ‖charFun μ t - charFun ν t‖ / |t| ≤
          (∫ y, |y| ∂μ) + (∫ y, |y| ∂ν) := by
      have htpos : 0 < |t| := abs_pos.mpr ht
      have htri : ‖charFun μ t - charFun ν t‖ ≤
          ‖charFun μ t - 1‖ + ‖charFun ν t - 1‖ := by
        convert norm_sub_le (charFun μ t - 1) (charFun ν t - 1) using 1
        ring_nf
      apply (div_le_iff₀ htpos).2
      nlinarith [hchar μ hμ t, hchar ν hν t]
    have hmeas : Measurable (fun t : ℝ =>
        ‖charFun μ t - charFun ν t‖ / |t|) := by fun_prop
    apply (intervalIntegrable_iff).2
    apply IntegrableOn.of_bound (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top)
      hmeas.aestronglyMeasurable
      ((∫ y, |y| ∂μ) + (∫ y, |y| ∂ν))
    filter_upwards [] with t
    by_cases ht : t = 0
    · subst t
      simp only [charFun_zero, probReal_univ, Complex.ofReal_one, sub_self,
        norm_zero, abs_zero, div_zero]
      exact add_nonneg (integral_nonneg (fun y => abs_nonneg y))
        (integral_nonneg (fun y => abs_nonneg y))
    · simpa [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (abs_nonneg t))]
        using hbound t ht
  let K : ℝ → ℂ := fun t => ∫ u : ℝ,
    Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (sinc4Kernel T u : ℂ)
  have hK (t : ℝ) : ‖K t‖ ≤ 1 := by
    calc
      ‖K t‖ ≤ ∫ u : ℝ, ‖Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
          (sinc4Kernel T u : ℂ)‖ := norm_integral_le_integral_norm _
      _ = ∫ u : ℝ, sinc4Kernel T u := by
        apply integral_congr_ae
        filter_upwards with u
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I,
          one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sinc4Kernel_nonneg T hT u)]
      _ = 1 := sinc4Kernel_integral_eq_one T hT
  have hpoint (t : ℝ) :
      ‖(Complex.exp (((-(t * z) : ℝ) : ℂ) * Complex.I) *
          (Complex.I * (charFun μ t - charFun ν t)) / (t : ℂ)) * K t‖ ≤
        ‖charFun μ t - charFun ν t‖ / |t| := by
    simp only [norm_mul, norm_div, Complex.norm_exp_ofReal_mul_I, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (div_nonneg (norm_nonneg _) (abs_nonneg t)) (hK t)
  have hbound : ‖∫ t in (-T)..T,
          (Complex.exp (((-(t * z) : ℝ) : ℂ) * Complex.I) *
            (Complex.I * (charFun μ t - charFun ν t)) / (t : ℂ)) * K t‖ ≤
      ∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith) _ hquot
    filter_upwards [] with t
    exact fun _ => hpoint t
  have hfactor : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  have hid := sinc4_smoothed_cdf_fourier_identity μ ν hμ hν T hT z
  change _ = (↑(1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t in (-T)..T,
      (Complex.exp (((-(t * z) : ℝ) : ℂ) * Complex.I) *
        (Complex.I * (charFun μ t - charFun ν t)) / (t : ℂ)) * K t at hid
  have hnorm := congrArg norm hid
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
    abs_of_nonneg hfactor] at hnorm
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left hbound hfactor

end Causalean.Stat.CLT.BerryEsseen
