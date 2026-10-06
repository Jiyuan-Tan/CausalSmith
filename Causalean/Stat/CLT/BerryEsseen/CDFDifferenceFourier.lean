module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourierFubini
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceIntegrable
public import Mathlib.Probability.CentralLimitTheorem

/-! # Fourier transform of a difference of distribution functions

The Fourier transform of the difference of two CDFs is identified with
the difference of their characteristic functions away from frequency zero.
Finite first moments supply the integrability needed for the identity.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [two probability laws μ and ν with finite first moments](hyp:hμ,hν) and
[a nonzero frequency t](hyp:ht), [t times the Fourier integral of the
difference of their CDFs equals i times the difference of their
characteristic functions at t](goal); that is, the Fourier integral is
(i/t)(φ_μ(t) − φ_ν(t)), written so as to avoid division at zero. -/
theorem cdf_difference_fourier_identity
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ => y) μ)
    (hν : Integrable (fun y : ℝ => y) ν)
    (t : ℝ) (ht : t ≠ 0) :
    (t : ℂ) *
      (∫ x : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ)) =
      Complex.I * (charFun μ t - charFun ν t) := by
  have hExp (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
      Integrable (fun x : ℝ => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) ρ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    simpa only [Complex.ofReal_mul] using
      le_of_eq (Complex.norm_exp_ofReal_mul_I (t * x))
  rw [cdf_difference_fourier_fubini μ ν hμ hν t]
  rw [← integral_const_mul]
  simp_rw [← integral_const_mul, fourier_oriented_interval_identity _ _ t ht]
  simp_rw [integral_const_mul]
  have hinner (a : ℝ) :
      (∫ b : ℝ, Complex.exp (((t * a : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((t * b : ℝ) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (((t * a : ℝ) : ℂ) * Complex.I) - charFun ν t := by
    rw [integral_sub (integrable_const (μ := ν) _) (hExp ν), integral_const]
    simp [charFun_apply_real]
  simp_rw [hinner]
  rw [integral_sub (hExp μ) (integrable_const (μ := μ) _), integral_const]
  simp [charFun_apply_real]

end Causalean.Stat.CLT.BerryEsseen
