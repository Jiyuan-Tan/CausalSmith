module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourierQuotient
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceModulus
public import Causalean.Stat.CLT.BerryEsseen.EsseenAnalyticOneSided
public import Mathlib.Probability.CentralLimitTheorem

/-! # One-sided scalar Esseen comparison

This isolates the upper CDF comparison in the Esseen inversion step with constant 24/π.
The lower comparison can be obtained by reflecting both laws; the reference
interval-mass condition is preserved by reflection.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- When [two scalar probability laws μ and ν have finite first moments](hyp:hμfirst,hνfirst),
[the reference law ν assigns every interval at most L times its length,
for a nonnegative constant L](hyp:hL,hν), and [the bandwidth T is
positive](hyp:hT), [the CDF of μ exceeds the CDF of ν at every point by at most 1/π times the
integral over [−T, T] of the characteristic-function discrepancy divided by
|t|, plus the Esseen smoothing error 24L/(πT)](goal). -/
theorem cdf_esseen_inversion_one_sided
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμfirst : Integrable (fun y : ℝ => y) μ)
    (hνfirst : Integrable (fun y : ℝ => y) ν)
    (L : ℝ) (hL : 0 ≤ L)
    (hν : ∀ a b : ℝ, a ≤ b →
      (ν (Set.Ioc a b)).toReal ≤ L * (b - a))
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    (μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal ≤
      (1 / Real.pi) *
        (∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t|) +
      24 * L / (Real.pi * T) := by
  have hH := integrable_cdf_difference_of_first_moments μ ν hμfirst hνfirst
  have hdown := cdf_difference_one_sided_modulus μ ν L hν
  have hbound := integrable_one_sided_esseen_fourier_bound
    (fun y : ℝ => (μ (Set.Iic y)).toReal - (ν (Set.Iic y)).toReal)
    hH L hL hdown T hT x
  rw [cdf_difference_fourier_magnitude_integral μ ν hμfirst hνfirst T] at hbound
  exact hbound

end Causalean.Stat.CLT.BerryEsseen
