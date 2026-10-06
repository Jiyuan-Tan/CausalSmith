module
public import Causalean.Stat.CLT.BerryEsseen.CDFReflection
public import Causalean.Stat.CLT.BerryEsseen.EsseenOneSided
public import Mathlib.Probability.CentralLimitTheorem

/-! # Scalar Esseen inversion inequality

This module isolates the analytic CDF smoothing inequality from Gaussian
moments and iid sampling. The reference law has a globally Lipschitz CDF.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- When [two scalar probability laws μ and ν have finite first moments](hyp:hμfirst,hνfirst),
[the reference law ν assigns every interval at most L times its length,
for a nonnegative constant L](hyp:hL,hν), and [the bandwidth T is
positive](hyp:hT), [their CDF discrepancy at every point is at most 1/π times the integral over
[−T, T] of the characteristic-function discrepancy divided by |t|, plus the
Esseen smoothing error 24L/(πT)](goal). -/
theorem cdf_esseen_inversion_lipschitz
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμfirst : Integrable (fun y : ℝ => y) μ)
    (hνfirst : Integrable (fun y : ℝ => y) ν)
    (L : ℝ) (hL : 0 ≤ L)
    (hν : ∀ a b : ℝ, a ≤ b →
      (ν (Set.Ioc a b)).toReal ≤ L * (b - a))
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    |(μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal| ≤
      (1 / Real.pi) *
        (∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t|) +
      24 * L / (Real.pi * T) := by
  haveI : IsProbabilityMeasure (μ.map (fun y : ℝ => -y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (ν.map (fun y : ℝ => -y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hpos := cdf_esseen_inversion_one_sided μ ν hμfirst hνfirst L hL hν T hT x
  obtain ⟨hνref, hlower⟩ := reflected_reference_interval_and_cdf μ ν L hL hν
  have hneg := cdf_esseen_inversion_one_sided
    (μ.map (fun y : ℝ => -y)) (ν.map (fun y : ℝ => -y))
    (reflected_first_moment_integrable μ hμfirst)
    (reflected_first_moment_integrable ν hνfirst) L hL hνref T hT (-x)
  simp_rw [reflected_charFun_discrepancy] at hneg
  rw [abs_le]
  constructor
  · have h := (hlower x).trans hneg
    linarith
  · exact hpos

end Causalean.Stat.CLT.BerryEsseen
