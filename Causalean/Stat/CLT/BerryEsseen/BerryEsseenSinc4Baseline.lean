module
public import Causalean.Stat.CLT.BerryEsseen.CDFSandwich
public import Causalean.Stat.CLT.BerryEsseen.SmoothedCDFFourier
public import Mathlib.Probability.CentralLimitTheorem

/-! # Baseline normal smoothing via the fourth-power sinc kernel

The already-proved Fourier and CDF sandwich estimates yield an explicit
normal smoothing bound. Its Gaussian error constant records exactly what
this kernel proves; a sharper inversion step is needed for Esseen's constant.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a scalar probability law with finite first moment](hyp:hfirst) and
[a positive bandwidth T](hyp:hT), [its CDF at every threshold x differs from
the standard Gaussian CDF by at most 1/π times the integral over [−T, T] of
the characteristic-function discrepancy divided by |t|, plus
24/(T√(2π))](goal). -/
theorem normal_cdf_smoothing_sinc4_baseline
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun y : ℝ => y) μ)
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    |(μ (Set.Iic x)).toReal -
      ((gaussianReal 0 1) (Set.Iic x)).toReal| ≤
      (1 / Real.pi) *
      (∫ t in (-T)..T,
          ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
        24 / (T * Real.sqrt (2 * Real.pi)) := by
  have hg : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 1)
  let L : ℝ := 1 / Real.sqrt (2 * Real.pi)
  let B : ℝ := (1 / (2 * Real.pi)) *
    (∫ t in (-T)..T,
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hB : 0 ≤ B := by
    have h := sinc4_smoothed_cdf_fourier_bound μ (gaussianReal 0 1)
      hfirst hg T hT 0
    exact (abs_nonneg _).trans h
  have hν : ∀ a b : ℝ, a ≤ b →
      ((gaussianReal 0 1) (Set.Ioc a b)).toReal ≤ L * (b - a) := by
    intro a b hab
    simpa [L, div_eq_mul_inv, mul_comm] using
      standardGaussian_interval_mass_le a b hab
  have hsmooth : ∀ z : ℝ,
      |∫ y : ℝ,
        ((μ (Set.Iic (z - y))).toReal -
          ((gaussianReal 0 1) (Set.Iic (z - y))).toReal) *
          sinc4Kernel T y| ≤ B := by
    intro z
    exact sinc4_smoothed_cdf_fourier_bound μ (gaussianReal 0 1)
      hfirst hg T hT z
  have hsand := sinc4_cdf_sandwich μ (gaussianReal 0 1)
    T L B hT hL hν hsmooth x
  calc
    _ ≤ 2 * B + 24 * L / T := hsand
    _ = (1 / Real.pi) *
        (∫ t in (-T)..T,
          ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
        24 / (T * Real.sqrt (2 * Real.pi)) := by
      dsimp [B, L]
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
      field_simp

end Causalean.Stat.CLT.BerryEsseen
