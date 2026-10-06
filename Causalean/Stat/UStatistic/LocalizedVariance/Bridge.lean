module
public import Causalean.Stat.UStatistic.LocalizedVariance.Main

/-!
# Extended nonnegative localized variance bound

The real centered second moment bound for a localized unordered pair average
transfers to its extended nonnegative integral.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.UStatistic.LocalizedVariance

variable {X : Type*} [MeasurableSpace X]
  (P : Measure X) [IsProbabilityMeasure P]
  {H W : X → X → ℝ} {M : ℝ} (h : LocalizedKernel H W M)

include h

/-- A [probability law and localized-kernel certificate](hyp:P,h) with [at least two
observations](hyp:hn) give [an extended-nonnegative centered second-moment bound retaining
the localized row and pair mass scales](goal). -/
theorem lintegral_centered_second_moment_le {n : ℕ} (hn : 2 ≤ n) :
    (∫⁻ ω, ENNReal.ofReal
      ((uStatistic n H ω - ∫ z, uStatistic n H z ∂iidLaw P n) ^ 2)
      ∂iidLaw P n) ≤
      ENNReal.ofReal
        (16 * M ^ 2 *
          (rowMassSq P W / (n : ℝ) + pairMass P W / (n : ℝ) ^ 2)) := by
  have : IsProbabilityMeasure (iidLaw P n) := by
    unfold iidLaw
    infer_instance
  calc
    _ = evariance (uStatistic n H) (iidLaw P n) :=
      (evariance_eq_lintegral_ofReal (uStatistic n H) (iidLaw P n)).symm
    _ = ENNReal.ofReal (variance (uStatistic n H) (iidLaw P n)) :=
      (ofReal_variance (uStatistic_memLp_two P h)).symm
    _ ≤ ENNReal.ofReal
          (16 * M ^ 2 *
            (rowMassSq P W / (n : ℝ) + pairMass P W / (n : ℝ) ^ 2)) :=
      ENNReal.ofReal_le_ofReal (by
        rw [variance_eq_integral (uStatistic_memLp_two P h).aemeasurable]
        exact centered_second_moment_le P h hn)

end Causalean.Stat.UStatistic.LocalizedVariance
