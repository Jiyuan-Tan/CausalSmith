module
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Moments
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Summability of the two independent squared Poisson counts

The product of two scalar Poisson count laws gives a finite weighted double
series of squared counts. This is the count envelope used for the square of a
bilinear sum over independent finite samples.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

/-- Given [two nonnegative Poisson rates](hyp:rateA,rateB), [the double series
weighted by both squared counts is finite](goal). -/
theorem poisson_pair_count_sq_series_lt_top (rateA rateB : ℝ≥0) :
    (∑' m : ℕ, ∑' n : ℕ,
      (poissonMeasure rateA) ({m} : Set ℕ) *
        (poissonMeasure rateB) ({n} : Set ℕ) *
          ((m : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞) ^ 2)) < ⊤ := by
  have scalar (rate : ℝ≥0) :
      (∑' n : ℕ, (poissonMeasure rate) ({n} : Set ℕ) * (n : ℝ≥0∞) ^ 2) < ⊤ := by
    have h := (integrable_poisson_count_sq rate).lintegral_lt_top
    rw [lintegral_countable'] at h
    simp_rw [ENNReal.ofReal_pow (Nat.cast_nonneg _) 2, ENNReal.ofReal_natCast] at h
    simpa only [mul_comm] using h
  calc
    (∑' m : ℕ, ∑' n : ℕ,
        (poissonMeasure rateA) ({m} : Set ℕ) *
          (poissonMeasure rateB) ({n} : Set ℕ) *
            ((m : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞) ^ 2))
        = ∑' m : ℕ, ∑' n : ℕ,
            ((poissonMeasure rateA) ({m} : Set ℕ) * (m : ℝ≥0∞) ^ 2) *
              ((poissonMeasure rateB) ({n} : Set ℕ) * (n : ℝ≥0∞) ^ 2) := by
                congr 1
                funext m
                congr 1
                funext n
                ac_rfl
    _ = ∑' m : ℕ, ((poissonMeasure rateA) ({m} : Set ℕ) * (m : ℝ≥0∞) ^ 2) *
          (∑' n : ℕ, (poissonMeasure rateB) ({n} : Set ℕ) * (n : ℝ≥0∞) ^ 2) := by
            simp_rw [ENNReal.tsum_mul_left]
    _ = (∑' m : ℕ, (poissonMeasure rateA) ({m} : Set ℕ) * (m : ℝ≥0∞) ^ 2) *
          (∑' n : ℕ, (poissonMeasure rateB) ({n} : Set ℕ) * (n : ℝ≥0∞) ^ 2) := by
            rw [ENNReal.tsum_mul_right]
    _ < ⊤ := ENNReal.mul_lt_top (scalar rateA) (scalar rateB)

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment
