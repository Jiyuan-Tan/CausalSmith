module
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Moments
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Factoring the two independent Poisson count series

An integrable function of each count has a product expectation under two
independent scalar Poisson laws. The iterated count series uses the weights
that occur in the finite-sample count-mixture formula.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

/-- Given [two nonnegative Poisson rates](hyp:rateA,rateB), [two scalar count
functions](hyp:f,g), and [their integrability under the respective Poisson
laws](hyp:hf,hg), [the weighted double count series factors into their two
expectations](goal). -/
theorem poisson_pair_weighted_tsum_mul
    (rateA rateB : ℝ≥0) (f g : ℕ → ℝ)
    (hf : Integrable f (poissonMeasure rateA))
    (hg : Integrable g (poissonMeasure rateB)) :
    (∑' m : ℕ, ∑' n : ℕ,
      ((poissonMeasure rateA) ({m} : Set ℕ)).toReal *
        ((poissonMeasure rateB) ({n} : Set ℕ)).toReal *
          (f m * g n)) =
      (∫ m : ℕ, f m ∂poissonMeasure rateA) *
        (∫ n : ℕ, g n ∂poissonMeasure rateB) := by
  -- Apply `integral_countable` to each scalar law, using `hf` and `hg`.
  -- The weighted series is absolutely summable by the integrability of
  -- `(fun p : ℕ × ℕ => f p.1 * g p.2)` under the product measure;
  -- `Summable.tsum_prod` (or two `tsum_mul_*` rewrites) then separates it.
  let a (m : ℕ) : ℝ := ((poissonMeasure rateA) ({m} : Set ℕ)).toReal * f m
  let b (n : ℕ) : ℝ := ((poissonMeasure rateB) ({n} : Set ℕ)).toReal * g n
  have ha : Summable a := by
    have hdirac : Integrable f
        (Measure.sum fun m : ℕ =>
          (poissonMeasure rateA) ({m} : Set ℕ) • Measure.dirac m) := by
      simpa only [Measure.sum_smul_dirac] using hf
    apply Summable.of_norm
    simpa only [a, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using hdirac.summable_of_dirac
  have hb : Summable b := by
    have hdirac : Integrable g
        (Measure.sum fun n : ℕ =>
          (poissonMeasure rateB) ({n} : Set ℕ) • Measure.dirac n) := by
      simpa only [Measure.sum_smul_dirac] using hg
    apply Summable.of_norm
    simpa only [b, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using hdirac.summable_of_dirac
  have hfa : (∫ m : ℕ, f m ∂poissonMeasure rateA) = ∑' m, a m := by
    simpa only [a, smul_eq_mul, measureReal_def] using integral_countable hf
  have hgb : (∫ n : ℕ, g n ∂poissonMeasure rateB) = ∑' n, b n := by
    simpa only [b, smul_eq_mul, measureReal_def] using integral_countable hg
  rw [hfa, hgb]
  calc
    _ = ∑' m : ℕ, ∑' n : ℕ, a m * b n := by
      congr 1
      funext m
      congr 1
      funext n
      dsimp [a, b]
      ring
    _ = (∑' m : ℕ, a m) * (∑' n : ℕ, b n) := by
      simpa only [Summable.tsum_mul_left _ hb] using
        (Summable.tsum_mul_right (∑' n : ℕ, b n) ha)

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment
