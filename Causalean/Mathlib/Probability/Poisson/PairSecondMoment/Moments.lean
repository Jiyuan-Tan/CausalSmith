module
public import Causalean.Mathlib.Probability.Poisson.Moments
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Scalar factorial moments of a Poisson count

This module supplies the first, ordered-pair, and raw second moments of a
scalar Poisson count used to weight the count fibres of a finite Poisson
sample.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

/-- Under [a Poisson law with nonnegative rate](hyp:rate), [the expected
count equals that rate](goal). -/
theorem poisson_count_first_moment (rate : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure rate) = (rate : ℝ) :=
  Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment rate

/-- Under [a Poisson law with nonnegative rate](hyp:rate), [the ordered count
of two distinct positions is integrable](goal). -/
theorem integrable_poisson_ordered_pairs (rate : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) (poissonMeasure rate) := by
  have hsq :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two rate).integrable_sq
  have hfirst :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two rate).integrable
      (by norm_num)
  rw [show (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) =
      (fun n : ℕ => (n : ℝ) ^ 2 - (n : ℝ)) by
        funext n
        ring]
  exact hsq.sub hfirst

private lemma poisson_descFactorial_two_shift (rate : ℝ≥0) (k : ℕ) :
    Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ (k + 2) /
          ((k + 2).factorial : ℝ) * ((k + 2).descFactorial 2 : ℝ) =
      ((rate : ℝ) ^ 2 * Real.exp (-(rate : ℝ))) *
        ((rate : ℝ) ^ k / (k.factorial : ℝ)) := by
  have hfacNat : k.factorial * (k + 2).descFactorial 2 = (k + 2).factorial := by
    simpa [Nat.add_sub_cancel] using
      (Nat.factorial_mul_descFactorial (n := k + 2) (k := 2) (Nat.le_add_left 2 k))
  have hfac : (k.factorial : ℝ) * ((k + 2).descFactorial 2 : ℝ) =
      ((k + 2).factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [pow_add]
  field_simp [Nat.factorial_ne_zero]
  linear_combination ((rate : ℝ) ^ k * (rate : ℝ) ^ 2) * hfac

/-- Under [a Poisson law with nonnegative rate](hyp:rate), [the expected
ordered number of distinct count positions is the squared rate](goal). -/
theorem poisson_ordered_pairs_second_moment (rate : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) * ((n : ℝ) - 1) ∂poissonMeasure rate) =
      (rate : ℝ) ^ 2 := by
  rw [show (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) =
      fun n => (n.descFactorial 2 : ℝ) by
        funext n
        simp only [Nat.cast_descFactorial_two]]
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  let f : ℕ → ℝ := fun n =>
    Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / (n.factorial : ℝ) *
      (n.descFactorial 2 : ℝ)
  have hshift : Summable (fun k => f (k + 2)) := by
    apply Summable.congr
      ((NormedSpace.expSeries_div_hasSum_exp (rate : ℝ)).summable.mul_left
        ((rate : ℝ) ^ 2 * Real.exp (-(rate : ℝ))))
    intro k
    exact (poisson_descFactorial_two_shift rate k).symm
  have hprefix : ∑ k ∈ Finset.range 2, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < 2 := Finset.mem_range.mp hk
    have hzero : k.descFactorial 2 = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr hklt
    simp only [f, hzero, Nat.cast_zero, mul_zero]
  calc
    ∑' n, Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / ↑n.factorial *
        ↑(n.descFactorial 2) = ∑' n, f n := by rfl
    _ = ∑ k ∈ Finset.range 2, f k + ∑' k, f (k + 2) :=
      (hshift.sum_add_tsum_nat_add').symm
    _ = ∑' k, (((rate : ℝ) ^ 2 * Real.exp (-(rate : ℝ))) *
        ((rate : ℝ) ^ k / (k.factorial : ℝ))) := by
      rw [hprefix, zero_add]
      congr 1
      funext k
      exact poisson_descFactorial_two_shift rate k
    _ = ((rate : ℝ) ^ 2 * Real.exp (-(rate : ℝ))) * Real.exp (rate : ℝ) := by
      rw [tsum_mul_left]
      simpa only [Real.exp_eq_exp_ℝ] using congrArg
        (fun z : ℝ => ((rate : ℝ) ^ 2 * Real.exp (-(rate : ℝ))) * z)
        (NormedSpace.expSeries_div_hasSum_exp (rate : ℝ)).tsum_eq
    _ = (rate : ℝ) ^ 2 := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp

/-- Under [a Poisson law with nonnegative rate](hyp:rate), [the squared count
is integrable](goal). -/
theorem integrable_poisson_count_sq (rate : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure rate) :=
  (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two rate).integrable_sq

/-- Under [a Poisson law with nonnegative rate](hyp:rate), [the expected
squared count is its squared rate plus its rate](goal). -/
theorem poisson_count_second_moment (rate : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure rate) =
      (rate : ℝ) ^ 2 + (rate : ℝ) := by
  have h : (fun n : ℕ => (n : ℝ) ^ 2) =
      (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) + (n : ℝ)) := by
    funext n
    ring
  rw [h, integral_add (integrable_poisson_ordered_pairs rate)
    ((Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two rate).integrable
      (by norm_num))]
  rw [poisson_ordered_pairs_second_moment, poisson_count_first_moment]

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment
