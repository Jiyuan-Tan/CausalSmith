/-! ## Quarter-mean Poisson overflow -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.Concentration.PoissonSelfNormalized

open Causalean.Stat.Concentration.PoissonSelfNormalized

/-- For [a positive sample size](hyp:hn), [a Poisson count with mean one quarter
of that size overshoots the sample size with probability at most
`exp (-n/8)`](goal). -/
theorem poisson_quarter_overflow_le_exp (n : ℕ) (hn : 0 < n) :
    (poissonMeasure ((n : ℝ≥0) / 4)).real (Set.Ioi n) ≤
      Real.exp (-(n : ℝ) / 8) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt :
      Real.sqrt (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) * ((n : ℝ) / 8)) =
        (n : ℝ) / 4 := by
    rw [show 2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) * ((n : ℝ) / 8) =
        ((n : ℝ) / 4) ^ 2 by norm_num; ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hsubset :
      Set.Ioi n ⊆
        {w : ℕ | (w : ℝ) - (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) >
          Real.sqrt (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) * ((n : ℝ) / 8)) +
            2 * ((n : ℝ) / 8)} := by
    intro w hw
    simp only [Set.mem_Ioi] at hw ⊢
    have hwR : (n : ℝ) < (w : ℝ) := by exact_mod_cast hw
    rw [hsqrt]
    norm_num
    nlinarith
  have hbern := poisson_upper_bernstein ((n : ℝ≥0) / 4)
    (z := (n : ℝ) / 8) (by positivity)
  have hmono :
      poissonMeasure ((n : ℝ≥0) / 4) (Set.Ioi n) ≤
        poissonMeasure ((n : ℝ≥0) / 4)
          {w : ℕ | (w : ℝ) - (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) >
            Real.sqrt (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) * ((n : ℝ) / 8)) +
              2 * ((n : ℝ) / 8)} :=
    measure_mono hsubset
  simpa only [Measure.real_def, ENNReal.toReal_ofReal (Real.exp_pos _).le, neg_div] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmono.trans hbern)

/-- For [a positive sample size](hyp:hn), [a Poisson count with mean one quarter
of that size overshoots the sample size with probability at most `8 / n`](goal). -/
theorem poisson_quarter_overflow_le_inv (n : ℕ) (hn : 0 < n) :
    (poissonMeasure ((n : ℝ≥0) / 4)).real (Set.Ioi n) ≤
      8 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) / 8 := by positivity
  have hexp : (n : ℝ) / 8 ≤ Real.exp ((n : ℝ) / 8) := by
    linarith [Real.add_one_le_exp ((n : ℝ) / 8)]
  calc
    (poissonMeasure ((n : ℝ≥0) / 4)).real (Set.Ioi n) ≤
        Real.exp (-(n : ℝ) / 8) :=
      poisson_quarter_overflow_le_exp n hn
    _ = 1 / Real.exp ((n : ℝ) / 8) := by
      rw [show -(n : ℝ) / 8 = -((n : ℝ) / 8) by ring, Real.exp_neg, one_div]
    _ ≤ 1 / ((n : ℝ) / 8) :=
      one_div_le_one_div_of_le hx hexp
    _ = 8 / (n : ℝ) := by
      field_simp

end Causalean.Stat.Concentration.PoissonSelfNormalized

