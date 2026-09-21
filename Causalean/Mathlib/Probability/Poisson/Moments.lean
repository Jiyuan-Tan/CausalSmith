/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.Poisson.Poincare.Series
public import Mathlib.Probability.Moments.Basic

/-!
# Scalar moments of the Poisson distribution

This module records square-integrability and exact first and exponential moments for the
natural-valued coordinate under a scalar Poisson law.
-/

public section

namespace Causalean.Mathlib.Probability.Poisson

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.PoissonAddOnePoincare

/-- For [a Poisson law with nonnegative mean](hyp:lambda) and [a real tilt](hyp:theta),
[the exponential of the natural-valued count is integrable](goal). -/
lemma integrable_exp_natCast_poisson (lambda : NNReal) (theta : Real) :
    Integrable (fun w : Nat ↦ Real.exp (theta * (w : Real)))
      (poissonMeasure lambda) := by
  rw [integrable_poissonMeasure_iff]
  have hs := Real.summable_pow_div_factorial
    ((lambda : Real) * Real.exp theta)
  apply (hs.mul_left (Real.exp (-(lambda : Real)))).congr
  intro w
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [show Real.exp (theta * (w : Real)) = (Real.exp theta) ^ w by
    rw [mul_comm, Real.exp_nat_mul]]
  ring

-- @node: poisson_natCast_memLp_two
/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the natural-valued
count is square-integrable](goal). -/
lemma poisson_natCast_memLp_two (lambda : NNReal) :
    MemLp (fun k : Nat => (k : Real)) 2 (poissonMeasure lambda) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_of_countable fun k : Nat => (k : Real)).aestronglyMeasurable).2
  have hexp := integrable_exp_natCast_poisson lambda 2
  apply hexp.mono
    (measurable_of_countable fun k : Nat => (k : Real) ^ 2).aestronglyMeasurable
  filter_upwards with k
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (k : Real))]
  have hk : (0 : Real) ≤ k := by positivity
  have hlin : (k : Real) ≤ Real.exp (k : Real) := by
    calc
      (k : Real) ≤ 1 + (k : Real) := by linarith
      _ ≤ Real.exp (k : Real) := by simpa [add_comm] using Real.add_one_le_exp (k : Real)
  have hsq : (k : Real) ^ 2 ≤ Real.exp (2 * (k : Real)) := by
    calc
      (k : Real) ^ 2 ≤ Real.exp (k : Real) ^ 2 :=
        pow_le_pow_left₀ hk hlin 2
      _ = Real.exp (2 * (k : Real)) := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hsq

-- @node: poisson_natCast_first_moment
/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the expected natural-valued
count equals its mean parameter](goal). -/
lemma poisson_natCast_first_moment (lambda : NNReal) :
    (∫ k : Nat, (k : Real) ∂poissonMeasure lambda) = (lambda : Real) := by
  have hk : Integrable (fun k : Nat ↦ (k : Real)) (poissonMeasure lambda) :=
    (poisson_natCast_memLp_two lambda).integrable (by norm_num)
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  let p : Nat → Real := poissonWeight lambda
  have hp : Summable p := (poissonWeight_hasSum_one lambda).summable
  let g : Nat → Real := fun k ↦ Real.exp (-(lambda : Real)) *
    (lambda : Real) ^ k / Nat.factorial k * (k : Real)
  have hg : Summable g := by
    exact (hasSum_integral_poissonMeasure hk).summable
  have hsplit := hg.sum_add_tsum_nat_add 1
  calc
    (∑' k : Nat, Real.exp (-(lambda : Real)) * (lambda : Real) ^ k /
        Nat.factorial k * (k : Real)) =
        ∑' k : Nat, Real.exp (-(lambda : Real)) * (lambda : Real) ^ (k + 1) /
        Nat.factorial (k + 1) * ((k + 1 : Nat) : Real) := by
          simpa [g] using hsplit.symm
    _ =
        ∑' k : Nat, (lambda : Real) * p k := by
          apply tsum_congr
          intro k
          simp only [p, poissonWeight, Nat.factorial_succ, Nat.cast_mul,
            Nat.cast_add, Nat.cast_one]
          field_simp
          ring
    _ = (lambda : Real) * ∑' k : Nat, p k := by rw [tsum_mul_left]
    _ = (lambda : Real) := by rw [(poissonWeight_hasSum_one lambda).tsum_eq, mul_one]

/-- For [a Poisson law with nonnegative mean](hyp:lambda) and [a real tilt](hyp:theta),
[the moment-generating function of the natural-valued count is the exponential of the mean
times the exponential remainder](goal). -/
lemma mgf_natCast_poisson (lambda : NNReal) (theta : Real) :
    mgf (fun w : Nat ↦ (w : Real)) (poissonMeasure lambda) theta =
      Real.exp ((lambda : Real) * (Real.exp theta - 1)) := by
  rw [mgf, integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    ∑' w : Nat, Real.exp (-(lambda : Real)) * (lambda : Real) ^ w /
          Nat.factorial w * Real.exp (theta * (w : Real)) =
        Real.exp (-(lambda : Real)) *
          ∑' w : Nat, (((lambda : Real) * Real.exp theta) ^ w /
            Nat.factorial w) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro w
      rw [show Real.exp (theta * (w : Real)) = (Real.exp theta) ^ w by
        rw [mul_comm, Real.exp_nat_mul]]
      ring
    _ = Real.exp (-(lambda : Real)) *
          Real.exp ((lambda : Real) * Real.exp theta) := by
      have hseries := (NormedSpace.expSeries_div_hasSum_exp
        ((lambda : Real) * Real.exp theta)).tsum_eq
      rw [← Real.exp_eq_exp_ℝ] at hseries
      rw [hseries]
    _ = Real.exp ((lambda : Real) * (Real.exp theta - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Causalean.Mathlib.Probability.Poisson
