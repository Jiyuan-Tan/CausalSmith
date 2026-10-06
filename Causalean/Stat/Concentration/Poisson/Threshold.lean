/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.Poisson.Moments
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Chernoff

/-!
# Scalar Poisson threshold bounds

This module derives fixed-fraction lower-tail and exponentially weighted upper-tail estimates
for a scalar Poisson count from exact exponential moments and Chernoff inequalities.
-/

public section

namespace Causalean.Stat.Concentration.Poisson

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal MeasureTheory
open Causalean.Mathlib.Probability.Poisson

/-- For [a Poisson law with nonnegative mean and a natural cutoff](hyp:lambda,k), if
[the cutoff is below one quarter of the mean](hyp:hk), [the lower-tail probability is at most
the exponential of minus one quarter of that mean](goal). -/
lemma poisson_le_cutoff_of_cutoff_lt_quarter (lambda : NNReal) (k : Nat)
    (hk : (k : Real) < (lambda : Real) / 4) :
    poissonMeasure lambda {w : Nat | w ≤ k} ≤
      ENNReal.ofReal (Real.exp (-(lambda : Real) / 4)) := by
  have hlambda : 0 < (lambda : Real) := by
    have hk0 : 0 ≤ (k : Real) := Nat.cast_nonneg k
    linarith
  have hz : 0 ≤ (lambda : Real) / 4 := by positivity
  have hsqrt_sq :
      (Real.sqrt (2 * (lambda : Real) * ((lambda : Real) / 4))) ^ 2 =
        (lambda : Real) ^ 2 / 2 := by
    rw [Real.sq_sqrt]
    · ring
    · positivity
  have hsqrt_lt :
      Real.sqrt (2 * (lambda : Real) * ((lambda : Real) / 4)) <
        3 * (lambda : Real) / 4 := by
    have hsqrt0 := Real.sqrt_nonneg
      (2 * (lambda : Real) * ((lambda : Real) / 4))
    nlinarith [sq_nonneg ((lambda : Real) / 4)]
  have hsubset :
      {w : Nat | w ≤ k} ⊆
        {w : Nat | (lambda : Real) - (w : Real) >
          Real.sqrt (2 * (lambda : Real) * ((lambda : Real) / 4))} := by
    intro w hw
    change w ≤ k at hw
    have hwk : (w : Real) ≤ (k : Real) := by exact_mod_cast hw
    change (lambda : Real) - (w : Real) > _
    linarith
  refine (measure_mono hsubset).trans ?_
  simpa only [neg_div] using
    (Causalean.Stat.Concentration.PoissonSelfNormalized.poisson_lower_bernstein
      lambda hz)

/-- For [a Poisson law with nonnegative mean, a natural cutoff, and a real exponential
weight](hyp:lambda,k,r), if [the weight is nonnegative](hyp:hr), [the strict upper-tail
probability times its exponential penalty is bounded by the logarithmic cutoff factor](goal). -/
lemma poisson_upper_tail_mul_exp_le (lambda : NNReal) (k : Nat) {r : Real}
    (hr : 0 ≤ r) :
    (poissonMeasure lambda).real {w : Nat | k < w} *
        Real.exp (-r * (lambda : Real)) ≤
      Real.exp (-Real.log (1 + r) * (k : Real)) := by
  let theta := Real.log (1 + r)
  have hone : 0 < 1 + r := by linarith
  have htheta : 0 ≤ theta := by
    dsimp [theta]
    exact Real.log_nonneg (by linarith)
  have hchernoff := measure_ge_le_exp_mul_mgf
    (X := fun w : Nat ↦ (w : Real)) (μ := poissonMeasure lambda)
    (k : Real) htheta (integrable_exp_natCast_poisson lambda theta)
  rw [mgf_natCast_poisson] at hchernoff
  have hexp : Real.exp theta = 1 + r := by
    dsimp [theta]
    exact Real.exp_log hone
  have hsubset : {w : Nat | k < w} ⊆ {w : Nat | (k : Real) ≤ (w : Real)} := by
    intro w hw
    exact_mod_cast (Nat.le_of_lt hw)
  have hprob : (poissonMeasure lambda).real {w : Nat | k < w} ≤
      Real.exp (-theta * (k : Real)) *
        Real.exp ((lambda : Real) * r) := by
    calc
      _ ≤ (poissonMeasure lambda).real
          {w : Nat | (k : Real) ≤ (w : Real)} :=
        MeasureTheory.measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ _ := by simpa [hexp] using hchernoff
  calc
    _ ≤ (Real.exp (-theta * (k : Real)) *
          Real.exp ((lambda : Real) * r)) *
        Real.exp (-r * (lambda : Real)) := by
      gcongr
    _ = Real.exp (-Real.log (1 + r) * (k : Real)) := by
      dsimp [theta]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- For [a real number and a natural exponent](hyp:r,k), if [the real number is
nonnegative](hyp:hr), [the exponential of the negative logarithmic multiple equals the
reciprocal natural power](goal). -/
lemma exp_neg_log_mul_nat_eq_inv_pow {r : Real} (hr : 0 ≤ r) (k : Nat) :
    Real.exp (-Real.log (1 + r) * (k : Real)) = ((1 + r) ^ k)⁻¹ := by
  have hone : 0 < 1 + r := by linarith
  rw [show -Real.log (1 + r) * (k : Real) =
      -((k : Real) * Real.log (1 + r)) by ring,
    Real.exp_neg, Real.exp_nat_mul, Real.exp_log hone]

end Causalean.Stat.Concentration.Poisson


namespace Causalean.Stat.Concentration.Poisson

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal MeasureTheory

/-- For a [positive requested count](hyp:n,hn) and a [Poisson mean at least twice
that count](hyp:lambda,hlambda), the probability of falling below the requested
count is at most `8 / n`. The result is [the `8 / n` Poisson lower-tail bound](goal). -/
lemma poisson_lower_tail_of_two_mul_le (n : ℕ) (lambda : ℝ≥0)
    (hn : 1 ≤ n) (hlambda : (2 : ℝ) * n ≤ lambda) :
    (poissonMeasure lambda (Set.Iio n)).toReal ≤ 8 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlambdaR : (2 : ℝ) * n ≤ (lambda : ℝ) := by exact hlambda
  have hlambdaPos : (0 : ℝ) < lambda := lt_of_lt_of_le (by positivity) hlambdaR
  have hsqrt : Real.sqrt (2 * (lambda : ℝ) * ((n : ℝ) / 8)) ≤
      (lambda : ℝ) / 2 := by
    rw [show 2 * (lambda : ℝ) * ((n : ℝ) / 8) =
      (lambda : ℝ) * (n : ℝ) / 4 by ring]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ lambda by positivity)
        (sub_nonneg.mpr (show (n : ℝ) ≤ lambda by linarith))]
  have hsubset : Set.Iio n ⊆
      {w : ℕ | (lambda : ℝ) - (w : ℝ) >
        Real.sqrt (2 * (lambda : ℝ) * ((n : ℝ) / 8))} := by
    intro w hw
    have hwNat : w < n := hw
    have hwR : (w : ℝ) < n := by exact_mod_cast hwNat
    have : (lambda : ℝ) / 2 ≤ (lambda : ℝ) - (n : ℝ) := by linarith
    exact lt_of_le_of_lt hsqrt (lt_of_le_of_lt this (by linarith))
  have hbern :=
    Causalean.Stat.Concentration.PoissonSelfNormalized.poisson_lower_bernstein
      lambda (z := (n : ℝ) / 8) (by positivity)
  have hreal : (poissonMeasure lambda (Set.Iio n)).toReal ≤
      Real.exp (-(n : ℝ) / 8) := by
    calc
      _ ≤ (ENNReal.ofReal (Real.exp (-(n : ℝ) / 8))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          ((measure_mono hsubset).trans (by simpa [neg_div] using hbern))
      _ = _ := ENNReal.toReal_ofReal (Real.exp_nonneg _)
  calc
    _ ≤ Real.exp (-(n : ℝ) / 8) := hreal
    _ = 1 / Real.exp ((n : ℝ) / 8) := by
      rw [show -(n : ℝ) / 8 = -((n : ℝ) / 8) by ring, Real.exp_neg, one_div]
    _ ≤ 1 / ((n : ℝ) / 8) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith [Real.add_one_le_exp ((n : ℝ) / 8)]
    _ = 8 / (n : ℝ) := by field_simp

/-- For a [Poisson rate](hyp:rate) and [real threshold](hyp:B), the probability of
the count being at most one quarter of the threshold obeys the stated
exponential lower-tail bound. The result is [the exponential Poisson lower-tail bound at one quarter of the threshold](goal). -/
lemma poisson_pilot_lower_tail (rate : NNReal) (B : ℝ) :
    (poissonMeasure rate).real {k : ℕ | (k : ℝ) ≤ B / 4} ≤
      Real.exp (B * Real.log 4 / 4 - 3 * (rate : ℝ) / 4) := by
  let theta : ℝ := -Real.log 4
  have hlog : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have htheta : theta ≤ 0 := by dsimp [theta]; linarith
  have hchernoff := measure_le_le_exp_mul_mgf
    (X := fun k : ℕ => (k : ℝ)) (μ := poissonMeasure rate)
    (B / 4) htheta
    (Causalean.Mathlib.Probability.Poisson.integrable_exp_natCast_poisson rate theta)
  rw [Causalean.Mathlib.Probability.Poisson.mgf_natCast_poisson] at hchernoff
  have hexp : Real.exp theta = 1 / 4 := by
    dsimp [theta]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  calc
    (poissonMeasure rate).real {k : ℕ | (k : ℝ) ≤ B / 4} ≤
        Real.exp (-theta * (B / 4)) *
          Real.exp ((rate : ℝ) * (Real.exp theta - 1)) := hchernoff
    _ = Real.exp (B * Real.log 4 / 4 - 3 * (rate : ℝ) / 4) := by
      rw [hexp, ← Real.exp_add]
      dsimp [theta]
      congr 1
      ring


/-- For a [Poisson rate](hyp:rate) and [real threshold](hyp:B), the probability of
the count exceeding one quarter of the threshold obeys the stated exponential
upper-tail bound. The result is [the exponential Poisson upper-tail bound at one quarter of the threshold](goal). -/
lemma poisson_pilot_upper_tail (rate : NNReal) (B : ℝ) :
    (poissonMeasure rate).real {k : ℕ | B / 4 < (k : ℝ)} ≤
      Real.exp (3 * (rate : ℝ) - B * Real.log 4 / 4) := by
  let theta : ℝ := Real.log 4
  have htheta : 0 ≤ theta := by
    dsimp [theta]
    exact (Real.log_pos (by norm_num)).le
  have hchernoff := measure_ge_le_exp_mul_mgf
    (X := fun k : ℕ => (k : ℝ)) (μ := poissonMeasure rate)
    (B / 4) htheta
    (Causalean.Mathlib.Probability.Poisson.integrable_exp_natCast_poisson rate theta)
  rw [Causalean.Mathlib.Probability.Poisson.mgf_natCast_poisson] at hchernoff
  have hexp : Real.exp theta = 4 := by
    dsimp [theta]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have hsubset : {k : ℕ | B / 4 < (k : ℝ)} ⊆
      {k : ℕ | B / 4 ≤ (k : ℝ)} := by
    intro k hk
    change B / 4 < (k : ℝ) at hk
    change B / 4 ≤ (k : ℝ)
    exact hk.le
  calc
    (poissonMeasure rate).real {k : ℕ | B / 4 < (k : ℝ)} ≤
        (poissonMeasure rate).real {k : ℕ | B / 4 ≤ (k : ℝ)} :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ Real.exp (-theta * (B / 4)) *
        Real.exp ((rate : ℝ) * (Real.exp theta - 1)) := hchernoff
    _ = Real.exp (3 * (rate : ℝ) - B * Real.log 4 / 4) := by
      rw [hexp, ← Real.exp_add]
      dsimp [theta]
      congr 1
      ring

end Causalean.Stat.Concentration.Poisson
