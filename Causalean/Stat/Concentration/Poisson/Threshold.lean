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
