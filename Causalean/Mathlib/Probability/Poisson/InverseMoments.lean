/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.Poisson.Moments
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Shifted reciprocal moments of the Poisson distribution

This module gives exact factorial-shift identities and uniform inverse-moment bounds for a
scalar Poisson count, together with two algebraic consequences used for inverse-count weights.
-/

public section

namespace Causalean.Mathlib.Probability.Poisson

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open Causalean.Mathlib.Probability.PoissonAddOnePoincare

-- @node: shifted_reciprocal_memLp_two
/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the reciprocal of one plus the
count is square-integrable](goal). -/
lemma shifted_reciprocal_memLp_two (lambda : NNReal) :
    MemLp (fun k : Nat => (((k + 1 : Nat) : Real))⁻¹) 2
      (poissonMeasure lambda) := by
  apply MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with k
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.le_add_left 1 k)

-- @node: shifted_reciprocal_pair_memLp_two
/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the reciprocal of the product of
the first two positive shifts of the count is square-integrable](goal). -/
lemma shifted_reciprocal_pair_memLp_two (lambda : NNReal) :
    MemLp (fun k : Nat =>
      ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹) 2
      (poissonMeasure lambda) := by
  apply MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards with k
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  exact inv_le_one_of_one_le₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega)))

/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the mean of the reciprocal of one
plus the count, multiplied by the rate, equals one minus the negative-rate exponential](goal).
The multiplied form includes the zero-rate law. -/
lemma shifted_reciprocal_first_moment (lambda : NNReal) :
    (lambda : Real) *
        (∫ k : Nat, (((k + 1 : Nat) : Real))⁻¹ ∂poissonMeasure lambda) =
      1 - Real.exp (-(lambda : Real)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  let p : Nat → Real := poissonWeight lambda
  let f : Nat → Real := fun k ↦ p k * (((k + 1 : Nat) : Real))⁻¹
  have hp : Summable p := (poissonWeight_hasSum_one lambda).summable
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact mul_nonneg (poissonWeight_nonneg lambda k) (inv_nonneg.mpr (by positivity))
    · intro k
      exact mul_le_of_le_one_right (poissonWeight_nonneg lambda k)
        (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.le_add_left 1 k))
    · exact hp
  have htail : (∑' k : Nat, p (k + 1)) = 1 - p 0 := by
    have hsplit := hp.sum_add_tsum_nat_add 1
    have hp1 : (∑' k : Nat, p k) = 1 :=
      (poissonWeight_hasSum_one lambda).tsum_eq
    have hh : (∑ k ∈ Finset.range 1, p k) + (∑' k : Nat, p (k + 1)) = 1 :=
      hsplit.trans hp1
    simp only [Finset.sum_range_one] at hh
    linarith
  have hterm (k : Nat) :
      (lambda : Real) * f k = p (k + 1) := by
    have hs := poissonWeight_succ_shift lambda k
    dsimp only [f]
    change (lambda : Real) * (poissonWeight lambda k *
      (((k + 1 : Nat) : Real))⁻¹) = poissonWeight lambda (k + 1)
    rw [← mul_assoc, ← hs]
    field_simp
  calc
    (lambda : Real) *
        (∑' k : Nat, Real.exp (-(lambda : Real)) *
          (lambda : Real) ^ k / Nat.factorial k *
            (((k + 1 : Nat) : Real))⁻¹) =
        (lambda : Real) * ∑' k : Nat, f k := by
          rfl
    _ = ∑' k : Nat, (lambda : Real) * f k := by rw [tsum_mul_left]
    _ = ∑' k : Nat, p (k + 1) := tsum_congr hterm
    _ = 1 - p 0 := htail
    _ = 1 - Real.exp (-(lambda : Real)) := by simp [p, poissonWeight]

/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the mean of the reciprocal of the
first two positive count shifts, multiplied by the squared rate, equals the upper tail of the
exponential series beyond degree one](goal). -/
lemma shifted_reciprocal_factorial_second_moment (lambda : NNReal) :
    (lambda : Real) ^ 2 *
        (∫ k : Nat,
          ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹
            ∂poissonMeasure lambda) =
      1 - Real.exp (-(lambda : Real)) * (1 + (lambda : Real)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  let p : Nat → Real := poissonWeight lambda
  let f : Nat → Real := fun k ↦
    p k * ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹
  have hp : Summable p := (poissonWeight_hasSum_one lambda).summable
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact mul_nonneg (poissonWeight_nonneg lambda k) (inv_nonneg.mpr (by positivity))
    · intro k
      exact mul_le_of_le_one_right (poissonWeight_nonneg lambda k)
        (inv_le_one_of_one_le₀ (by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by omega) (by omega))))
    · exact hp
  have htail : (∑' k : Nat, p (k + 2)) = 1 - p 0 - p 1 := by
    have hsplit := hp.sum_add_tsum_nat_add 2
    have hp1 : (∑' k : Nat, p k) = 1 :=
      (poissonWeight_hasSum_one lambda).tsum_eq
    have hh : (∑ k ∈ Finset.range 2, p k) + (∑' k : Nat, p (k + 2)) = 1 :=
      hsplit.trans hp1
    norm_num [Finset.sum_range_succ] at hh ⊢
    linarith
  have hterm (k : Nat) :
      (lambda : Real) ^ 2 * f k = p (k + 2) := by
    have hs1 := poissonWeight_succ_shift lambda k
    have hs2 := poissonWeight_succ_shift lambda (k + 1)
    change (lambda : Real) ^ 2 *
      (poissonWeight lambda k *
        ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹) =
      poissonWeight lambda (k + 2)
    have hprod :
        (lambda : Real) ^ 2 * poissonWeight lambda k =
          ((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
            poissonWeight lambda (k + 2) := by
      calc
        (lambda : Real) ^ 2 * poissonWeight lambda k =
            (lambda : Real) * ((lambda : Real) * poissonWeight lambda k) := by ring
        _ = (lambda : Real) *
            (((k + 1 : Nat) : Real) * poissonWeight lambda (k + 1)) := by rw [← hs1]
        _ = ((k + 1 : Nat) : Real) *
            ((lambda : Real) * poissonWeight lambda (k + 1)) := by ring
        _ = ((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
            poissonWeight lambda (k + 2) := by rw [← hs2]; ring
    rw [← mul_assoc, hprod]
    field_simp
  calc
    (lambda : Real) ^ 2 *
        (∑' k : Nat, Real.exp (-(lambda : Real)) *
          (lambda : Real) ^ k / Nat.factorial k *
            ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹) =
        (lambda : Real) ^ 2 * ∑' k : Nat, f k := by rfl
    _ = ∑' k : Nat, (lambda : Real) ^ 2 * f k := by rw [tsum_mul_left]
    _ = ∑' k : Nat, p (k + 2) := tsum_congr hterm
    _ = 1 - p 0 - p 1 := htail
    _ = 1 - Real.exp (-(lambda : Real)) * (1 + (lambda : Real)) := by
      simp [p, poissonWeight]
      ring

/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the mean squared reciprocal of one
plus the count, multiplied by the squared rate, is at most two](goal). -/
lemma shifted_reciprocal_sq_rate_bound (lambda : NNReal) :
    (lambda : Real) ^ 2 *
        (∫ k : Nat, (((k + 1 : Nat) : Real))⁻¹ ^ 2 ∂poissonMeasure lambda) ≤ 2 := by
  let f : Nat → Real := fun k ↦ (((k + 1 : Nat) : Real))⁻¹ ^ 2
  let g : Nat → Real := fun k ↦
    2 * ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹
  have hf : Integrable f (poissonMeasure lambda) := by
    refine Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable 1 ?_
    filter_upwards with k
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (inv_nonneg.mpr (by positivity))
      (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.le_add_left 1 k))
  have hg : Integrable g (poissonMeasure lambda) := by
    refine Integrable.of_bound (measurable_of_countable g).aestronglyMeasurable 2 ?_
    filter_upwards with k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (by positivity)))]
    exact mul_le_of_le_one_right (by norm_num)
      (inv_le_one_of_one_le₀ (by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by omega) (by omega))))
  have hpoint (k : Nat) : f k ≤ g k := by
    dsimp only [f, g]
    have hk1 : 0 < (((k + 1 : Nat) : Real)) := by positivity
    have hk2 : 0 < (((k + 2 : Nat) : Real)) := by positivity
    calc
      (((k + 1 : Nat) : Real))⁻¹ ^ 2 =
          1 / (((k + 1 : Nat) : Real) * ((k + 1 : Nat) : Real)) := by
            rw [one_div, inv_pow, pow_two]
      _ ≤ 2 / (((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)) := by
        apply (div_le_div_iff₀ (mul_pos hk1 hk1) (mul_pos hk1 hk2)).2
        norm_num
        nlinarith
      _ = 2 * ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹ := by
        rw [div_eq_mul_inv]
  have hint : (∫ k : Nat, f k ∂poissonMeasure lambda) ≤
      ∫ k : Nat, g k ∂poissonMeasure lambda :=
    integral_mono hf hg hpoint
  have hrate : 0 ≤ (lambda : Real) ^ 2 := sq_nonneg _
  calc
    (lambda : Real) ^ 2 *
        (∫ k : Nat, (((k + 1 : Nat) : Real))⁻¹ ^ 2 ∂poissonMeasure lambda) =
        (lambda : Real) ^ 2 * ∫ k : Nat, f k ∂poissonMeasure lambda := by rfl
    _ ≤ (lambda : Real) ^ 2 * ∫ k : Nat, g k ∂poissonMeasure lambda :=
      mul_le_mul_of_nonneg_left hint hrate
    _ = 2 * (1 - Real.exp (-(lambda : Real)) * (1 + (lambda : Real))) := by
      rw [show (∫ k : Nat, g k ∂poissonMeasure lambda) =
          2 * ∫ k : Nat,
            ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹
              ∂poissonMeasure lambda by
            dsimp only [g]
            rw [integral_const_mul]]
      calc
        (lambda : Real) ^ 2 *
            (2 * ∫ k : Nat,
              ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹
                ∂poissonMeasure lambda) =
            2 * ((lambda : Real) ^ 2 *
              ∫ k : Nat,
                ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹
                  ∂poissonMeasure lambda) := by ring
        _ = _ := by rw [shifted_reciprocal_factorial_second_moment]
    _ ≤ 2 := by
      have hnonneg : 0 ≤ Real.exp (-(lambda : Real)) * (1 + (lambda : Real)) := by
        positivity
      linarith

/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the mean squared reciprocal of one
plus the count, multiplied by one plus the rate squared, is at most eight](goal). -/
lemma shifted_reciprocal_sq_bound (lambda : NNReal) :
    (1 + (lambda : Real)) ^ 2 *
        (∫ k : Nat, (((k + 1 : Nat) : Real))⁻¹ ^ 2 ∂poissonMeasure lambda) ≤ 8 := by
  let f : Nat → Real := fun k ↦ (((k + 1 : Nat) : Real))⁻¹ ^ 2
  have hf : Integrable f (poissonMeasure lambda) := by
    refine Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable 1 ?_
    filter_upwards with k
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (inv_nonneg.mpr (by positivity))
      (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.le_add_left 1 k))
  have hf_nonneg : 0 ≤ ∫ k : Nat, f k ∂poissonMeasure lambda :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hf_le_one : (∫ k : Nat, f k ∂poissonMeasure lambda) ≤ 1 := by
    calc
      (∫ k : Nat, f k ∂poissonMeasure lambda) ≤
          ∫ _k : Nat, (1 : Real) ∂poissonMeasure lambda := by
            apply integral_mono hf (integrable_const 1)
            intro k
            exact pow_le_one₀ (inv_nonneg.mpr (by positivity))
              (inv_le_one_of_one_le₀ (by
                have h : (1 : Real) ≤ ((k + 1 : Nat) : Real) := by
                  exact_mod_cast Nat.le_add_left 1 k
                simpa only [Nat.cast_mul] using h))
      _ = 1 := by simp
  by_cases hsmall : (lambda : Real) ≤ 1
  · have hsquare : (1 + (lambda : Real)) ^ 2 ≤ 4 := by
      nlinarith [lambda.coe_nonneg]
    change (1 + (lambda : Real)) ^ 2 * (∫ k : Nat, f k ∂poissonMeasure lambda) ≤ 8
    nlinarith [mul_le_mul hsquare hf_le_one hf_nonneg (by positivity)]
  · have hone : 1 ≤ (lambda : Real) := le_of_not_ge hsmall
    have hsquare : (1 + (lambda : Real)) ^ 2 ≤ 4 * (lambda : Real) ^ 2 := by
      nlinarith
    have hrate := shifted_reciprocal_sq_rate_bound lambda
    change (1 + (lambda : Real)) ^ 2 * (∫ k : Nat, f k ∂poissonMeasure lambda) ≤ 8
    have hmul := mul_le_mul_of_nonneg_right hsquare hf_nonneg
    nlinarith

/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the mean reciprocal of the first
four positive count shifts, multiplied by the fourth power of the rate, equals the upper tail
of the exponential series beyond degree three](goal). -/
lemma shifted_reciprocal_factorial_fourth_moment (lambda : NNReal) :
    (lambda : Real) ^ 4 *
        (∫ k : Nat,
          ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
              ((k + 3 : Nat) : Real) * ((k + 4 : Nat) : Real)))⁻¹
            ∂poissonMeasure lambda) =
      1 - Real.exp (-(lambda : Real)) *
        (1 + (lambda : Real) + (lambda : Real) ^ 2 / 2 +
          (lambda : Real) ^ 3 / 6) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  let p : Nat → Real := poissonWeight lambda
  let f : Nat → Real := fun k ↦ p k *
    ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
        ((k + 3 : Nat) : Real) * ((k + 4 : Nat) : Real)))⁻¹
  have hp : Summable p := (poissonWeight_hasSum_one lambda).summable
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact mul_nonneg (poissonWeight_nonneg lambda k) (inv_nonneg.mpr (by positivity))
    · intro k
      exact mul_le_of_le_one_right (poissonWeight_nonneg lambda k)
        (inv_le_one_of_one_le₀ (by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero
              (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
              (by omega))))
    · exact hp
  have htail : (∑' k : Nat, p (k + 4)) = 1 - p 0 - p 1 - p 2 - p 3 := by
    have hsplit := hp.sum_add_tsum_nat_add 4
    have hp1 : (∑' k : Nat, p k) = 1 :=
      (poissonWeight_hasSum_one lambda).tsum_eq
    have hh : (∑ k ∈ Finset.range 4, p k) + (∑' k : Nat, p (k + 4)) = 1 :=
      hsplit.trans hp1
    norm_num [Finset.sum_range_succ] at hh ⊢
    linarith
  have hterm (k : Nat) : (lambda : Real) ^ 4 * f k = p (k + 4) := by
    have hs1 := poissonWeight_succ_shift lambda k
    have hs2 := poissonWeight_succ_shift lambda (k + 1)
    have hs3 := poissonWeight_succ_shift lambda (k + 2)
    have hs4 := poissonWeight_succ_shift lambda (k + 3)
    change (lambda : Real) ^ 4 *
      (poissonWeight lambda k *
        ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
            ((k + 3 : Nat) : Real) * ((k + 4 : Nat) : Real)))⁻¹) =
      poissonWeight lambda (k + 4)
    have hprod : (lambda : Real) ^ 4 * poissonWeight lambda k =
        ((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
          ((k + 3 : Nat) : Real) * ((k + 4 : Nat) : Real) *
            poissonWeight lambda (k + 4) := by
      calc
        (lambda : Real) ^ 4 * poissonWeight lambda k =
            (lambda : Real) ^ 3 *
              ((lambda : Real) * poissonWeight lambda k) := by ring
        _ = (lambda : Real) ^ 3 *
              (((k + 1 : Nat) : Real) * poissonWeight lambda (k + 1)) := by rw [← hs1]
        _ = ((k + 1 : Nat) : Real) * (lambda : Real) ^ 2 *
              ((lambda : Real) * poissonWeight lambda (k + 1)) := by ring
        _ = ((k + 1 : Nat) : Real) * (lambda : Real) ^ 2 *
              (((k + 2 : Nat) : Real) * poissonWeight lambda (k + 2)) := by rw [← hs2]
        _ = ((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
              (lambda : Real) *
                ((lambda : Real) * poissonWeight lambda (k + 2)) := by ring
        _ = ((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
              (lambda : Real) *
                (((k + 3 : Nat) : Real) * poissonWeight lambda (k + 3)) := by rw [← hs3]
        _ = ((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
              ((k + 3 : Nat) : Real) *
                ((lambda : Real) * poissonWeight lambda (k + 3)) := by ring
        _ = _ := by rw [← hs4]; ring
    rw [← mul_assoc, hprod]
    field_simp
  calc
    (lambda : Real) ^ 4 *
        (∑' k : Nat, Real.exp (-(lambda : Real)) *
          (lambda : Real) ^ k / Nat.factorial k *
            ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
                ((k + 3 : Nat) : Real) * ((k + 4 : Nat) : Real)))⁻¹) =
        (lambda : Real) ^ 4 * ∑' k : Nat, f k := by rfl
    _ = ∑' k : Nat, (lambda : Real) ^ 4 * f k := by rw [tsum_mul_left]
    _ = ∑' k : Nat, p (k + 4) := tsum_congr hterm
    _ = 1 - p 0 - p 1 - p 2 - p 3 := htail
    _ = 1 - Real.exp (-(lambda : Real)) *
        (1 + (lambda : Real) + (lambda : Real) ^ 2 / 2 +
          (lambda : Real) ^ 3 / 6) := by
      simp [p, poissonWeight]
      ring

/-- Under [a Poisson law with nonnegative mean](hyp:lambda), [the mean squared reciprocal of the
first two positive count shifts, multiplied by the fourth power of one plus the rate, is at
most ninety-six](goal). -/
lemma shifted_reciprocal_pair_sq_bound (lambda : NNReal) :
    (1 + (lambda : Real)) ^ 4 *
        (∫ k : Nat,
          ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹ ^ 2
            ∂poissonMeasure lambda) ≤ 96 := by
  let f : Nat → Real := fun k ↦
    ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)))⁻¹ ^ 2
  let g : Nat → Real := fun k ↦ 6 *
    ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
        ((k + 3 : Nat) : Real) * ((k + 4 : Nat) : Real)))⁻¹
  have hf : Integrable f (poissonMeasure lambda) := by
    refine Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable 1 ?_
    filter_upwards with k
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (inv_nonneg.mpr (by positivity))
      (inv_le_one_of_one_le₀ (by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by omega) (by omega))))
  have hg : Integrable g (poissonMeasure lambda) := by
    refine Integrable.of_bound (measurable_of_countable g).aestronglyMeasurable 6 ?_
    filter_upwards with k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (by positivity)))]
    exact mul_le_of_le_one_right (by norm_num)
      (inv_le_one_of_one_le₀ (by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero
            (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
            (by omega))))
  have hpoint (k : Nat) : f k ≤ g k := by
    dsimp only [f, g]
    have h1 : 0 < (((k + 1 : Nat) : Real)) := by positivity
    have h2 : 0 < (((k + 2 : Nat) : Real)) := by positivity
    have h3 : 0 < (((k + 3 : Nat) : Real)) := by positivity
    have h4 : 0 < (((k + 4 : Nat) : Real)) := by positivity
    rw [inv_pow, show 6 *
        ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
          ((k + 3 : Nat) : Real) * ((k + 4 : Nat) : Real)))⁻¹ =
        6 / (((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
          ((k + 3 : Nat) : Real) * ((k + 4 : Nat) : Real)) by
          rw [div_eq_mul_inv]]
    rw [show (((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real))) ^ 2)⁻¹ =
        1 / ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real)) ^ 2) by
          rw [one_div]]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hk : 0 ≤ (k : Real) := Nat.cast_nonneg k
    have hred : ((k : Real) + 3) * ((k : Real) + 4) ≤
        6 * ((k : Real) + 1) * ((k : Real) + 2) := by
      nlinarith [sq_nonneg (k : Real)]
    have hfront : 0 ≤ ((k : Real) + 1) * ((k : Real) + 2) := by positivity
    norm_num [Nat.cast_add] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr hred) hfront]
  have hint : (∫ k : Nat, f k ∂poissonMeasure lambda) ≤
      ∫ k : Nat, g k ∂poissonMeasure lambda := integral_mono hf hg hpoint
  have hf_nonneg : 0 ≤ ∫ k : Nat, f k ∂poissonMeasure lambda :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hf_le_one : (∫ k : Nat, f k ∂poissonMeasure lambda) ≤ 1 := by
    calc
      (∫ k : Nat, f k ∂poissonMeasure lambda) ≤
          ∫ _k : Nat, (1 : Real) ∂poissonMeasure lambda := by
            apply integral_mono hf (integrable_const 1)
            intro k
            exact pow_le_one₀ (inv_nonneg.mpr (by positivity))
              (inv_le_one_of_one_le₀ (by
                have h : (1 : Real) ≤ (((k + 1) * (k + 2) : Nat) : Real) := by
                  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
                    (Nat.mul_ne_zero (by omega) (by omega))
                simpa only [Nat.cast_mul] using h))
      _ = 1 := by simp
  by_cases hsmall : (lambda : Real) ≤ 1
  · have hsquare : (1 + (lambda : Real)) ^ 4 ≤ 16 := by
      have hbase : 0 ≤ 1 + (lambda : Real) := by positivity
      have hle : 1 + (lambda : Real) ≤ 2 := by linarith
      have hpow := pow_le_pow_left₀ hbase hle 4
      norm_num at hpow
      exact hpow
    change (1 + (lambda : Real)) ^ 4 * (∫ k : Nat, f k ∂poissonMeasure lambda) ≤ 96
    nlinarith [mul_le_mul hsquare hf_le_one hf_nonneg (by positivity)]
  · have hone : 1 ≤ (lambda : Real) := le_of_not_ge hsmall
    have hsquare : (1 + (lambda : Real)) ^ 4 ≤ 16 * (lambda : Real) ^ 4 := by
      rw [show (16 : Real) * (lambda : Real) ^ 4 =
          (2 * (lambda : Real)) ^ 4 by ring]
      exact pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hrate : (lambda : Real) ^ 4 * (∫ k : Nat, f k ∂poissonMeasure lambda) ≤ 6 := by
      calc
        (lambda : Real) ^ 4 * (∫ k : Nat, f k ∂poissonMeasure lambda) ≤
            (lambda : Real) ^ 4 * (∫ k : Nat, g k ∂poissonMeasure lambda) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
        _ = 6 * (1 - Real.exp (-(lambda : Real)) *
            (1 + (lambda : Real) + (lambda : Real) ^ 2 / 2 +
              (lambda : Real) ^ 3 / 6)) := by
          rw [show (∫ k : Nat, g k ∂poissonMeasure lambda) =
              6 * ∫ k : Nat,
                ((((k + 1 : Nat) : Real) * ((k + 2 : Nat) : Real) *
                    ((k + 3 : Nat) : Real) * ((k + 4 : Nat) : Real)))⁻¹
                  ∂poissonMeasure lambda by
                dsimp only [g]
                rw [integral_const_mul]]
          rw [← shifted_reciprocal_factorial_fourth_moment lambda]
          ring
        _ ≤ 6 := by
          have hnonneg : 0 ≤ Real.exp (-(lambda : Real)) *
              (1 + (lambda : Real) + (lambda : Real) ^ 2 / 2 +
                (lambda : Real) ^ 3 / 6) := by positivity
          linarith
    change (1 + (lambda : Real)) ^ 4 * (∫ k : Nat, f k ∂poissonMeasure lambda) ≤ 96
    have hmul := mul_le_mul_of_nonneg_right hsquare hf_nonneg
    nlinarith

-- @node: poisson_inverse_weight_second_moment_scalar
/-- The scalar estimate behind the uniform second moment of
`1 + V / (K + 1)`.  Here `lambda` and `nu` are the Poisson rates of `K` and
`V`, while `r1` and `r2` are the first and second shifted-reciprocal moments.
[Under the stated positivity, overlap, and moment bounds](hyp:heps,hlambda,hnu,hoverlap,hr1,hr1rate,_hr2,hr2rate),
[the displayed uniform second-moment bound holds](goal). -/
lemma poisson_inverse_weight_second_moment_scalar
    {eps lambda nu r1 r2 : Real}
    (heps : 0 < eps) (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (hoverlap : eps * nu ≤ lambda)
    (hr1 : 0 ≤ r1) (hr1rate : lambda * r1 ≤ 1)
    (_hr2 : 0 ≤ r2) (hr2rate : (1 + lambda) ^ 2 * r2 ≤ 8) :
    1 + 2 * nu * r1 + (nu + nu ^ 2) * r2 ≤
      1 + 10 * eps⁻¹ + 8 * eps⁻¹ ^ 2 := by
  have heps0 : 0 ≤ eps := heps.le
  have hepsinv : 0 ≤ eps⁻¹ := inv_nonneg.mpr heps0
  have hnu_r1 : nu * r1 ≤ eps⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ heps).2
    calc
      nu * r1 * eps = (eps * nu) * r1 := by ring
      _ ≤ lambda * r1 := mul_le_mul_of_nonneg_right hoverlap hr1
      _ ≤ 1 := hr1rate
  have hone : 1 ≤ 1 + lambda := by linarith
  have hsqpos : 0 < (1 + lambda) ^ 2 := sq_pos_of_pos (by linarith)
  have hr2' : r2 ≤ 8 / (1 + lambda) ^ 2 :=
    (le_div_iff₀ hsqpos).2 (by simpa [mul_comm] using hr2rate)
  have hratio : nu / (1 + lambda) ≤ eps⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ heps).2
    calc
      nu / (1 + lambda) * eps = (eps * nu) / (1 + lambda) := by ring
      _ ≤ 1 := (div_le_one (by linarith : 0 < 1 + lambda)).2 (by linarith)
  have hratio0 : 0 ≤ nu / (1 + lambda) := div_nonneg hnu (by linarith)
  have hnu_r2 : nu * r2 ≤ 8 * eps⁻¹ := by
    calc
      nu * r2 ≤ nu * (8 / (1 + lambda) ^ 2) :=
        mul_le_mul_of_nonneg_left hr2' hnu
      _ ≤ 8 * (nu / (1 + lambda)) := by
        have hden : 1 ≤ 1 + lambda := by linarith
        field_simp
        nlinarith
      _ ≤ 8 * eps⁻¹ := by gcongr
  have hnu2_r2 : nu ^ 2 * r2 ≤ 8 * eps⁻¹ ^ 2 := by
    calc
      nu ^ 2 * r2 ≤ nu ^ 2 * (8 / (1 + lambda) ^ 2) :=
        mul_le_mul_of_nonneg_left hr2' (sq_nonneg nu)
      _ = 8 * (nu / (1 + lambda)) ^ 2 := by field_simp
      _ ≤ 8 * eps⁻¹ ^ 2 := by
        gcongr
  nlinarith

-- @node: poisson_inverse_weight_poincare_energy_scalar
/-- The scalar overlap calculation for the two add-one energies of
`1 + V / (K + 1)`. It is stated in the multiplied form used after the tensorized Poisson
Poincaré inequality. [Under the stated positivity, overlap, scale, and reciprocal-moment
bounds](hyp:heps,heps1,hw,hlambda,hnu,hlower,hupper,_hr2,hr2rate,_hr4,hr4rate), [the two
add-one energies satisfy the displayed uniform estimate](goal). -/
lemma poisson_inverse_weight_poincare_energy_scalar
    {eps w lambda nu r2 r4 : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hw : 0 ≤ w) (hlambda : 0 ≤ lambda) (hnu : 0 ≤ nu)
    (hlower : eps * w ≤ lambda) (hupper : nu ≤ w)
    (_hr2 : 0 ≤ r2) (hr2rate : (1 + lambda) ^ 2 * r2 ≤ 8)
    (_hr4 : 0 ≤ r4) (hr4rate : (1 + lambda) ^ 4 * r4 ≤ 96) :
    (1 + w) * (lambda * (nu + nu ^ 2) * r4 + nu * r2) ≤
      8 * eps⁻¹ ^ 2 + 96 * (eps⁻¹ ^ 2 + eps⁻¹ ^ 3) := by
  have heps0 : 0 ≤ eps := heps.le
  have hepsinv : 0 ≤ eps⁻¹ := inv_nonneg.mpr heps0
  have hscale : eps * (1 + w) ≤ 1 + lambda := by nlinarith
  have hnu_lambda : eps * nu ≤ lambda := by nlinarith
  have hden : 0 < 1 + lambda := by linarith
  have hsq : 0 < (1 + lambda) ^ 2 := sq_pos_of_pos hden
  have hfour : 0 < (1 + lambda) ^ 4 := pow_pos hden 4
  have hr2' : r2 ≤ 8 / (1 + lambda) ^ 2 :=
    (le_div_iff₀ hsq).2 (by simpa [mul_comm] using hr2rate)
  have hr4' : r4 ≤ 96 / (1 + lambda) ^ 4 :=
    (le_div_iff₀ hfour).2 (by simpa [mul_comm] using hr4rate)
  have hratioNu : nu / (1 + lambda) ≤ eps⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ heps).2
    calc
      nu / (1 + lambda) * eps = (eps * nu) / (1 + lambda) := by ring
      _ ≤ 1 := (div_le_one hden).2 (by linarith)
  have hratioScale : (1 + w) / (1 + lambda) ≤ eps⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ heps).2
    calc
      (1 + w) / (1 + lambda) * eps =
          (eps * (1 + w)) / (1 + lambda) := by ring
      _ ≤ 1 := (div_le_one hden).2 hscale
  have hratioLambda : lambda / (1 + lambda) ≤ 1 := by
    exact (div_le_one hden).2 (by linarith)
  have hsmall : (1 + w) * (nu * r2) ≤ 8 * eps⁻¹ ^ 2 := by
    calc
      (1 + w) * (nu * r2) ≤
          (1 + w) * (nu * (8 / (1 + lambda) ^ 2)) := by
            gcongr
      _ = 8 * ((1 + w) / (1 + lambda)) *
          (nu / (1 + lambda)) := by field_simp
      _ ≤ 8 * eps⁻¹ * eps⁻¹ := by gcongr
      _ = 8 * eps⁻¹ ^ 2 := by ring
  have hlarge : (1 + w) * (lambda * (nu + nu ^ 2) * r4) ≤
      96 * (eps⁻¹ ^ 2 + eps⁻¹ ^ 3) := by
    have hratioNuSq : nu / (1 + lambda) ^ 2 ≤ eps⁻¹ := by
      calc
        nu / (1 + lambda) ^ 2 ≤ nu / (1 + lambda) := by
          apply div_le_div_of_nonneg_left hnu hden
          nlinarith [sq_nonneg lambda]
        _ ≤ eps⁻¹ := hratioNu
    calc
      (1 + w) * (lambda * (nu + nu ^ 2) * r4) ≤
          (1 + w) * (lambda * (nu + nu ^ 2) *
            (96 / (1 + lambda) ^ 4)) := by gcongr
      _ = 96 * ((1 + w) / (1 + lambda)) *
          (lambda / (1 + lambda)) *
          ((nu / (1 + lambda) ^ 2) +
            (nu / (1 + lambda)) ^ 2) := by field_simp
      _ ≤ 96 * eps⁻¹ * 1 * (eps⁻¹ + eps⁻¹ ^ 2) := by gcongr
      _ = 96 * (eps⁻¹ ^ 2 + eps⁻¹ ^ 3) := by ring
  nlinarith

end Causalean.Mathlib.Probability.Poisson
