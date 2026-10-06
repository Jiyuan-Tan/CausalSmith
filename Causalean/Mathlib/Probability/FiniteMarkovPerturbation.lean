module
public import Causalean.Mathlib.Probability.FiniteMarkovOscillation

/-!
# Finite Markov perturbation bounds

This module bounds finite-horizon rewards and moments when a finite initial law, transition
matrix, or reward function is perturbed in total variation or uniform distance.
-/

public section

namespace Causalean.Mathlib.Probability.FiniteMarkovPerturbation

open scoped BigOperators
open CertifiedFiniteMarkovExpectation
open FiniteMarkovOscillation

/-- A [probability-weighted mean](hyp:hp) of [values in the unit interval](hyp:hf)
[remains in the unit interval](goal). -/
lemma probability_mean_unit {S : Type*} [Fintype S]
    {p f : S → ℝ} (hp : IsProbabilityVector p)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, p i * f i) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp.1 i) (hf i).1)
  · calc
      _ ≤ ∑ i, p i * 1 := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_left (hf i).2 (hp.1 i))
      _ = 1 := by simpa using hp.2

/-- Averaging under [a probability vector](hyp:hp) cannot increase [a uniform pointwise
error](hyp:hfg), so [the two weighted means differ by at most that error](goal). -/
lemma probability_mean_error {S : Type*} [Fintype S]
    {p f g : S → ℝ} {ε : ℝ} (hp : IsProbabilityVector p)
    (hfg : ∀ i, |f i - g i| ≤ ε) :
    |(∑ i, p i * f i) - ∑ i, p i * g i| ≤ ε := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |p i * f i - p i * g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p i * ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hp.1 i)]
      exact mul_le_mul_of_nonneg_left (hfg i) (hp.1 i)
    _ = ε := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- Every [iterate count](hyp:k) of [a stochastic transition matrix](hyp:hP) sends [a
unit-range reward](hyp:hr) to [another unit-range function](goal). -/
lemma stochastic_power_reward_unit {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} (hP : IsStochasticMatrix P) {r : S → ℝ}
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (k : Nat) :
    ∀ i, ((P ^ k).mulVec r) i ∈ Set.Icc (0 : ℝ) 1 := by
  induction k with
  | zero => simpa using hr
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    intro i
    exact probability_mean_unit ⟨hP.1 i, hP.2 i⟩ ih

/-- For [two stochastic transition matrices](hyp:hP,hQ), [a unit-range reference
reward](hyp:hr), [a uniform row total-variation error](hyp:hPQ), [a uniform reward
error](hyp:hrs), and [a horizon](hyp:k), [the propagated reward error is at most the horizon
times the transition error plus the reward error](goal). -/
lemma stochastic_power_reward_error {S : Type*} [Fintype S] [DecidableEq S]
    {P Q : Matrix S S ℝ} (hP : IsStochasticMatrix P) (hQ : IsStochasticMatrix Q)
    {r s : S → ℝ} (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    {εP εr : ℝ}
    (hPQ : ∀ i, (1 / 2 : ℝ) * ∑ j, |P i j - Q i j| ≤ εP)
    (hrs : ∀ i, |r i - s i| ≤ εr) (k : Nat) :
    ∀ i, |((P ^ k).mulVec r) i - ((Q ^ k).mulVec s) i| ≤
      (k : ℝ) * εP + εr := by
  induction k with
  | zero => simpa using hrs
  | succ k ih =>
    simp only [pow_succ', ← Matrix.mulVec_mulVec]
    intro i
    letI : Nonempty S := nonemptyOfProbabilityVector (P i) ⟨hP.1 i, hP.2 i⟩
    have hunit := stochastic_power_reward_unit hP hr k
    have hosc : OscillationBound 1 ((P ^ k).mulVec r) := by
      intro x y
      rw [abs_le]
      constructor <;> linarith [(hunit x).1, (hunit x).2, (hunit y).1, (hunit y).2]
    have ht : |(∑ j, P i j * ((P ^ k).mulVec r) j) -
        ∑ j, Q i j * ((P ^ k).mulVec r) j| ≤ εP := by
      rw [← Finset.sum_sub_distrib]
      simpa only [sub_mul] using
        (abs_sum_sub_mul_le_oscillation_halfL1
          ⟨hP.1 i, hP.2 i⟩ ⟨hQ.1 i, hQ.2 i⟩ hosc).trans (by simpa using hPQ i)
    have he := probability_mean_error ⟨hQ.1 i, hQ.2 i⟩ ih
    change |(∑ j, P i j * ((P ^ k).mulVec r) j) -
      ∑ j, Q i j * ((Q ^ k).mulVec s) j| ≤ _
    calc
      _ ≤ |(∑ j, P i j * ((P ^ k).mulVec r) j) -
          ∑ j, Q i j * ((P ^ k).mulVec r) j| +
          |(∑ j, Q i j * ((P ^ k).mulVec r) j) -
          ∑ j, Q i j * ((Q ^ k).mulVec s) j| := abs_sub_le _ _ _
      _ ≤ εP + ((k : ℝ) * εP + εr) := add_le_add ht he
      _ = _ := by push_cast; ring

/-- For [two stochastic transition matrices](hyp:hP,hQ), [two probability initial
laws](hyp:hp,hq), [a unit-range reference reward](hyp:hr), [an initial-law total-variation
error](hyp:hpq), [a uniform row total-variation error](hyp:hPQ), [a uniform reward
error](hyp:hrs), and [a horizon](hyp:k), [the finite-horizon moments differ by at most the sum
of the initial, accumulated transition, and reward errors](goal). -/
lemma stochastic_moment_error {S : Type*} [Fintype S] [DecidableEq S]
    {P Q : Matrix S S ℝ} (hP : IsStochasticMatrix P) (hQ : IsStochasticMatrix Q)
    {p q r s : S → ℝ} (hp : IsProbabilityVector p) (hq : IsProbabilityVector q)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) {εν εP εr : ℝ}
    (hpq : (1 / 2 : ℝ) * ∑ i, |p i - q i| ≤ εν)
    (hPQ : ∀ i, (1 / 2 : ℝ) * ∑ j, |P i j - Q i j| ≤ εP)
    (hrs : ∀ i, |r i - s i| ≤ εr) (k : Nat) :
    |(∑ i, (Matrix.vecMul p (P ^ k)) i * r i) -
      ∑ i, (Matrix.vecMul q (Q ^ k)) i * s i| ≤ εν + (k : ℝ) * εP + εr := by
  letI : Nonempty S := nonemptyOfProbabilityVector p hp
  have hunit := stochastic_power_reward_unit hP hr k
  have hosc : OscillationBound 1 ((P ^ k).mulVec r) := by
    intro x y
    rw [abs_le]
    constructor <;> linarith [(hunit x).1, (hunit x).2, (hunit y).1, (hunit y).2]
  have ht : |(∑ i, p i * ((P ^ k).mulVec r) i) -
      ∑ i, q i * ((P ^ k).mulVec r) i| ≤ εν := by
    rw [← Finset.sum_sub_distrib]
    simpa only [sub_mul] using
      (abs_sum_sub_mul_le_oscillation_halfL1 hp hq hosc).trans (by simpa using hpq)
  have he := probability_mean_error hq (stochastic_power_reward_error hP hQ hr hPQ hrs k)
  have hdot (v f : S → ℝ) (R : Matrix S S ℝ) :
      (∑ i, (Matrix.vecMul v R) i * f i) = ∑ i, v i * (R.mulVec f) i := by
    exact Matrix.dotProduct_mulVec v R f |>.symm
  rw [hdot, hdot]
  calc
    _ ≤ |(∑ i, p i * ((P ^ k).mulVec r) i) -
        ∑ i, q i * ((P ^ k).mulVec r) i| +
        |(∑ i, q i * ((P ^ k).mulVec r) i) -
        ∑ i, q i * ((Q ^ k).mulVec s) i| := abs_sub_le _ _ _
    _ ≤ εν + ((k : ℝ) * εP + εr) := add_le_add ht he
    _ = _ := by ring

end Causalean.Mathlib.Probability.FiniteMarkovPerturbation
