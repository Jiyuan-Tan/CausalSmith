import Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.FiniteKernel

/-!
# Finite Markov operators and oscillation contraction

This module provides the backward action of a finite stochastic matrix on functions and the
duality between total-variation contraction of distributions and oscillation contraction of
functions. It reuses the finite probability vectors and forward Markov steps from
`CertifiedFiniteMarkovExpectation.FiniteKernel`.
-/

namespace Causalean.Mathlib.Probability.FiniteMarkovOscillation

open scoped BigOperators
open CertifiedFiniteMarkovExpectation

/-- Given [a finite transition matrix](hyp:P), [a real-valued function](hyp:f), and [a starting
state](hyp:s), [the backward Markov operator is the transition-weighted sum of the function](goal). -/
noncomputable def markovOperator {S : Type*} [Fintype S]
    (P : S → S → ℝ) (f : S → ℝ) (s : S) : ℝ :=
  ∑ s', P s s' * f s'

/-- Given [a finite transition matrix](hyp:P), [the iterated backward Markov operator](goal)
applies the matrix a specified number of times to a real-valued function. -/
noncomputable def markovOperatorIter {S : Type*} [Fintype S]
    (P : S → S → ℝ) : Nat → (S → ℝ) → S → ℝ
  | 0, f => f
  | n + 1, f => markovOperator P (markovOperatorIter P n f)

/-- For [a finite transition matrix](hyp:P), [a step count](hyp:n), and [a function](hyp:f),
[the successor iterate is one backward Markov step after the preceding iterate](goal). -/
lemma markovOperatorIter_succ {S : Type*} [Fintype S]
    (P : S → S → ℝ) (n : Nat) (f : S → ℝ) :
    markovOperatorIter P (n + 1) f =
      markovOperator P (markovOperatorIter P n f) := rfl

/-- Given [an upper bound](hyp:B) and [a real-valued function](hyp:f), [the function has
pairwise oscillation at most that bound](goal) when every two values differ by at most it. -/
def OscillationBound {S : Type*} (B : ℝ) (f : S → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ B

/-- If [a function has an oscillation bound](hyp:h), [that bound is nonnegative](goal). -/
lemma oscillationBound_nonneg {S : Type*} [Nonempty S] {B : ℝ} {f : S → ℝ}
    (h : OscillationBound B f) : 0 ≤ B := by
  let x : S := Classical.choice inferInstance
  simpa using h x x

/-- Given [two finite probability vectors](hyp:hp,hq) and [a function with oscillation at most
`B`](hyp:hf), [the difference of their expectations is at most `B` times half their ℓ¹
distance](goal). -/
lemma abs_sum_sub_mul_le_oscillation_halfL1 {S : Type*} [Fintype S] [Nonempty S]
    {p q : S → ℝ} (hp : IsProbabilityVector p) (hq : IsProbabilityVector q)
    {B : ℝ} {f : S → ℝ} (hf : OscillationBound B f) :
    |∑ s, (p s - q s) * f s| ≤ B * ((1 / 2 : ℝ) * ∑ s, |p s - q s|) := by
  obtain ⟨imin, -, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  obtain ⟨imax, -, hmax⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hB0 := oscillationBound_nonneg hf
  have hspan : f imax - f imin ≤ B := by
    have := hf imax imin
    exact (le_abs_self (f imax - f imin)).trans this
  let c : ℝ := (f imin + f imax) / 2
  have hcenter (s : S) : |f s - c| ≤ B / 2 := by
    have hlo : f imin ≤ f s := hmin s (Finset.mem_univ s)
    have hhi : f s ≤ f imax := hmax s (Finset.mem_univ s)
    rw [abs_le]
    constructor <;> dsimp [c] <;> linarith
  have hsum0 : ∑ s, (p s - q s) = 0 := by
    rw [Finset.sum_sub_distrib, hp.2, hq.2, sub_self]
  calc
    |∑ s, (p s - q s) * f s| =
        |∑ s, (p s - q s) * (f s - c)| := by
      congr 1
      rw [show (∑ s, (p s - q s) * (f s - c)) =
          (∑ s, (p s - q s) * f s) - (∑ s, (p s - q s)) * c by
        calc
          _ = ∑ s, ((p s - q s) * f s - (p s - q s) * c) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = (∑ s, (p s - q s) * f s) - ∑ s, (p s - q s) * c := by
            rw [Finset.sum_sub_distrib]
          _ = _ := by rw [← Finset.sum_mul]]
      rw [hsum0, zero_mul, sub_zero]
    _ ≤ ∑ s, |(p s - q s) * (f s - c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, |p s - q s| * (B / 2) := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcenter s) (abs_nonneg _)
    _ = B * ((1 / 2 : ℝ) * ∑ s, |p s - q s|) := by
      simp only [← Finset.sum_mul]
      ring

/-- For [a state](hyp:x), [its point mass is a finite probability vector](goal). -/
lemma isProbabilityVector_indicator {S : Type*} [Fintype S] [DecidableEq S] (x : S) :
    IsProbabilityVector (fun y : S ↦ if y = x then 1 else 0) := by
  constructor
  · intro y
    by_cases hy : y = x <;> simp [hy]
  · simp

/-- For [two states](hyp:x,y), [half the ℓ¹ distance between their point masses is at most
one](goal). -/
lemma halfL1_indicator_sub_indicator_le_one {S : Type*} [Fintype S] [DecidableEq S]
    (x y : S) :
    (1 / 2 : ℝ) * ∑ z,
      |(if z = x then 1 else 0) - (if z = y then 1 else 0)| ≤ 1 := by
  let px : S → ℝ := fun z ↦ if z = x then 1 else 0
  let py : S → ℝ := fun z ↦ if z = y then 1 else 0
  have hpoint (z : S) : |px z - py z| ≤ px z + py z := by
    calc
      _ ≤ |px z| + |py z| := abs_sub _ _
      _ = _ := by
        rw [abs_of_nonneg, abs_of_nonneg]
        · by_cases hz : z = y <;> simp [py, hz]
        · by_cases hz : z = x <;> simp [px, hz]
  change (1 / 2 : ℝ) * ∑ z, |px z - py z| ≤ 1
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ z, (px z + py z) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun z _ ↦ hpoint z
    _ = 1 := by
      rw [Finset.sum_add_distrib]
      have hx : ∑ z, px z = 1 := by
        simpa [px] using (isProbabilityVector_indicator x).2
      have hy : ∑ z, py z = 1 := by
        simpa [py] using (isProbabilityVector_indicator y).2
      rw [hx, hy]
      norm_num

/-- Given [a finite stochastic matrix](hyp:hP), [a nonnegative contraction coefficient](hyp:halpha),
[half-ℓ¹ contraction of its forward action](hyp:hcontract), and [a function with oscillation at
most `B`](hyp:hf), [one backward Markov step has oscillation at most `alpha * B`](goal). -/
lemma oscillationBound_markovOperator {S : Type*} [Fintype S] [Nonempty S]
    (P : S → S → ℝ) (hP : ∀ s, IsProbabilityVector (P s))
    {alpha B : ℝ} (halpha : 0 ≤ alpha)
    (hcontract : ∀ p q, IsProbabilityVector p → IsProbabilityVector q →
      (1 / 2 : ℝ) * ∑ s, |markovStep p P s - markovStep q P s| ≤
        alpha * ((1 / 2 : ℝ) * ∑ s, |p s - q s|))
    {f : S → ℝ} (hf : OscillationBound B f) :
    OscillationBound (alpha * B) (markovOperator P f) := by
  classical
  intro x y
  let px : S → ℝ := fun z ↦ if z = x then 1 else 0
  let py : S → ℝ := fun z ↦ if z = y then 1 else 0
  have hpx : IsProbabilityVector px := isProbabilityVector_indicator x
  have hpy : IsProbabilityVector py := isProbabilityVector_indicator y
  have happx : markovStep px P = P x := by
    funext z
    simp [markovStep, Matrix.vecMul, dotProduct, px]
  have happy : markovStep py P = P y := by
    funext z
    simp [markovStep, Matrix.vecMul, dotProduct, py]
  have htv : (1 / 2 : ℝ) * ∑ s, |P x s - P y s| ≤ alpha := by
    have hc := hcontract px py hpx hpy
    rw [happx, happy] at hc
    exact hc.trans (by
      simpa [px, py] using mul_le_mul_of_nonneg_left
        (halfL1_indicator_sub_indicator_le_one x y) halpha)
  have hdual := abs_sum_sub_mul_le_oscillation_halfL1 (hP x) (hP y) hf
  unfold markovOperator
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ s, (P x s * f s - P y s * f s)| =
        |∑ s, (P x s - P y s) * f s| := by
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ B * ((1 / 2 : ℝ) * ∑ s, |P x s - P y s|) := hdual
    _ ≤ B * alpha := mul_le_mul_of_nonneg_left htv (oscillationBound_nonneg hf)
    _ = alpha * B := mul_comm _ _

/-- Given [a finite stochastic matrix](hyp:hP), [a nonnegative contraction coefficient](hyp:halpha),
[half-ℓ¹ contraction of its forward action](hyp:hcontract), [an initial oscillation bound](hyp:hf),
and [a number of steps](hyp:n), [the iterated backward operator's oscillation is bounded by the coefficient raised to the
number of steps times the initial bound](goal), which decays geometrically when the coefficient is
below one. -/
lemma oscillationBound_markovOperatorIter {S : Type*} [Fintype S] [Nonempty S]
    (P : S → S → ℝ) (hP : ∀ s, IsProbabilityVector (P s))
    {alpha B : ℝ} (halpha : 0 ≤ alpha)
    (hcontract : ∀ p q, IsProbabilityVector p → IsProbabilityVector q →
      (1 / 2 : ℝ) * ∑ s, |markovStep p P s - markovStep q P s| ≤
        alpha * ((1 / 2 : ℝ) * ∑ s, |p s - q s|))
    {f : S → ℝ} (hf : OscillationBound B f) (n : Nat) :
    OscillationBound (alpha ^ n * B) (markovOperatorIter P n f) := by
  induction n with
  | zero => simpa [markovOperatorIter] using hf
  | succ n ih =>
      simpa [markovOperatorIter, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        oscillationBound_markovOperator P hP halpha hcontract ih

/-- If [a function has oscillation at most `A`](hyp:hf) and [`A` is at most `B`](hyp:hAB),
[the function has oscillation at most `B`](goal). -/
lemma OscillationBound.mono {S : Type*} {A B : ℝ} {f : S → ℝ}
    (hf : OscillationBound A f) (hAB : A ≤ B) : OscillationBound B f :=
  fun x y ↦ (hf x y).trans hAB

/-- Given [a real vector on a finite carrier](hyp:p) that [is a probability vector](hyp:hp),
[the carrier is nonempty](goal). -/
noncomputable def nonemptyOfProbabilityVector {S : Type*} [Fintype S]
    (p : S → ℝ) (hp : IsProbabilityVector p) : Nonempty S := by
  classical
  by_contra hempty
  haveI : IsEmpty S := not_nonempty_iff.mp hempty
  have := hp.2
  simpa using this

end Causalean.Mathlib.Probability.FiniteMarkovOscillation
