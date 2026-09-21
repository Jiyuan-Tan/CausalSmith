/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.SequentialSampling
public import Causalean.Stat.CLT.Martingale.Main

/-!
# Finite-population CLT under the Li–Ding maximal-deviation condition

This module develops an explicit reveal martingale for a simple random sample without replacement.
Its first layer identifies each martingale increment
as a deterministic coefficient times the next draw centered by its remaining-population mean.
The asymptotic layer controls those increments and their predictable quadratic variation under
the convenient Li–Ding maximal-deviation sufficient condition, then transports the Gaussian limit
from ordered permutations to the library's complete-randomization design.  It does not formalize
Hájek's weaker necessary-and-sufficient Lindeberg criterion.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators Topology

namespace Causalean.Experimentation.DesignBased
open Causalean.Stat

open FinitePopulationMoments
open Filter ProbabilityTheory

/-- Given [a population size](hyp:N), [a proper positive sample size](hyp:K,hKpos,hKlt), and
[a reveal time](hyp:k), the [Hájek coefficient](goal) multiplying the centered next draw is
`(N-K)/(K(N-k-1))`. -/
noncomputable def hajekIncrementCoefficient
    (N K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (k : ℕ) : ℝ :=
  ((N - K : ℕ) : ℝ) / ((K : ℝ) * ((N - k - 1 : ℕ) : ℝ))

/-- Given [a population size](hyp:N), [a proper positive sample size](hyp:K,hKpos,hKlt),
[population outcomes](hyp:y), [an active reveal time](hyp:k,hk), and [an ordering](hyp:π), the
[Hájek reveal increment](goal) is `(N-K)/(K(N-k-1))` times the next outcome minus its
prefix-conditional remaining-population mean. -/
noncomputable def permutationHajekIncrement
    {N : ℕ} (K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (y : Fin N → ℝ)
    (k : ℕ) (hk : k < K) (π : PermutationSampleSpace N) : ℝ :=
  hajekIncrementCoefficient N K hKpos hKlt k *
    (permutationDraw y k (hk.trans hKlt) π -
      permutationNextMean y k (hk.trans hKlt) π)

/-- For [population outcomes](hyp:y), [a reveal time](hyp:k), [feasibility of the next
prefix](hyp:hk), and [an ordering](hyp:π), [revealing the next position adds exactly its draw to
the revealed sum](goal). -/
lemma permutationRevealedSum_succ {N : ℕ} (y : Fin N → ℝ) (k : ℕ)
    (hk : k + 1 ≤ N) (π : PermutationSampleSpace N) :
    permutationRevealedSum y (k + 1) hk π =
      permutationRevealedSum y k (Nat.le_trans (Nat.le_succ k) hk) π +
        permutationDraw y k (lt_of_lt_of_le (Nat.lt_succ_self k) hk) π := by
  unfold permutationRevealedSum permutationDraw
  rw [Fin.sum_univ_castSucc]
  rfl

/-- Given [a proper positive sample size](hyp:K,hKpos,hKlt), [population outcomes](hyp:y),
[a feasible reveal time](hyp:k,hk), and [an ordering](hyp:π), the [explicit Doob-martingale
value after `k` reveals](goal) averages the revealed outcomes and fills the unrevealed sample
positions with their remaining-population conditional mean. -/
noncomputable def permutationHajekValue {N : ℕ} (K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (y : Fin N → ℝ) (k : ℕ) (hk : k ≤ K) (π : PermutationSampleSpace N) : ℝ :=
  (permutationRevealedSum y k (hk.trans hKlt.le) π +
      ((K - k : ℕ) : ℝ) * permutationNextMean y k (hk.trans_lt hKlt) π) / (K : ℝ) -
    popMean y

/-- Given [a proper positive sample size](hyp:K,hKpos,hKlt), [population outcomes](hyp:y),
[an active reveal time](hyp:k,hk), and [an ordering](hyp:π), [the successive explicit Doob values
differ by the Hájek reveal increment](goal). -/
theorem permutationHajekValue_succ_sub {N : ℕ} (K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (y : Fin N → ℝ) (k : ℕ) (hk : k < K) (π : PermutationSampleSpace N) :
    permutationHajekValue K hKpos hKlt y (k + 1) hk π -
        permutationHajekValue K hKpos hKlt y k hk.le π =
      permutationHajekIncrement K hKpos hKlt y k hk π := by
  have hkN : k < N := hk.trans hKlt
  have hksN : k + 1 < N := by omega
  have hk1N : k + 1 ≤ N := hksN.le
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hRne : ((N - k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hkN).ne'
  have hR1ne : ((N - k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : 0 < N - k - 1).ne'
  have hremain : permutationRemainingSum y (k + 1) hk1N π =
      permutationRemainingSum y k hkN.le π - permutationDraw y k hkN π := by
    unfold permutationRemainingSum
    rw [permutationRevealedSum_succ]
    ring
  rw [permutationHajekValue, permutationHajekValue,
    permutationHajekIncrement, permutationNextMean_eq_remainingMean,
    permutationNextMean_eq_remainingMean, hremain,
    permutationRevealedSum_succ]
  have hNK : (N - K : ℕ) = N - K := rfl
  have hNs : N - (k + 1) = N - k - 1 := by omega
  have hKs : K - (k + 1) = K - k - 1 := by omega
  rw [hNs, hKs]
  unfold hajekIncrementCoefficient
  field_simp [hKne, hRne, hR1ne]
  rw [Nat.cast_sub (by omega : 1 ≤ N - k), Nat.cast_sub (by omega : 1 ≤ K - k),
    Nat.cast_sub hkN.le, Nat.cast_sub hk.le, Nat.cast_sub hKlt.le]
  norm_num
  ring

/-- Given [a proper positive sample size](hyp:K,hKpos,hKlt), [population outcomes](hyp:y), and
[an ordering](hyp:π), [the explicit Hájek martingale starts at zero](goal). -/
theorem permutationHajekValue_zero {N : ℕ} (K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (y : Fin N → ℝ) (π : PermutationSampleSpace N) :
    permutationHajekValue K hKpos hKlt y 0 (Nat.zero_le K) π = 0 := by
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hNpos : 0 < N := hKpos.trans hKlt
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hsum : (∑ i : Fin N, y (π i)) = ∑ i : Fin N, y i := Equiv.sum_comp π y
  unfold permutationHajekValue
  rw [permutationNextMean_eq_remainingMean]
  simp only [permutationRevealedSum, Fintype.sum_empty, permutationRemainingSum, hsum, popMean,
    Nat.sub_zero, Fintype.card_fin, zero_add, sub_zero]
  field_simp [hKne, hNne]
  ring

/-- Given [a proper positive sample size](hyp:K,hKpos,hKlt), [population outcomes](hyp:y), and
[an ordering](hyp:π), [the explicit Hájek martingale ends at the centered first-`K` sample
mean](goal). -/
theorem permutationHajekValue_final {N : ℕ} (K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (y : Fin N → ℝ) (π : PermutationSampleSpace N) :
    permutationHajekValue K hKpos hKlt y K le_rfl π =
      permutationSampleMean K hKlt.le y π - popMean y := by
  simp only [permutationHajekValue, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
  unfold permutationSampleMean permutationRevealedSum
  rfl

/-- For [a nonempty finite population](hyp:N,hN), [population outcomes](hyp:y), and [a unit](hyp:i),
[that unit's absolute deviation from the population mean is bounded by the square root of the
maximum squared deviation](goal). -/
lemma abs_sub_popMean_le_sqrt_popMaxSqDev {N : ℕ} [hN : Nonempty (Fin N)]
    (y : Fin N → ℝ) (i : Fin N) :
    |y i - popMean y| ≤ Real.sqrt (popMaxSqDev y) := by
  apply Real.abs_le_sqrt
  unfold popMaxSqDev
  exact Finset.le_sup' (fun j : Fin N => (y j - popMean y) ^ 2) (Finset.mem_univ i)

/-- For [a nonempty finite population](hyp:N,hN), [population outcomes](hyp:y), [a valid reveal
time](hyp:k,hk), and [an ordering](hyp:π), [the remaining-population conditional mean differs from
the full population mean by at most the square root of the maximum squared deviation](goal). -/
lemma abs_permutationNextMean_sub_popMean_le_sqrt_popMaxSqDev
    {N : ℕ} [hN : Nonempty (Fin N)] (y : Fin N → ℝ) (k : ℕ) (hk : k < N)
    (π : PermutationSampleSpace N) :
    |permutationNextMean y k hk π - popMean y| ≤ Real.sqrt (popMaxSqDev y) := by
  have hRposNat : 0 < N - k := Nat.sub_pos_of_lt hk
  have hRpos : (0 : ℝ) < (N - k : ℕ) := by exact_mod_cast hRposNat
  rw [permutationNextMean_eq_remainingMean,
    ← sum_remainingPositions_eq_permutationRemainingSum]
  have heq :
      (∑ j : Fin (N - k), y (π (permutationRemainingPosition k hk.le j))) /
          ((N - k : ℕ) : ℝ) - popMean y =
        (∑ j : Fin (N - k),
          (y (π (permutationRemainingPosition k hk.le j)) - popMean y)) /
            ((N - k : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [ne_of_gt hRpos]
  rw [heq, abs_div, abs_of_pos hRpos]
  apply (div_le_iff₀ hRpos).2
  calc
    |∑ j : Fin (N - k),
        (y (π (permutationRemainingPosition k hk.le j)) - popMean y)| ≤
        ∑ j : Fin (N - k),
          |y (π (permutationRemainingPosition k hk.le j)) - popMean y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (N - k), Real.sqrt (popMaxSqDev y) := by
      apply Finset.sum_le_sum
      intro j _
      exact abs_sub_popMean_le_sqrt_popMaxSqDev y
        (π (permutationRemainingPosition k hk.le j))
    _ = Real.sqrt (popMaxSqDev y) * ((N - k : ℕ) : ℝ) := by
      simp [mul_comm]

/-- For [a nonempty finite population](hyp:N,hN), [population outcomes](hyp:y), [a valid reveal
time](hyp:k,hk), and [an ordering](hyp:π), [the next draw centered by its remaining-population
mean is bounded in absolute value by twice the square root of the maximal squared
deviation](goal). -/
lemma abs_permutationDraw_sub_nextMean_le_two_sqrt_popMaxSqDev
    {N : ℕ} [hN : Nonempty (Fin N)] (y : Fin N → ℝ) (k : ℕ) (hk : k < N)
    (π : PermutationSampleSpace N) :
    |permutationDraw y k hk π - permutationNextMean y k hk π| ≤
      2 * Real.sqrt (popMaxSqDev y) := by
  calc
    |permutationDraw y k hk π - permutationNextMean y k hk π| =
        |(permutationDraw y k hk π - popMean y) -
          (permutationNextMean y k hk π - popMean y)| := by ring_nf
    _ ≤ |permutationDraw y k hk π - popMean y| +
        |permutationNextMean y k hk π - popMean y| := abs_sub _ _
    _ ≤ Real.sqrt (popMaxSqDev y) + Real.sqrt (popMaxSqDev y) :=
      add_le_add
        (abs_sub_popMean_le_sqrt_popMaxSqDev y _)
        (abs_permutationNextMean_sub_popMean_le_sqrt_popMaxSqDev y k hk π)
    _ = 2 * Real.sqrt (popMaxSqDev y) := by ring

/-- Given [a proper positive sample size](hyp:K,hKpos,hKlt) and [an active reveal
time](hyp:k,hk), [the nonnegative Hájek coefficient is at most the reciprocal sample size](goal). -/
lemma hajekIncrementCoefficient_le_inv
    (N K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (k : ℕ) (hk : k < K) :
    0 ≤ hajekIncrementCoefficient N K hKpos hKlt k ∧
      hajekIncrementCoefficient N K hKpos hKlt k ≤ 1 / (K : ℝ) := by
  have hRposNat : 0 < N - k - 1 := by omega
  have hRpos : (0 : ℝ) < (N - k - 1 : ℕ) := by exact_mod_cast hRposNat
  have hKposR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hLleRNat : N - K ≤ N - k - 1 := by omega
  have hLleR : ((N - K : ℕ) : ℝ) ≤ (N - k - 1 : ℕ) := by
    exact_mod_cast hLleRNat
  constructor
  · unfold hajekIncrementCoefficient
    positivity
  · unfold hajekIncrementCoefficient
    rw [div_le_iff₀ (mul_pos hKposR hRpos)]
    field_simp [ne_of_gt hKposR]
    nlinarith

/-- Given [a proper positive sample size](hyp:K,hKpos,hKlt), [population outcomes](hyp:y),
[an active reveal time](hyp:k,hk), and [an ordering](hyp:π), [the absolute Hájek increment is
at most twice the maximal centered deviation divided by the sample size](goal). -/
lemma abs_permutationHajekIncrement_le
    {N : ℕ} [Nonempty (Fin N)] (K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (y : Fin N → ℝ) (k : ℕ) (hk : k < K) (π : PermutationSampleSpace N) :
    |permutationHajekIncrement K hKpos hKlt y k hk π| ≤
      2 * Real.sqrt (popMaxSqDev y) / (K : ℝ) := by
  obtain ⟨hc0, hc⟩ := hajekIncrementCoefficient_le_inv N K hKpos hKlt k hk
  have hsqrt : 0 ≤ 2 * Real.sqrt (popMaxSqDev y) := by positivity
  rw [permutationHajekIncrement, abs_mul, abs_of_nonneg hc0]
  calc
    hajekIncrementCoefficient N K hKpos hKlt k *
          |permutationDraw y k (hk.trans hKlt) π -
            permutationNextMean y k (hk.trans hKlt) π| ≤
        hajekIncrementCoefficient N K hKpos hKlt k *
          (2 * Real.sqrt (popMaxSqDev y)) :=
      mul_le_mul_of_nonneg_left
        (abs_permutationDraw_sub_nextMean_le_two_sqrt_popMaxSqDev
          y k (hk.trans hKlt) π) hc0
    _ ≤ (1 / (K : ℝ)) * (2 * Real.sqrt (popMaxSqDev y)) :=
      mul_le_mul_of_nonneg_right hc hsqrt
    _ = 2 * Real.sqrt (popMaxSqDev y) / (K : ℝ) := by ring

/-- Given [two natural-number counts and finite-population outcomes](hyp:N,K,y), the [simple-random-sample
mean variance expression](goal) is the difference of their reciprocal real embeddings multiplied by
the finite-population variance. -/
noncomputable def srsSampleMeanVariance (N K : ℕ) (y : Fin N → ℝ) : ℝ :=
  (1 / (K : ℝ) - 1 / (N : ℝ)) * popVar y

/-- For [a sample size that is positive and strictly smaller than the population
size](hyp:hKpos,hKlt) and [a population whose finite-population variance is
positive](hyp:hvar), [the simple-random-sample mean variance expression is
positive](goal).

Outside this range the expression is not a variance: `1 / K` is `0` when `K = 0` by the
division convention, and `1 / K - 1 / N` is negative when `K > N`, so every result that reads
this expression as a variance carries these two hypotheses. -/
lemma srsSampleMeanVariance_pos {N K : ℕ} {y : Fin N → ℝ}
    (hKpos : 0 < K) (hKlt : K < N) (hvar : 0 < popVar y) :
    0 < srsSampleMeanVariance N K y := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hfactor : (0 : ℝ) < 1 / (K : ℝ) - 1 / (N : ℝ) :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hKR (by exact_mod_cast hKlt))
  exact mul_pos hfactor hvar

/-- Given [a proper positive sample size](hyp:K,hKpos,hKlt), [population outcomes](hyp:y),
[an active reveal time](hyp:k,hk), and [an ordering](hyp:π), the [standardized Hájek
increment](goal) divides the reveal increment by the exact sample-mean standard deviation. -/
noncomputable def standardizedPermutationHajekIncrement
    {N : ℕ} (K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (y : Fin N → ℝ)
    (k : ℕ) (hk : k < K) (π : PermutationSampleSpace N) : ℝ :=
  permutationHajekIncrement K hKpos hKlt y k hk π /
    Real.sqrt (srsSampleMeanVariance N K y)

/-- Given [a proper positive sample size](hyp:K,hKpos,hKlt), [population outcomes](hyp:y) with
[positive variance](hyp:hvar), [an active reveal time](hyp:k,hk), and [an ordering](hyp:π),
[the squared standardized Hájek increment is bounded by eight times the Hájek
maximal-deviation ratio](goal). -/
theorem standardizedPermutationHajekIncrement_sq_le
    {N : ℕ} [Nonempty (Fin N)] (K : ℕ) (hKpos : 0 < K) (hKlt : K < N)
    (y : Fin N → ℝ) (hvar : 0 < popVar y) (k : ℕ) (hk : k < K)
    (π : PermutationSampleSpace N) :
    (standardizedPermutationHajekIncrement K hKpos hKlt y k hk π) ^ 2 ≤
      8 * popMaxSqDev y / (((min K (N - K) : ℕ) : ℝ) * popVar y) := by
  have hNpos : 0 < N := hKpos.trans hKlt
  have hLpos : 0 < N - K := Nat.sub_pos_of_lt hKlt
  have hminpos : 0 < min K (N - K) := lt_min hKpos hLpos
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hLR : (0 : ℝ) < (N - K : ℕ) := by exact_mod_cast hLpos
  have hminR : (0 : ℝ) < (min K (N - K) : ℕ) := by exact_mod_cast hminpos
  have hsampleVar : 0 < srsSampleMeanVariance N K y :=
    srsSampleMeanVariance_pos hKpos hKlt hvar
  have hmax0 : 0 ≤ popMaxSqDev y := by
    let i : Fin N := Classical.choice (inferInstance : Nonempty (Fin N))
    exact (sq_nonneg (y i - popMean y)).trans (by
      unfold popMaxSqDev
      exact Finset.le_sup' (fun j : Fin N => (y j - popMean y) ^ 2) (Finset.mem_univ i))
  have hraw := abs_permutationHajekIncrement_le K hKpos hKlt y k hk π
  have hstd :
      |standardizedPermutationHajekIncrement K hKpos hKlt y k hk π| ≤
        (2 * Real.sqrt (popMaxSqDev y) / (K : ℝ)) /
          Real.sqrt (srsSampleMeanVariance N K y) := by
    unfold standardizedPermutationHajekIncrement
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 hsampleVar)]
    exact div_le_div_of_nonneg_right hraw (Real.sqrt_nonneg _)
  have hsquare :
      (standardizedPermutationHajekIncrement K hKpos hKlt y k hk π) ^ 2 ≤
        ((2 * Real.sqrt (popMaxSqDev y) / (K : ℝ)) /
          Real.sqrt (srsSampleMeanVariance N K y)) ^ 2 := by
    apply (sq_le_sq).2
    simpa [abs_of_nonneg (by positivity : 0 ≤
      (2 * Real.sqrt (popMaxSqDev y) / (K : ℝ)) /
        Real.sqrt (srsSampleMeanVariance N K y))] using hstd
  have hboundSq :
      ((2 * Real.sqrt (popMaxSqDev y) / (K : ℝ)) /
          Real.sqrt (srsSampleMeanVariance N K y)) ^ 2 =
        4 * popMaxSqDev y /
          ((K : ℝ) ^ 2 * srsSampleMeanVariance N K y) := by
    rw [div_pow, div_pow, mul_pow, Real.sq_sqrt hmax0,
      Real.sq_sqrt hsampleVar.le]
    ring
  rw [hboundSq] at hsquare
  refine hsquare.trans ?_
  have hdenLeft : 0 < (K : ℝ) ^ 2 * srsSampleMeanVariance N K y := by positivity
  have hdenRight : 0 < ((min K (N - K) : ℕ) : ℝ) * popVar y :=
    mul_pos hminR hvar
  rw [div_le_div_iff₀ hdenLeft hdenRight]
  have hminK : ((min K (N - K) : ℕ) : ℝ) ≤ K := by
    exact_mod_cast min_le_left K (N - K)
  have hminL : ((min K (N - K) : ℕ) : ℝ) ≤ (N - K : ℕ) := by
    exact_mod_cast min_le_right K (N - K)
  have hNsum : (N : ℝ) = (K : ℝ) + (N - K : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le hKlt.le).symm
  have hLcast : ((N - K : ℕ) : ℝ) = (N : ℝ) - (K : ℝ) :=
    Nat.cast_sub hKlt.le
  have hmKprod : ((min K (N - K) : ℕ) : ℝ) * (K : ℝ) ≤
      (K : ℝ) * (N - K : ℕ) := by
    nlinarith
  have hmLprod : ((min K (N - K) : ℕ) : ℝ) * (N - K : ℕ) ≤
      (K : ℝ) * (N - K : ℕ) := by
    nlinarith
  have hcore : ((min K (N - K) : ℕ) : ℝ) * (N : ℝ) ≤
      2 * (K : ℝ) * (N - K : ℕ) := by
    rw [hNsum]
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hcore
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hmax0)
  unfold srsSampleMeanVariance
  field_simp [ne_of_gt hKR, ne_of_gt hNR]
  rw [← hLcast]
  ring_nf at hscaled ⊢
  exact hscaled

/-- Given [nonempty finite populations](hyp:N,hN), [proper positive sample
sizes](hyp:K,hKpos,hKlt), and [population outcomes](hyp:y) with [positive
variances](hyp:hvar), if [the Li–Ding maximal-deviation sufficient-condition ratio tends to zero](hyp:hmax), then
[every active standardized reveal increment is eventually uniformly below each positive
threshold](goal). -/
theorem standardizedPermutationHajekIncrement_eventually_uniformly_small
    (N K : ℕ → ℕ) [hN : ∀ n, Nonempty (Fin (N n))]
    (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (hvar : ∀ n, 0 < popVar (y n))
    (hmax : Tendsto (fun n =>
      popMaxSqDev (y n) /
        (((min (K n) (N n - K n) : ℕ) : ℝ) * popVar (y n))) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ k, (hk : k < K n) →
      ∀ π : PermutationSampleSpace (N n),
        |standardizedPermutationHajekIncrement
          (K n) (hKpos n) (hKlt n) (y n) k hk π| ≤ ε := by
  intro ε hε
  have hthreshold : (0 : ℝ) < ε ^ 2 / 8 := by positivity
  filter_upwards [hmax.eventually_lt_const hthreshold] with n hn
  intro k hk π
  have hsq := standardizedPermutationHajekIncrement_sq_le
    (K n) (hKpos n) (hKlt n) (y n) (hvar n) k hk π
  have hsqLt :
      (standardizedPermutationHajekIncrement
        (K n) (hKpos n) (hKlt n) (y n) k hk π) ^ 2 < ε ^ 2 := by
    calc
      (standardizedPermutationHajekIncrement
          (K n) (hKpos n) (hKlt n) (y n) k hk π) ^ 2 ≤
          8 * (popMaxSqDev (y n) /
            (((min (K n) (N n - K n) : ℕ) : ℝ) * popVar (y n))) := by
        simpa [mul_div_assoc] using hsq
      _ < 8 * (ε ^ 2 / 8) := mul_lt_mul_of_pos_left hn (by norm_num)
      _ = ε ^ 2 := by ring
  exact (abs_lt_of_sq_lt_sq hsqLt hε.le).le

/-- Given [a proper positive sample size](hyp:K,hKpos,hKlt), [population outcomes](hyp:y), and
[an active reveal time](hyp:k,hk), [the conditional second moment of the Hájek increment is its
coefficient squared times the remaining-population variance](goal). -/
theorem permutationHajekIncrement_sq_condExp {N : ℕ}
    (K : ℕ) (hKpos : 0 < K) (hKlt : K < N) (y : Fin N → ℝ)
    (k : ℕ) (hk : k < K) :
    ((uniformPermutationDesign N).toMeasure)[
      (fun π => (permutationHajekIncrement K hKpos hKlt y k hk π) ^ 2) |
        (permutationRevealFiltration N) k] =ᵐ[(uniformPermutationDesign N).toMeasure]
      fun π => (hajekIncrementCoefficient N K hKpos hKlt k) ^ 2 *
        permutationNextVariance y k (hk.trans hKlt) π := by
  let μ := (uniformPermutationDesign N).toMeasure
  let m := (permutationRevealFiltration N) k
  let c := hajekIncrementCoefficient N K hKpos hKlt k
  let X : PermutationSampleSpace N → ℝ := fun π =>
    permutationDraw y k (hk.trans hKlt) π -
      permutationNextMean y k (hk.trans hKlt) π
  have hfun :
      (fun π => (permutationHajekIncrement K hKpos hKlt y k hk π) ^ 2) =
        (c ^ 2) • fun π => (X π) ^ 2 := by
    funext π
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold permutationHajekIncrement
    change (c * X π) ^ 2 = c ^ 2 * X π ^ 2
    ring
  have hlinear := condExp_smul (μ := μ) (c ^ 2) (fun π => (X π) ^ 2) m
  have hvariance := permutationNextVariance_ae_eq_condExp y k (hk.trans hKlt)
  rw [hfun]
  filter_upwards [hlinear, hvariance] with π hlinearπ hvarianceπ
  change μ[(c ^ 2) • (fun π => X π ^ 2) | m] π =
    c ^ 2 * permutationNextVariance y k (hk.trans hKlt) π
  rw [hlinearπ, hvarianceπ]
  simp only [Pi.smul_apply, smul_eq_mul]
  rfl

private lemma sum_range_succ_sub (K : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range K, (f (k + 1) - f k)) = f K - f 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Given [sequences of population sizes](hyp:N), [proper positive sample sizes](hyp:K,hKpos,hKlt),
and [finite-population outcomes](hyp:y), the [explicit Hájek martingale-difference array](goal)
reveals one sampled unit at a time. -/
noncomputable def srsPermutationHajekArray
    (N K : ℕ → ℕ) (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) :
    MartingaleDifferenceArray
      (fun n => PermutationSampleSpace (N n))
      (fun n => (uniformPermutationDesign (N n)).toMeasure) where
  rowLength := K
  increment := fun n k π => if hk : k < K n then
    permutationHajekIncrement (K n) (hKpos n) (hKlt n) (y n) k hk π else 0
  filtration := fun n => permutationRevealFiltration (N n)
  adapted := by
    intro n k hk
    simp only [hk, dite_true, permutationHajekIncrement]
    apply StronglyMeasurable.const_mul
    exact (permutationDraw_stronglyMeasurable (y n) k (hk.trans (hKlt n))).sub
      ((permutationNextMean_stronglyMeasurable (y n) k (hk.trans (hKlt n))).mono
        ((permutationRevealFiltration (N n)).mono (Nat.le_succ k)))
  squareIntegrable := by
    intro n k hk
    exact (uniformPermutationDesign (N n)).memLp_toMeasure
      (fun π => if hk' : k < K n then
        permutationHajekIncrement (K n) (hKpos n) (hKlt n) (y n) k hk' π else 0) 2
  condExp_zero := by
    intro n k hk
    simp only [hk, dite_true, permutationHajekIncrement]
    let μ := (uniformPermutationDesign (N n)).toMeasure
    let m := (permutationRevealFiltration (N n)) k
    let X : PermutationSampleSpace (N n) → ℝ := fun π =>
      permutationDraw (y n) k (hk.trans (hKlt n)) π -
        permutationNextMean (y n) k (hk.trans (hKlt n)) π
    have hzero : μ[X | m] =ᵐ[μ] 0 :=
      permutationCenteredDraw_condExp_zero (y n) k (hk.trans (hKlt n))
    have hsmul := condExp_smul (μ := μ)
      (hajekIncrementCoefficient (N n) (K n) (hKpos n) (hKlt n) k) X m
    let c := hajekIncrementCoefficient (N n) (K n) (hKpos n) (hKlt n) k
    have hfun : (fun ω => c * X ω) = c • X := by
      funext ω
      simp [smul_eq_mul]
    change μ[(fun ω => c * X ω) | m] =ᵐ[μ] 0
    rw [hfun]
    filter_upwards [hsmul, hzero] with π hsmulπ hzeroπ
    rw [hsmulπ]
    simp [hzeroπ]

/-- Given [row spaces](hyp:Ω), [their measurable structures](hyp:mΩ), [row
measures](hyp:μ), [a martingale-difference array](hyp:A), and [deterministic row
scalars](hyp:c), the [row-scaled martingale-difference array](goal) multiplies every increment in
row `n` by `c n`. -/
noncomputable def scaleMartingaleDifferenceArray
    {Ω : ℕ → Type*} [mΩ : (n : ℕ) → MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)}
    (A : MartingaleDifferenceArray Ω μ) (c : ℕ → ℝ) :
    MartingaleDifferenceArray Ω μ where
  rowLength := A.rowLength
  increment := fun n k ω => c n * A.increment n k ω
  filtration := A.filtration
  adapted := by
    intro n k hk
    exact (A.adapted n k hk).const_mul (c n)
  squareIntegrable := by
    intro n k hk
    exact (A.squareIntegrable n k hk).const_mul (c n)
  condExp_zero := by
    intro n k hk
    have hlinear := condExp_smul (μ := μ n) (c n) (A.increment n k) (A.filtration n k)
    have hzero := A.condExp_zero n k hk
    have hfun : (fun ω => c n * A.increment n k ω) = (c n) • A.increment n k := by
      funext ω
      simp [smul_eq_mul]
    rw [hfun]
    filter_upwards [hlinear, hzero] with ω hlinearω hzeroω
    rw [hlinearω]
    simp [hzeroω]

/-- Given [sequences of population sizes](hyp:N), [proper positive sample
sizes](hyp:K,hKpos,hKlt), and [finite-population outcomes](hyp:y), the [standardized explicit
Hájek martingale-difference array](goal) divides each reveal increment by the exact
simple-random-sample standard deviation. -/
noncomputable def standardizedSrsPermutationHajekArray
    (N K : ℕ → ℕ) (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) :
    MartingaleDifferenceArray
      (fun n => PermutationSampleSpace (N n))
      (fun n => (uniformPermutationDesign (N n)).toMeasure) :=
  scaleMartingaleDifferenceArray (srsPermutationHajekArray N K hKpos hKlt y)
    (fun n => (Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)))⁻¹)

/-- Given [sequences of population sizes](hyp:N), [proper positive sample
sizes](hyp:K,hKpos,hKlt), [finite-population outcomes](hyp:y), [a row](hyp:n), [an active reveal
time](hyp:k,hk), and [an ordering](hyp:π), [the standardized array increment equals the explicit
standardized Hájek increment](goal). -/
lemma standardizedSrsPermutationHajekArray_increment
    (N K : ℕ → ℕ) (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (n k : ℕ) (hk : k < K n)
    (π : PermutationSampleSpace (N n)) :
    (standardizedSrsPermutationHajekArray N K hKpos hKlt y).increment n k π =
      standardizedPermutationHajekIncrement
        (K n) (hKpos n) (hKlt n) (y n) k hk π := by
  unfold standardizedSrsPermutationHajekArray scaleMartingaleDifferenceArray
    srsPermutationHajekArray standardizedPermutationHajekIncrement
  simp only [hk, dite_true]
  ring

/-- Given [nonempty finite populations](hyp:N,hN), [proper positive sample
sizes](hyp:K,hKpos,hKlt), and [population outcomes](hyp:y) with [positive
variances](hyp:hvar), if [the Li–Ding maximal-deviation sufficient-condition ratio tends to zero](hyp:hmax), then
[the standardized Hájek array satisfies the conditional Lindeberg condition](goal). -/
theorem standardizedSrsPermutationHajekArray_conditionalLindeberg
    (N K : ℕ → ℕ) [hN : ∀ n, Nonempty (Fin (N n))]
    (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (hvar : ∀ n, 0 < popVar (y n))
    (hmax : Tendsto (fun n =>
      popMaxSqDev (y n) /
        (((min (K n) (N n - K n) : ℕ) : ℝ) * popVar (y n))) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → TendstoInProbability
      (fun n => (uniformPermutationDesign (N n)).toMeasure)
      ((standardizedSrsPermutationHajekArray N K hKpos hKlt y).conditionalLindeberg ε) 0 := by
  apply conditionalLindeberg_tendstoInProbability_of_eventually_uniformly_small
  intro ε hε
  filter_upwards [standardizedPermutationHajekIncrement_eventually_uniformly_small
    N K hKpos hKlt y hvar hmax ε hε] with n hn
  intro k hk π
  change k < K n at hk
  rw [standardizedSrsPermutationHajekArray_increment N K hKpos hKlt y n k hk π]
  exact hn k hk π

/-- Given [sequences of population sizes](hyp:N), [proper positive sample sizes](hyp:K,hKpos,hKlt),
[finite-population outcomes](hyp:y), and [a row](hyp:n), [the explicit Hájek array's row sum is
the centered first-`K` simple-random-sample mean](goal). -/
theorem srsPermutationHajekArray_rowSum
    (N K : ℕ → ℕ) (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (n : ℕ) :
    (srsPermutationHajekArray N K hKpos hKlt y).rowSum n = fun π =>
      permutationSampleMean (K n) (hKlt n).le (y n) π - popMean (y n) := by
  funext π
  unfold MartingaleDifferenceArray.rowSum srsPermutationHajekArray
  simp only [Finset.sum_apply]
  let f : ℕ → ℝ := fun k => if hk : k ≤ K n then
    permutationHajekValue (K n) (hKpos n) (hKlt n) (y n) k hk π else 0
  calc
    (∑ k ∈ Finset.range (K n), if hk : k < K n then
        permutationHajekIncrement (K n) (hKpos n) (hKlt n) (y n) k hk π else 0) =
        ∑ k ∈ Finset.range (K n), (f (k + 1) - f k) := by
      apply Finset.sum_congr rfl
      intro k hkRange
      have hk := Finset.mem_range.mp hkRange
      simp only [hk, dite_true]
      simp only [f, hk.le, Nat.succ_le_iff.mpr hk, dite_true]
      exact (permutationHajekValue_succ_sub
        (K n) (hKpos n) (hKlt n) (y n) k hk π).symm
    _ = f (K n) - f 0 := sum_range_succ_sub (K n) f
    _ = permutationSampleMean (K n) (hKlt n).le (y n) π - popMean (y n) := by
      simp only [f, le_rfl, Nat.zero_le, dite_true]
      rw [permutationHajekValue_final, permutationHajekValue_zero, sub_zero]

/-- Given [sequences of population sizes](hyp:N), [proper positive sample
sizes](hyp:K,hKpos,hKlt), [finite-population outcomes](hyp:y), and [a row](hyp:n), [the
standardized Hájek array's row sum is the centered sample mean divided by its exact standard
deviation](goal). -/
theorem standardizedSrsPermutationHajekArray_rowSum
    (N K : ℕ → ℕ) (hKpos : ∀ n, 0 < K n) (hKlt : ∀ n, K n < N n)
    (y : ∀ n, Fin (N n) → ℝ) (n : ℕ) :
    (standardizedSrsPermutationHajekArray N K hKpos hKlt y).rowSum n = fun π =>
      (permutationSampleMean (K n) (hKlt n).le (y n) π - popMean (y n)) /
        Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)) := by
  funext π
  unfold MartingaleDifferenceArray.rowSum standardizedSrsPermutationHajekArray
    scaleMartingaleDifferenceArray
  simp only [Finset.sum_apply, ← Finset.mul_sum]
  change (Real.sqrt (srsSampleMeanVariance (N n) (K n) (y n)))⁻¹ *
      (∑ k ∈ Finset.range (K n),
        (srsPermutationHajekArray N K hKpos hKlt y).increment n k π) = _
  rw [show (∑ k ∈ Finset.range (K n),
      (srsPermutationHajekArray N K hKpos hKlt y).increment n k π) =
        permutationSampleMean (K n) (hKlt n).le (y n) π - popMean (y n) by
      simpa [MartingaleDifferenceArray.rowSum, srsPermutationHajekArray] using
        congrFun (srsPermutationHajekArray_rowSum N K hKpos hKlt y n) π]
  rw [div_eq_mul_inv]
  ring

end Causalean.Experimentation.DesignBased
