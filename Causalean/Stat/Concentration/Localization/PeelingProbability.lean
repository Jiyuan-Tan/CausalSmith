/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Dyadic peeling with an explicit failure bound

In a peeling argument over shells of radius 2^k·δ, a tail bound exp(−c·n·r²) at
radius r gives the k-th shell failure probability exp(−4^k·t) with t = c·n·δ².
This file sums those probabilities: for t ≥ 1 the series is dominated by a
geometric series and is at most 2·exp(−t); for t < 1 the bound 4·exp(−t) exceeds
one. The union bound therefore holds for every t, with no lower bound on the
sample size or the radius.

## Main results

* `dyadic_exp_sum_le` — Σ_k exp(−4^k·t) ≤ 2·exp(−t) for t ≥ 1.
* `probability_dyadic_union_le` — a base event and dyadic shell events with these
  probability bounds have union of probability at most 4·exp(−t).
-/

public section

namespace Causalean.Stat.Concentration

open MeasureTheory

/-- For [t ≥ 1](hyp:ht), [the series Σ_{k ≥ 0} exp(−4^k·t) converges and its sum is at most
2·exp(−t)](goal). -/
lemma dyadic_exp_sum_le {t : ℝ} (ht : 1 ≤ t) :
    Summable (fun k : ℕ => Real.exp (-((4 : ℝ) ^ k * t))) ∧
      (∑' k : ℕ, Real.exp (-((4 : ℝ) ^ k * t))) ≤ 2 * Real.exp (-t) := by
  have ht0 : 0 ≤ t := by linarith
  have hr0 : 0 ≤ Real.exp (-(3 * t)) := Real.exp_nonneg _
  have hrhalf : Real.exp (-(3 * t)) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have hexp := Real.add_one_le_exp (3 * t)
    norm_num
    linarith
  have hr1 : Real.exp (-(3 * t)) < 1 := by linarith
  have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-t))
  have hmajor : ∀ k : ℕ, Real.exp (-((4 : ℝ) ^ k * t)) ≤
      Real.exp (-t) * Real.exp (-(3 * t)) ^ k := by
    intro k
    have hpow : 1 + (k : ℝ) * 3 ≤ (4 : ℝ) ^ k := by
      simpa only [show (1 : ℝ) + 3 = 4 by norm_num] using
        one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 3) k
    calc
      Real.exp (-((4 : ℝ) ^ k * t)) ≤
          Real.exp (-t + (k : ℝ) * (-(3 * t))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hpow ht0]
      _ = Real.exp (-t) * Real.exp (-(3 * t)) ^ k := by
        rw [Real.exp_add, Real.exp_nat_mul]
  have hsum := hgeom.of_nonneg_of_le (fun k => Real.exp_nonneg _) hmajor
  refine ⟨hsum, (hsum.tsum_le_tsum hmajor hgeom).trans ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hinv : (1 - Real.exp (-(3 * t)))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    norm_num
    linarith
  calc
    Real.exp (-t) * (1 - Real.exp (-(3 * t)))⁻¹ ≤ Real.exp (-t) * 2 :=
      mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg (-t))
    _ = 2 * Real.exp (-t) := mul_comm _ _

/-- Under [a probability measure μ](hyp:μ), if [an event E₀ has probability at most
exp(−t)](hyp:E₀,hbase) and [events E_k, k = 0, 1, 2, …, have probabilities at most
exp(−4^k·t)](hyp:E,hshell), then [μ(E₀ ∪ ⋃_k E_k) ≤ 4·exp(−t)](goal).

The real number t is arbitrary; for t < 1 the right-hand side is at least one. -/
lemma probability_dyadic_union_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E₀ : Set Ω) (E : ℕ → Set Ω)
    {t : ℝ} (hbase : μ.real E₀ ≤ Real.exp (-t))
    (hshell : ∀ k, μ.real (E k) ≤ Real.exp (-((4 : ℝ) ^ k * t))) :
    μ.real (E₀ ∪ ⋃ k, E k) ≤ 4 * Real.exp (-t) := by
  by_cases ht1 : 1 ≤ t
  · obtain ⟨hsum, hbound⟩ := dyadic_exp_sum_le ht1
    have hunion : μ (⋃ k, E k) ≤
        ENNReal.ofReal (∑' k : ℕ, Real.exp (-((4 : ℝ) ^ k * t))) := by
      calc
        μ (⋃ k, E k) ≤ ∑' k, μ (E k) := measure_iUnion_le E
        _ ≤ ∑' k, ENNReal.ofReal (Real.exp (-((4 : ℝ) ^ k * t))) := by
          apply ENNReal.tsum_le_tsum
          intro k
          simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ (E k))]
            using ENNReal.ofReal_le_ofReal (hshell k)
        _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun k => Real.exp_nonneg _) hsum).symm
    have hunionReal : μ.real (⋃ k, E k) ≤
        ∑' k : ℕ, Real.exp (-((4 : ℝ) ^ k * t)) := by
      simpa only [Measure.real, ENNReal.toReal_ofReal (tsum_nonneg (fun k => Real.exp_nonneg _))]
        using ENNReal.toReal_mono ENNReal.ofReal_ne_top hunion
    have htotal := measureReal_union_le (μ := μ) E₀ (⋃ k, E k)
    have hexp := Real.exp_nonneg (-t)
    linarith
  · have htlt : t < 1 := lt_of_not_ge ht1
    have hexp : Real.exp t ≤ 4 := by
      exact (Real.exp_le_exp.mpr htlt.le).trans (by linarith [Real.exp_one_lt_three])
    have hone : 1 ≤ 4 * Real.exp (-t) := by
      rw [Real.exp_neg]
      exact (le_mul_inv_iff₀ (Real.exp_pos t)).2 (by simpa using hexp)
    exact measureReal_le_one.trans hone

end Causalean.Stat.Concentration
