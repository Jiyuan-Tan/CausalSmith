module
public import Causalean.Mathlib.Probability.Birthday.Concentration

/-!
# Averaging a kernel concentrated around the binomial mean

A bounded count kernel converges in binomial average when it is uniformly
close to its target on a fixed relative band around a diverging mean.
-/

public section

namespace Causalean.Mathlib.Probability.Birthday

open Filter

/-- A [bounded count kernel](hyp:hbound) that is [uniformly close on a
relative mean band](hyp:hband) has [a convergent binomial average](goal) when
the [success parameters are valid](hyp:heta), the [mean diverges](hyp:hmean),
and the [target lies in the unit interval](hyp:hc). -/
theorem binomialAverage_tendsto_of_relative_band
    (Tseq : ℕ → ℕ) (etaseq : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (c : ℝ)
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hbound : ∀ j r, r ≤ Tseq j → f j r ∈ Set.Icc (0 : ℝ) 1)
    (hband : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ j in atTop, ∀ r : ℕ, r ≤ Tseq j →
        |(r : ℝ) - mean (Tseq j) (etaseq j)| <
          ε * mean (Tseq j) (etaseq j) → |f j r - c| ≤ δ) :
    Tendsto (fun j => binomialAverage (Tseq j) (etaseq j) (f j)) atTop (nhds c) := by
  apply (Metric.tendsto_nhds).2
  intro a ha
  obtain ⟨ε, hε, hbandε⟩ := hband (a / 2) (by positivity)
  have hbad := binomial_relative_deviation_tendsto_zero Tseq etaseq heta hmean hε
  have hsmall : ∀ᶠ j in atTop,
      binomialAverage (Tseq j) (etaseq j)
        (fun r => if ε * mean (Tseq j) (etaseq j) ≤
          |(r : ℝ) - mean (Tseq j) (etaseq j)| then 1 else 0) < a / 2 := by
    have := (Metric.tendsto_nhds.mp hbad) (a / 2) (by positivity)
    filter_upwards [this] with j hj
    have hnn : 0 ≤ binomialAverage (Tseq j) (etaseq j)
        (fun r => if ε * mean (Tseq j) (etaseq j) ≤
          |(r : ℝ) - mean (Tseq j) (etaseq j)| then 1 else 0) := by
      apply binomialAverage_nonneg (Tseq j) (etaseq j) _ (heta j)
      intro r _
      split_ifs <;> norm_num
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnn] using hj
  filter_upwards [hbandε, hsmall] with j hjband hjbad
  let w : ℕ → ℝ := Causalean.Mathlib.Probability.binomialWeight (Tseq j) (etaseq j)
  let b : ℕ → ℝ := fun r => if ε * mean (Tseq j) (etaseq j) ≤
    |(r : ℝ) - mean (Tseq j) (etaseq j)| then 1 else 0
  have hw (r : ℕ) : 0 ≤ w r := by
    dsimp [w, Causalean.Mathlib.Probability.binomialWeight]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (heta j).1 _))
      (pow_nonneg (sub_nonneg.mpr (heta j).2) _)
  have hp (r : ℕ) (hr : r ≤ Tseq j) : |f j r - c| ≤ a / 2 + b r := by
    dsimp [b]
    split_ifs with hb
    · have hf := hbound j r hr
      have : |f j r - c| ≤ 1 := abs_le.mpr ⟨by linarith [hf.1, hc.2],
        by linarith [hf.2, hc.1]⟩
      linarith [le_of_lt ha]
    · simpa using hjband r hr (lt_of_not_ge hb)
  have hdiff : binomialAverage (Tseq j) (etaseq j) (f j) - c =
      ∑ r ∈ Finset.range (Tseq j + 1), w r * (f j r - c) := by
    calc
      _ = binomialAverage (Tseq j) (etaseq j) (f j) -
          c * binomialAverage (Tseq j) (etaseq j) (fun _ => 1) := by
        rw [binomialAverage_one]; ring
      _ = ∑ r ∈ Finset.range (Tseq j + 1), w r * (f j r - c) := by
        simp only [binomialAverage, mul_one]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro r _
        dsimp [w]
        ring
  have hboundavg : |binomialAverage (Tseq j) (etaseq j) (f j) - c| ≤
      a / 2 + binomialAverage (Tseq j) (etaseq j) b := by
    rw [hdiff]
    calc
      |∑ r ∈ Finset.range (Tseq j + 1), w r * (f j r - c)| ≤
          ∑ r ∈ Finset.range (Tseq j + 1), |w r * (f j r - c)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.range (Tseq j + 1), w r * (a / 2 + b r) := by
        apply Finset.sum_le_sum
        intro r hr
        rw [abs_mul, abs_of_nonneg (hw r)]
        exact mul_le_mul_of_nonneg_left (hp r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))) (hw r)
      _ = a / 2 + binomialAverage (Tseq j) (etaseq j) b := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
        have hunit : (∑ r ∈ Finset.range (Tseq j + 1), w r) = 1 := by
          simpa [binomialAverage, w] using binomialAverage_one (Tseq j) (etaseq j)
        rw [hunit]
        change 1 * (a / 2) + binomialAverage (Tseq j) (etaseq j) b = _
        ring
  change dist (binomialAverage (Tseq j) (etaseq j) (f j)) c < a
  rw [Real.dist_eq]
  change binomialAverage (Tseq j) (etaseq j) b < a / 2 at hjbad
  linarith

end Causalean.Mathlib.Probability.Birthday
