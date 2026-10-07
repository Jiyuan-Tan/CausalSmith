module
public import Causalean.Mathlib.Probability.Birthday.Concentration

/-!
# The binomial pair scale is asymptotically half the squared mean

For T trials with success probability η, the expected number of unordered pairs of successes is
C(T, 2)·η², and the mean number of successes is T·η. Along any sequence of trial counts and
probabilities in [0, 1] whose mean T·η tends to infinity, the ratio of C(T, 2)·η² to (T·η)²/2
tends to one, so the two normalizations of the birthday-collision scale are interchangeable in the
limit.

## Main results

* `pairScale_div_half_mean_sq_tendsto_one` — the ratio of the pair scale to half the squared mean
  converges to one when the mean diverges.
-/

public section

namespace Causalean.Mathlib.Probability.Birthday

open Filter

/-- For [valid success probabilities](hyp:heta) and a [diverging expected
count](hyp:hmean), the [pair scale divided by half the squared mean](goal)
converges to one. -/
theorem pairScale_div_half_mean_sq_tendsto_one
    (Tseq : ℕ → ℕ) (etaseq : ℕ → ℝ)
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop) :
    Tendsto (fun j => pairScale (Tseq j) (etaseq j) /
      (mean (Tseq j) (etaseq j) ^ 2 / 2)) atTop (nhds 1) := by
  have hpos : ∀ᶠ j : ℕ in atTop, 0 < mean (Tseq j) (etaseq j) :=
    hmean.eventually_gt_atTop 0
  have hinv : Tendsto (fun j => (mean (Tseq j) (etaseq j))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hmean
  have hratio : Tendsto (fun j => etaseq j / mean (Tseq j) (etaseq j))
      atTop (nhds 0) := by
    apply squeeze_zero' _ _ hinv
    · filter_upwards [hpos] with j hj
      exact div_nonneg (heta j).1 (le_of_lt hj)
    · filter_upwards [hpos] with j hj
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right (heta j).2 (inv_nonneg.mpr (le_of_lt hj))
  have hlim : Tendsto (fun j => 1 - etaseq j / mean (Tseq j) (etaseq j))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hratio
  apply hlim.congr'
  filter_upwards [hpos] with j hj
  have hmu : mean (Tseq j) (etaseq j) ≠ 0 := ne_of_gt hj
  have hident : 2 * pairScale (Tseq j) (etaseq j) =
      mean (Tseq j) (etaseq j) *
        (mean (Tseq j) (etaseq j) - etaseq j) := by
    simp only [pairScale, mean, Nat.cast_choose_two]
    ring
  field_simp [hmu]
  nlinarith [hident]

end Causalean.Mathlib.Probability.Birthday
