module
public import Causalean.Stat.UStatistic.LocalizedVariance.SumBound

/-!
# Localized variance of an unordered order-two U-statistic

For a symmetric kernel bounded by a symmetric weight, the centered second moment of
the unordered pair average is controlled by both the squared row mass at order `1/n`
and the pair mass at order `1/n²`. The extended nonnegative form is in `Bridge`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.UStatistic.LocalizedVariance

variable {X : Type*} [MeasurableSpace X]
  (P : Measure X) [IsProbabilityMeasure P]
  {H W : X → X → ℝ} {M : ℝ} (h : LocalizedKernel H W M)

-- Preserve the genuine localized-kernel premise while the proof is scaffolded.
include h

/-- A [probability law and localized-kernel certificate](hyp:P,h) give [an unordered
order-two U-statistic with finite second moment](goal). -/
theorem uStatistic_memLp_two {n : ℕ} :
    MemLp (uStatistic n H) 2 (iidLaw P n) := by
  have hsum : MemLp (∑ p ∈ pairIndices n, pairValue H p) 2 (iidLaw P n) :=
    memLp_finsetSum' (pairIndices n) (fun p _ => pairValue_memLp_two P h p)
  convert hsum.const_mul (((pairIndices n).card : ℝ)⁻¹) using 1
  funext ω
  simp only [uStatistic, pairValue, Finset.sum_apply]

/-- Under [a probability law and a kernel H localized by a weight W with envelope M](hyp:P,h)
— both symmetric and measurable, W between zero and one, and |H| at most M·W — with [at least
two observations](hyp:hn), [the variance of the unordered order-two U-statistic of H under n
independent draws (its expected squared deviation from its mean) is at most
16·M²·(R/n + Q/n²)](goal). Here Q, the pair mass, is the mean of W over two independent draws,
and R, the squared row mass, is the mean over one draw of the square of W's mean over a second
independent draw. -/
theorem centered_second_moment_le {n : ℕ} (hn : 2 ≤ n) :
    (∫ ω, (uStatistic n H ω - ∫ z, uStatistic n H z ∂iidLaw P n) ^ 2
      ∂iidLaw P n) ≤
      16 * M ^ 2 *
        (rowMassSq P W / (n : ℝ) + pairMass P W / (n : ℝ) ^ 2) := by
  have hp : 0 ≤ pairMass P W := by
    unfold pairMass
    apply integral_nonneg
    intro x
    apply integral_nonneg
    intro y
    exact h.weight_nonneg x y
  have hr : 0 ≤ rowMassSq P W := by
    unfold rowMassSq
    apply integral_nonneg
    intro x
    exact sq_nonneg _
  have hscale :
      variance (uStatistic n H) (iidLaw P n) =
        (((pairIndices n).card : ℝ)⁻¹) ^ 2 *
          variance (fun ω => ∑ p ∈ pairIndices n, pairValue H p ω) (iidLaw P n) := by
    have hfun : uStatistic n H =
        fun ω => (((pairIndices n).card : ℝ)⁻¹) *
          ∑ p ∈ pairIndices n, pairValue H p ω := by
      funext ω
      simp only [uStatistic, pairValue]
    rw [hfun]
    exact variance_const_mul (((pairIndices n).card : ℝ)⁻¹)
      (fun ω => ∑ p ∈ pairIndices n, pairValue H p ω) (iidLaw P n)
  calc
    _ = variance (uStatistic n H) (iidLaw P n) :=
      (variance_eq_integral (uStatistic_memLp_two P h).aemeasurable).symm
    _ = (((pairIndices n).card : ℝ)⁻¹) ^ 2 *
          variance (fun ω => ∑ p ∈ pairIndices n, pairValue H p ω) (iidLaw P n) :=
      hscale
    _ ≤ (((pairIndices n).card : ℝ)⁻¹) ^ 2 *
          ((n.choose 2 : ℝ) * (M ^ 2 * pairMass P W) +
            ((2 * (n.choose 2) * (n - 2) : ℕ) : ℝ) *
              (2 * M ^ 2 * rowMassSq P W)) :=
      mul_le_mul_of_nonneg_left (pair_sum_variance_le_localized_counts P h hn)
        (sq_nonneg _)
    _ ≤ 16 * M ^ 2 *
          (rowMassSq P W / (n : ℝ) + pairMass P W / (n : ℝ) ^ 2) := by
      rw [card_pairIndices]
      exact normalized_pair_counts_le hn (sq_nonneg M) hp hr

end Causalean.Stat.UStatistic.LocalizedVariance
