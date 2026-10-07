module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Weighted geometric bound for ordered Gaussian tails

This analytic lemma supplies a uniform bound on finite dyadic sums whose
decay rate is determined by a positive real exponent.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Probability.SubGaussian

/-- For [a decay exponent](hyp:α) satisfying [strict positivity](hyp:hα), [one
positive constant bounds, for every length `J`, the partial sum over `j < J` of
`(j+1)·r^j` with ratio `r = exp(-α·log 2/2) = 2^(-α/2)`](goal).

Proof strategy: set `r = exp (-α * log 2 / 2)`, so `0 < r < 1`.
Use Mathlib's summability of `n * r^n` and of `r^n`, then bound each
nonnegative partial sum by the corresponding `tsum`.  The weight `j+1`
also controls the square-root logarithm arising from a dyadic block. -/
theorem weighted_dyadic_geometric_bound (α : ℝ) (hα : 0 < α) :
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ J : ℕ,
        (∑ j ∈ Finset.range J,
          ((j : ℝ) + 1) *
            (Real.exp (-(α * Real.log 2 / 2))) ^ j) ≤ Cα := by
  let r : ℝ := Real.exp (-(α * Real.log 2 / 2))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpos : 0 < α * Real.log 2 / 2 := by positivity
    linarith
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hsum : Summable (fun j : ℕ => ((j : ℝ) + 1) * r ^ j) := by
    have hweighted : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
      simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm)
    have hplain : Summable (fun j : ℕ => r ^ j) :=
      summable_geometric_of_lt_one hr0 hr1
    convert hweighted.add hplain using 1
    ext j
    ring
  have hnonneg (j : ℕ) : 0 ≤ ((j : ℝ) + 1) * r ^ j := by positivity
  refine ⟨1 + ∑' j : ℕ, ((j : ℝ) + 1) * r ^ j, ?_, ?_⟩
  · have htsum : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 1) * r ^ j :=
      tsum_nonneg hnonneg
    linarith
  · intro J
    change (∑ j ∈ Finset.range J, ((j : ℝ) + 1) * r ^ j) ≤
      1 + ∑' j : ℕ, ((j : ℝ) + 1) * r ^ j
    have hle := hsum.sum_le_tsum (Finset.range J) (fun j _ => hnonneg j)
    linarith

end Causalean.Mathlib.Probability.SubGaussian
