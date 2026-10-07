module
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.Parameters
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL.Bernoulli

/-!
# Algebra of four selected Bernoulli cells

For a common treatment propensity, the propensity factor cancels from each
cell likelihood ratio, leaving the two weighted Bernoulli divergences.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL

open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

/-- [The sum of four selected-cell KL contributions equals the two weighted
Bernoulli divergences](goal) for a [strictly interior propensity](hyp:he0,he1).

The four outcome probabilities are unrestricted: when one of them is zero or one (or lies
outside the unit interval), both sides are evaluated with the conventions that the logarithm of
zero and a quotient by zero are zero, and the identity is a statement about Kullback–Leibler
divergences only for outcome probabilities strictly between zero and one.

Split both finite sums on `Bool`. Cancel the common positive propensity
factor in the log quotient using `Real.log_mul` or `Real.log_div`, then unfold
`bernoulliKL`, `cellMass`, and `bitMass` and normalize by ring.
-/
theorem sum_cellMass_mul_log_ratio_eq_weighted_bernoulliKL
    {e q₀ q₁ q₀' q₁' : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    (∑ a : Bool, ∑ y : Bool,
      cellMass e q₀ q₁ a y *
        Real.log (cellMass e q₀ q₁ a y / cellMass e q₀' q₁' a y)) =
      (1 - e) * bernoulliKL q₀ q₀' + e * bernoulliKL q₁ q₁' := by
  have he' : 1 - e ≠ 0 := ne_of_gt (by linarith : 0 < 1 - e)
  have he : e ≠ 0 := ne_of_gt he0
  simp only [Fintype.sum_bool]
  dsimp [cellMass, bitMass]
  simp only [mul_div_mul_left _ _ he, mul_div_mul_left _ _ he']
  unfold bernoulliKL
  ring

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL
