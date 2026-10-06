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
Bernoulli divergences](goal) for a [strictly interior propensity](hyp:he0,he1)
and [strictly interior outcome means](hyp:hq₀0,hq₀1,hq₁0,hq₁1,hq₀'0,hq₀'1,hq₁'0,hq₁'1).

Split both finite sums on `Bool`. Cancel the common positive propensity
factor in the log quotient using `Real.log_mul` or `Real.log_div`, then unfold
`bernoulliKL`, `cellMass`, and `bitMass` and normalize by ring.
-/
theorem sum_cellMass_mul_log_ratio_eq_weighted_bernoulliKL
    {e q₀ q₁ q₀' q₁' : ℝ}
    (he0 : 0 < e) (he1 : e < 1)
    (hq₀0 : 0 < q₀) (hq₀1 : q₀ < 1)
    (hq₁0 : 0 < q₁) (hq₁1 : q₁ < 1)
    (hq₀'0 : 0 < q₀') (hq₀'1 : q₀' < 1)
    (hq₁'0 : 0 < q₁') (hq₁'1 : q₁' < 1) :
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
