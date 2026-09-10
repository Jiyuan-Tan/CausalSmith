import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.Reduction

/-!
# Large-alphabet two-unknown-distribution minimax lower bound

This module combines the explicit moment-matched fuzzy construction with the
all-estimator reduction.  It exports the requested real minimax lower bound
with universal numerical constants and the exact intensity-convention bridge.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

/-- For alphabets of size at least eight, sample size at least a constant
multiple of `d/log(e d)`, and comparable logarithms, the minimax squared risk
for estimating the `L₁` distance between two unknown distributions from
independent Poisson counts of means `2npᵢ,2nqᵢ` is at least a universal positive
multiple of `min(1,d/(n log(e n)))`. -/
theorem poissonizedTwoUnknownL1_minimax_lower (n d : ℕ)
    (hd : 8 ≤ d)
    (hn : (d : ℝ) /
      (100 * Real.log (Real.exp 1 * (d : ℝ))) ≤ (n : ℝ))
    (hlog : Real.log (Real.exp 1 * (n : ℝ)) ≤
      4 * Real.log (Real.exp 1 * (d : ℝ))) :
    (1 / 100000000 : ℝ) * largeAlphabetL1Rate n d ≤
      poissonizedTwoUnknownL1MinimaxRisk n d := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (poissonizedTwoUnknownL1MinimaxRiskENNReal_ne_top n d)).mp
  apply le_iInf
  intro est
  obtain ⟨p, q, hpq⟩ :=
    poissonizedTwoUnknownL1_allEstimator_lower n d hd hn hlog est
  exact hpq.trans (le_iSup (fun θ : TwoUnknownParameter d =>
    poissonizedTwoSampleL1Risk n θ.1 θ.2 est) (p, q))

/-- The displayed universal lower-bound constant is strictly positive. -/
theorem poissonizedTwoUnknownL1_lower_constant_pos :
    (0 : ℝ) < 1 / 100000000 := by
  norm_num

/-- The same minimax theorem under the convention `Pois(m pᵢ), Pois(m qᵢ)` is
obtained by setting `m=2n`; there is no statistical loss in the change of
notation. -/
theorem poissonizedTwoUnknownL1_minimax_lower_at_two_mul (n d : ℕ)
    (hd : 8 ≤ d)
    (hn : (d : ℝ) /
      (100 * Real.log (Real.exp 1 * (d : ℝ))) ≤ (n : ℝ))
    (hlog : Real.log (Real.exp 1 * (n : ℝ)) ≤
      4 * Real.log (Real.exp 1 * (d : ℝ))) :
    (1 / 100000000 : ℝ) * largeAlphabetL1Rate n d ≤
      poissonizedTwoUnknownL1MinimaxRiskAt (2 * (n : ℝ≥0)) d := by
  rw [← poissonizedTwoUnknownL1MinimaxRisk_eq_at_two_mul]
  exact poissonizedTwoUnknownL1_minimax_lower n d hd hn hlog

end CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower
