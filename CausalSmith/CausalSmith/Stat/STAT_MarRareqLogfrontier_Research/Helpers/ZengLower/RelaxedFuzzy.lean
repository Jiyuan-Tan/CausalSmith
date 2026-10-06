module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.Concentration
public import Causalean.Stat.Minimax.FuzzyHypotheses

/-! Fuzzy testing lower bounds for conditioned iid relaxed rare-cell priors. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
open Causalean.Stat.Minimax.FuzzyHypotheses
open Causalean.Stat.Minimax.MomentMatchedMixture

/-- For [the specified inputs and assumptions](hyp:d,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def iidRareTargetSum {d : ℕ} (z : Fin d → MarkedParam) : ℝ :=
  ∑ x, targetFunctional (z x)

private theorem measurable_iidRareTargetSum {d : ℕ} :
    Measurable (iidRareTargetSum : (Fin d → MarkedParam) → ℝ) := by
  unfold iidRareTargetSum targetFunctional
  fun_prop

end CausalSmith.Stat.MarRareqLogfrontier
