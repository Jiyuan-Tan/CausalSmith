module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.TUniformFrontier

/-!
# True-side Gaussian measurement-error endpoint frontier

Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- The uniform precision question is resolved by the same root, public minimization, and observable procedures. Given [the displayed inputs and assumptions](hyp:β,hβ), [the stated mathematical conclusion holds](goal). -/
-- @node: thm:uniform-frontier-resolution
theorem uniform_frontier_resolution (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    UniformFrontierConclusion β := by
  exact uniform_frontier β hβ

end CausalSmith.Stat.RdTruesideNoiseFrontier
