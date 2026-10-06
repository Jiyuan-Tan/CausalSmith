module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedPrefixReconstruction

/-! Nested-risk form of the relaxed split-count Rao--Blackwell bridge. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat

end CausalSmith.Stat.MarRareqLogfrontier
