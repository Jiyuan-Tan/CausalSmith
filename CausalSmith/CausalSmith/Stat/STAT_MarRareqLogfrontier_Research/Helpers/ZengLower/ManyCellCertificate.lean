module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.ConditionalSupport
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.ConditionedTVCalibration
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.ManyCellFixedRisk
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! The moment-certificate specialization of the many-cell fixed-risk bound. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
open Causalean.Stat
open Causalean.Stat.Minimax.FuzzyHypotheses

end CausalSmith.Stat.MarRareqLogfrontier
