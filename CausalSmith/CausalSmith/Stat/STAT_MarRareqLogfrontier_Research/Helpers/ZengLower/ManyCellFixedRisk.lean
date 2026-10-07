module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.CountEstimatorBridge
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.ManyCellComposition
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.MinimaxConversion
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedBayesRiskConversion
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedExactTransfer
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.TransferErrorCalibration

/-! Bayes and worst-case composition for the many-cell lower bound. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
open Causalean.Stat
open Causalean.Stat.Minimax.FuzzyHypotheses
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

end CausalSmith.Stat.MarRareqLogfrontier
