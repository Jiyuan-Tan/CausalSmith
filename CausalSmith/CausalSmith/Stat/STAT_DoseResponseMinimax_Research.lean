/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Basic
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Frontier
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Divergence
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.FrontierBracket
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.RateAlgebra
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.TwoPointConstruction
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.UpperBoundCited
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Base
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.BumpHolder
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Channel
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Core
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.HolderAux
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.KL
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Measure
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Membership
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.PiCond
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Regression
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Theta
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_CertifiedPartialBetaFrontier
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_FrontierBracketDeficient
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_OracleRegimeReduction
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_SharpMinimaxSmoothCovariate
public import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_SharpPointwiseLowerBound

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/
