/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.ArmDisintegration
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.ArmDisintegrationTV
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.Bandwidth
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.Bracket
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.BumpHolder
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.BumpHolderAux
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CateWitness
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CausalLowerBound
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CausalNullLaw
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DivergenceLocalized
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DivergenceProduct
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DpContraction
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DpContractionAux
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.EqualSmoothnessAlgebra
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.HolderInterpolation
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.MinimaxReduction
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationBias
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationDesign
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationGram
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateMechanism
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateRisk
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateRiskBound
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateUpperBound
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateUpperEndpoint
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateWitness
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RandomizedLeCam
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RateAlgebra
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RegressionCalibrationBounds
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RegressionEmbedding
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TVSharp
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TwoPointDivergence
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TwoPointDivergenceAux
public import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.T_CausalDpTwoPointBarrier

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith research run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/
