/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Basic
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.ArmScoreSubstrate
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.Balanced
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.ExtremalProduct
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.NeymanAlgebra
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.Rayleigh
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.ScoreProgram
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.ScoreProgramDefs
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.SequentialRisk
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.SequentialRiskUniform
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.Tilt
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.TiltBand
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.TiltConstruction
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.TiltConstructionHelpers
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.TiltScore
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.VanTrees
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.TGlobalLogRate
public import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.TInstanceLocalMinimax

/-! # Run barrel (auto-generated)

Aggregates every module of this CausalSmith run so the whole run is one buildable target.
Research modules are not reachable from the top-level `CausalSmith.lean` barrel, so the
default Lake target does not check them.
-/
