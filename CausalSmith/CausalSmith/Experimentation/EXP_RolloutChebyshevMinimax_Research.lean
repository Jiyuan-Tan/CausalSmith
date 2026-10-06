/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Basic
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Amplification
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ChebyshevEndpoint
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ChebyshevExtremal
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ChebyshevSchedule
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.EhlichZeller
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.EqualSpacing
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.EqualSpacingArithmetic
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ExactRisk
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.MinimaxAssembly
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.MinimaxUpper
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.NoExtrapolation
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Schedule
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ScheduleGrid
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Variance
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.T_chebyshev_minimax
public import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.T_tv_envelope_design

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/
