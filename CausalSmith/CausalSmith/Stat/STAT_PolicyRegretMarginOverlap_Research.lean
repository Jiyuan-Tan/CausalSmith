/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.BochnerIntegrability
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.ClipBias
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.CrossfitProcess
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.DriftBound
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.FeasibleERM
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.MasterBound
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.OffsetControl
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.SelfBound
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.T_feasible_tight
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.T_feasible_upper
public import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.T_minimax_lower

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/
